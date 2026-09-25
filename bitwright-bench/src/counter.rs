//! What a benchmark sample measures: the thread's instructions retired (hardware counters:
//! user space on Linux, kernel mode too on macOS), its CPU time, and wall time.
//!
//! Instructions retired is the primary metric: it does not depend on other load, frequency
//! scaling or which core the thread runs on, so two runs on a busy machine agree to a fraction
//! of a percent. CPU time is the fallback where counters are unavailable (another OS, a
//! container without `perf_event_open`, `perf_event_paranoid` > 2); it excludes time the thread
//! waits for a core but not the slowdown of sharing caches with other load. Wall time is shown
//! for reference only.
//!
//! On a hybrid CPU (performance and efficiency cores are separate PMUs, `cpu_core` and
//! `cpu_atom`), one counter per PMU is opened and their counts are added: each counts only
//! while the thread runs on its kind of core.
//!
//! On macOS the kernel keeps each thread's instructions retired per kind of core (performance,
//! efficiency) and `proc_pidinfo(PROC_PIDTHREADCOUNTS)` reads them without privileges; the
//! kinds are added as on a hybrid Linux CPU. They include kernel mode, which no unprivileged
//! interface separates: the cost of a reading itself (a system call, about 5,000 instructions)
//! is measured when the counters open and subtracted, and what remains is the workload with the
//! page faults and interrupts it takes.

#![allow(unsafe_code)]

use std::time::Instant;

/// One reading of every clock.
#[derive(Clone, Copy, Debug, Default)]
pub struct Reading {
    /// User-space instructions retired, if counters are available.
    pub instructions: Option<u64>,
    /// Thread CPU time, nanoseconds.
    pub cpu_ns: u64,
    /// Wall time, nanoseconds.
    pub wall_ns: u64,
}

/// The counters of the current thread.
#[derive(Debug)]
pub struct Counters {
    #[cfg(target_os = "linux")]
    fds: Vec<i32>,
    #[cfg(target_os = "macos")]
    thread: macos::Thread,
    /// Why instructions are unavailable, if they are.
    pub unavailable: Option<String>,
}

impl Counters {
    /// Opens instruction counters for the calling thread (disabled until [`Counters::start`]).
    pub fn open() -> Counters {
        #[cfg(target_os = "linux")]
        {
            match linux::open_instructions() {
                Ok(fds) => Counters {
                    fds,
                    unavailable: None,
                },
                Err(why) => Counters {
                    fds: Vec::new(),
                    unavailable: Some(why),
                },
            }
        }
        #[cfg(target_os = "macos")]
        {
            let (thread, unavailable) = match macos::Thread::open() {
                Ok(t) => (t, None),
                Err(why) => (macos::Thread::default(), Some(why)),
            };
            Counters {
                thread,
                unavailable,
            }
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            Counters {
                unavailable: Some("instruction counters are only read on Linux and macOS".into()),
            }
        }
    }

    /// Whether instructions are counted.
    pub fn counts_instructions(&self) -> bool {
        self.unavailable.is_none()
    }

    /// Resets and starts every clock.
    pub fn start(&mut self) -> Start {
        #[cfg(target_os = "linux")]
        linux::reset_enable(&self.fds);
        #[cfg(target_os = "macos")]
        self.thread.reset_enable();
        Start {
            cpu: thread_cpu_ns(),
            wall: Instant::now(),
        }
    }

    /// Stops the counters; returns what ran since [`Counters::start`].
    pub fn stop(&mut self, start: Start) -> Reading {
        #[cfg(target_os = "linux")]
        linux::disable(&self.fds);
        #[cfg(target_os = "macos")]
        self.thread.disable();
        let cpu = thread_cpu_ns().saturating_sub(start.cpu);
        let wall = u64::try_from(start.wall.elapsed().as_nanos()).unwrap_or(u64::MAX);
        #[cfg(target_os = "linux")]
        let instructions = (!self.fds.is_empty())
            .then(|| linux::read_sum(&self.fds))
            .flatten();
        #[cfg(target_os = "macos")]
        let instructions = self.unavailable.is_none().then_some(self.thread.counted);
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let instructions = None;
        Reading {
            instructions,
            cpu_ns: cpu,
            wall_ns: wall,
        }
    }

    /// The CPU and wall clocks now (for timing part of a sample).
    pub fn clocks(&self) -> Start {
        Start {
            cpu: thread_cpu_ns(),
            wall: Instant::now(),
        }
    }

    /// CPU and wall nanoseconds since `start`.
    pub fn since(&self, start: Start) -> (u64, u64) {
        (
            thread_cpu_ns().saturating_sub(start.cpu),
            u64::try_from(start.wall.elapsed().as_nanos()).unwrap_or(u64::MAX),
        )
    }

    /// Pauses the counters (for per-iteration setup inside a sample).
    pub fn pause(&mut self) {
        #[cfg(target_os = "linux")]
        linux::disable(&self.fds);
        #[cfg(target_os = "macos")]
        self.thread.disable();
    }

    /// Resumes paused counters without resetting them.
    pub fn resume(&mut self) {
        #[cfg(target_os = "linux")]
        linux::enable(&self.fds);
        #[cfg(target_os = "macos")]
        self.thread.enable();
    }
}

impl Drop for Counters {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        for &fd in &self.fds {
            // SAFETY: `fd` was returned by `perf_event_open` and is closed once, here.
            unsafe {
                libc::close(fd);
            }
        }
    }
}

/// The clocks at [`Counters::start`].
#[derive(Clone, Copy, Debug)]
pub struct Start {
    cpu: u64,
    wall: Instant,
}

/// CPU time consumed by the calling thread, nanoseconds (wall time where unavailable).
fn thread_cpu_ns() -> u64 {
    #[cfg(unix)]
    {
        let mut ts = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        // SAFETY: `ts` is a valid, writable timespec for the duration of the call.
        let rc = unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut ts) };
        if rc == 0 {
            return (ts.tv_sec as u64)
                .saturating_mul(1_000_000_000)
                .saturating_add(ts.tv_nsec as u64);
        }
    }
    use std::sync::OnceLock;
    static ORIGIN: OnceLock<Instant> = OnceLock::new();
    let origin = *ORIGIN.get_or_init(Instant::now);
    u64::try_from(origin.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

#[cfg(target_os = "linux")]
mod linux {
    //! `perf_event_open(2)` for user-space instructions retired.

    const PERF_TYPE_HARDWARE: u32 = 0;
    const PERF_COUNT_HW_INSTRUCTIONS: u64 = 1;
    // `perf_event_attr` flag bits (in the `flags` word after `read_format`).
    const DISABLED: u64 = 1 << 0;
    const EXCLUDE_KERNEL: u64 = 1 << 5;
    const EXCLUDE_HV: u64 = 1 << 6;
    // ioctl requests: _IO('$', 0..3).
    const IOC_ENABLE: libc::c_ulong = 0x2400;
    const IOC_DISABLE: libc::c_ulong = 0x2401;
    const IOC_RESET: libc::c_ulong = 0x2403;

    /// `struct perf_event_attr`, through `sample_max_stack` (PERF_ATTR_SIZE_VER5, 112 bytes);
    /// the kernel accepts any published size.
    #[repr(C)]
    #[derive(Default)]
    struct Attr {
        type_: u32,
        size: u32,
        config: u64,
        sample_period: u64,
        sample_type: u64,
        read_format: u64,
        flags: u64,
        wakeup_events: u32,
        bp_type: u32,
        config1: u64,
        config2: u64,
        branch_sample_type: u64,
        sample_regs_user: u64,
        sample_stack_user: u32,
        clockid: i32,
        sample_regs_intr: u64,
        aux_watermark: u32,
        sample_max_stack: u16,
        reserved: u16,
    }

    /// The PMU types of a hybrid CPU's core kinds, or empty on a uniform CPU.
    fn hybrid_pmus() -> Vec<u32> {
        ["cpu_core", "cpu_atom"]
            .iter()
            .filter_map(|pmu| {
                std::fs::read_to_string(format!("/sys/bus/event_source/devices/{pmu}/type"))
                    .ok()?
                    .trim()
                    .parse()
                    .ok()
            })
            .collect()
    }

    fn open(config: u64) -> Result<i32, String> {
        let mut attr = Attr {
            type_: PERF_TYPE_HARDWARE,
            size: std::mem::size_of::<Attr>() as u32,
            config,
            flags: DISABLED | EXCLUDE_KERNEL | EXCLUDE_HV,
            ..Attr::default()
        };
        // SAFETY: `attr` is a valid perf_event_attr of the size it declares; pid 0 / cpu -1
        // counts the calling thread on any CPU; no group, no flags.
        let fd = unsafe {
            libc::syscall(
                libc::SYS_perf_event_open,
                &mut attr as *mut Attr,
                0 as libc::pid_t,
                -1 as libc::c_int,
                -1 as libc::c_int,
                0 as libc::c_ulong,
            )
        };
        if fd < 0 {
            return Err(format!(
                "perf_event_open failed: {} (see /proc/sys/kernel/perf_event_paranoid)",
                std::io::Error::last_os_error()
            ));
        }
        i32::try_from(fd).map_err(|_| "perf_event_open returned an invalid descriptor".into())
    }

    pub(super) fn open_instructions() -> Result<Vec<i32>, String> {
        let pmus = hybrid_pmus();
        if pmus.is_empty() {
            return Ok(vec![open(PERF_COUNT_HW_INSTRUCTIONS)?]);
        }
        // Extended hardware event type: the PMU in the upper 32 bits of `config`.
        pmus.iter()
            .map(|&pmu| open((u64::from(pmu) << 32) | PERF_COUNT_HW_INSTRUCTIONS))
            .collect()
    }

    fn ioctl_all(fds: &[i32], request: libc::c_ulong) {
        for &fd in fds {
            // SAFETY: `fd` is an open perf event descriptor; these requests take no argument.
            unsafe {
                libc::ioctl(fd, request as _, 0);
            }
        }
    }

    pub(super) fn reset_enable(fds: &[i32]) {
        ioctl_all(fds, IOC_RESET);
        ioctl_all(fds, IOC_ENABLE);
    }

    pub(super) fn enable(fds: &[i32]) {
        ioctl_all(fds, IOC_ENABLE);
    }

    pub(super) fn disable(fds: &[i32]) {
        ioctl_all(fds, IOC_DISABLE);
    }

    pub(super) fn read_sum(fds: &[i32]) -> Option<u64> {
        let mut total = 0u64;
        for &fd in fds {
            let mut value = 0u64;
            // SAFETY: reads exactly 8 bytes into `value` (read_format 0: one u64 count).
            let n = unsafe { libc::read(fd, (&mut value as *mut u64).cast(), 8) };
            if n != 8 {
                return None;
            }
            total = total.saturating_add(value);
        }
        Some(total)
    }
}

#[cfg(target_os = "macos")]
mod macos {
    //! `proc_pidinfo(PROC_PIDTHREADCOUNTS)` for the calling thread's instructions retired.

    /// The flavor, from XNU's `bsd/sys/proc_info_private.h` (used by `taskinfo`).
    const PROC_PIDTHREADCOUNTS: libc::c_int = 34;

    /// `struct proc_threadcounts_data`, one per kind of core, in `u64`s: instructions first.
    const DATA: usize = 5;

    /// The most kinds of core read (`hw.nperflevels` is 1 or 2 on current machines).
    const KINDS: usize = 8;

    /// A counter over the enabled intervals, less the cost of the readings that bound them.
    #[derive(Debug, Default)]
    pub(super) struct Thread {
        /// The thread's system-wide id (`pthread_threadid_np`).
        tid: u64,
        /// The kinds of core (`hw.nperflevels`).
        kinds: usize,
        /// Instructions counted since the last reset.
        pub(super) counted: u64,
        /// The reading at the last enable, while enabled.
        since: Option<u64>,
        /// What one reading costs, as the least of a few back-to-back pairs.
        reading: u64,
    }

    impl Thread {
        pub(super) fn open() -> Result<Thread, String> {
            let mut kinds = 0u32;
            let mut len = std::mem::size_of::<u32>();
            // SAFETY: `kinds` is a writable u32 and `len` its size, as the sysctl expects.
            let rc = unsafe {
                libc::sysctlbyname(
                    c"hw.nperflevels".as_ptr(),
                    (&mut kinds as *mut u32).cast(),
                    &mut len,
                    std::ptr::null_mut(),
                    0,
                )
            };
            let mut tid = 0u64;
            // SAFETY: thread 0 is the calling thread; `tid` is writable.
            let tc = unsafe { libc::pthread_threadid_np(0, &mut tid) };
            if rc != 0 || tc != 0 {
                return Err("no thread id or kinds of core".into());
            }
            let mut t = Thread {
                tid,
                kinds: (kinds as usize).clamp(1, KINDS),
                ..Thread::default()
            };
            t.reading = u64::MAX;
            for _ in 0..8 {
                let before = t
                    .instructions()
                    .ok_or("PROC_PIDTHREADCOUNTS reads nothing")?;
                let after = t
                    .instructions()
                    .ok_or("PROC_PIDTHREADCOUNTS reads nothing")?;
                t.reading = t.reading.min(after.saturating_sub(before));
            }
            Ok(t)
        }

        /// The instructions the thread has retired so far, on every kind of core (no allocation:
        /// a reading's cost is subtracted as measured).
        fn instructions(&self) -> Option<u64> {
            // The header (two u16 and a u32: the entries filled) and one entry per kind.
            let mut buf = [0u64; 1 + KINDS * DATA];
            let size = libc::c_int::try_from((1 + self.kinds * DATA) * 8).ok()?;
            // SAFETY: `buf` is writable for `size` bytes, which the flavor fills at most.
            let n = unsafe {
                libc::proc_pidinfo(
                    libc::getpid(),
                    PROC_PIDTHREADCOUNTS,
                    self.tid,
                    buf.as_mut_ptr().cast(),
                    size,
                )
            };
            let filled = ((buf[0] & 0xffff) as usize).min(self.kinds);
            let total: u64 = (0..filled).map(|i| buf[1 + i * DATA]).sum();
            (n > 0 && total > 0).then_some(total)
        }

        pub(super) fn reset_enable(&mut self) {
            self.counted = 0;
            self.enable();
        }

        pub(super) fn enable(&mut self) {
            self.since = self.instructions();
        }

        pub(super) fn disable(&mut self) {
            if let (Some(since), Some(now)) = (self.since.take(), self.instructions()) {
                let spent = now.saturating_sub(since).saturating_sub(self.reading);
                self.counted = self.counted.saturating_add(spent);
            }
        }
    }
}
