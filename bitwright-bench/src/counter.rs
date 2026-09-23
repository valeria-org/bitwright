//! What a benchmark sample measures: user-space instructions retired (hardware counters, Linux),
//! the thread's CPU time, and wall time.
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
        #[cfg(not(target_os = "linux"))]
        {
            Counters {
                unavailable: Some("instruction counters are only read on Linux".into()),
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
        Start {
            cpu: thread_cpu_ns(),
            wall: Instant::now(),
        }
    }

    /// Stops the counters; returns what ran since [`Counters::start`].
    pub fn stop(&mut self, start: Start) -> Reading {
        #[cfg(target_os = "linux")]
        linux::disable(&self.fds);
        let cpu = thread_cpu_ns().saturating_sub(start.cpu);
        let wall = u64::try_from(start.wall.elapsed().as_nanos()).unwrap_or(u64::MAX);
        #[cfg(target_os = "linux")]
        let instructions = (!self.fds.is_empty())
            .then(|| linux::read_sum(&self.fds))
            .flatten();
        #[cfg(not(target_os = "linux"))]
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
    }

    /// Resumes paused counters without resetting them.
    pub fn resume(&mut self) {
        #[cfg(target_os = "linux")]
        linux::enable(&self.fds);
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
