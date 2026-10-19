//! PROTOTYPE (solver-budget investigation): with `BW_CALLS=FILE`, every MBA solver call of a
//! bitwright tool is appended to FILE (dataset, line, call, the question's nodes and variables,
//! step limit, steps spent, answer, memo hit, user-space instructions, wall and thread CPU
//! nanoseconds, pass work left and the run's pass-work limit), in the format of
//! `bitwright-bench --solver-calls`.

#![allow(unsafe_code)]

use std::cell::RefCell;
use std::io::Write as _;
use std::sync::OnceLock;

use bitwright::mba::probe::{self, Call};

thread_local! {
    static DATASET: RefCell<String> = const { RefCell::new(String::new()) };
}

/// Names the dataset the next calls belong to; installs the clocks on first use.
pub fn dataset(name: &str) {
    DATASET.with(|d| *d.borrow_mut() = name.replace('\t', " "));
    static INIT: OnceLock<()> = OnceLock::new();
    INIT.get_or_init(|| {
        let f = free_running();
        let _ = CLOCK.set(f);
        if let Some(f) = f {
            probe::set_clock(f);
        }
        probe::set_cpu_clock(thread_cpu_ns);
    });
}

/// The instruction and CPU clocks now.
pub fn now() -> (u64, u64) {
    let i = CLOCK.get().copied().flatten().map_or(0, |f| f());
    (i, thread_cpu_ns())
}

static CLOCK: OnceLock<Option<fn() -> u64>> = OnceLock::new();

/// Appends a case's calls, and its engine run's instructions and CPU time since `start`.
pub fn record(line: usize, calls: &[Call], start: (u64, u64)) {
    let (i1, c1) = now();
    let Some(path) = std::env::var_os("BW_CALLS") else {
        return;
    };
    let Ok(f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    else {
        return;
    };
    let mut f = std::io::BufWriter::new(f);
    DATASET.with(|d| {
        let d = d.borrow();
        let _ = writeln!(
            f,
            "R\t{d}\t{line}\tinstr={}\tcpu={}\tcalls={}",
            i1.saturating_sub(start.0),
            c1.saturating_sub(start.1),
            calls.len()
        );
        for (j, c) in calls.iter().enumerate() {
            let _ = writeln!(
                f,
                "C\t{d}\t{line}\t{j}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                c.nodes,
                c.vars,
                c.limit,
                c.steps,
                c.answer,
                u8::from(c.memo),
                c.instr,
                c.nanos,
                c.cpu_nanos,
                c.left,
                c.cap
            );
        }
    });
}

fn thread_cpu_ns() -> u64 {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: `ts` is a valid, writable timespec for the duration of the call.
    let rc = unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut ts) };
    if rc != 0 {
        return 0;
    }
    (ts.tv_sec as u64)
        .saturating_mul(1_000_000_000)
        .saturating_add(ts.tv_nsec as u64)
}

/// A free-running user-space instruction counter of the calling thread (one per PMU of a
/// hybrid CPU, summed), as `bitwright-bench`'s counter reads it.
fn free_running() -> Option<fn() -> u64> {
    static FDS: OnceLock<Vec<i32>> = OnceLock::new();
    let fds = FDS.get_or_init(|| {
        let fds = open_instructions().unwrap_or_default();
        for &fd in &fds {
            // SAFETY: `fd` is an open perf event descriptor; these requests take no argument.
            unsafe {
                libc::ioctl(fd, 0x2403 as _, 0);
                libc::ioctl(fd, 0x2400 as _, 0);
            }
        }
        fds
    });
    if fds.is_empty() {
        return None;
    }
    fn read() -> u64 {
        let Some(fds) = FDS.get() else { return 0 };
        let mut total = 0u64;
        for &fd in fds {
            let mut value = 0u64;
            // SAFETY: reads exactly 8 bytes into `value` (read_format 0: one u64 count).
            let n = unsafe { libc::read(fd, (&mut value as *mut u64).cast(), 8) };
            if n != 8 {
                return 0;
            }
            total = total.saturating_add(value);
        }
        total
    }
    Some(read)
}

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

fn open(config: u64) -> Option<i32> {
    let mut attr = Attr {
        type_: 0,
        size: std::mem::size_of::<Attr>() as u32,
        config,
        // disabled, exclude_kernel, exclude_hv
        flags: 1 | (1 << 5) | (1 << 6),
        ..Attr::default()
    };
    // SAFETY: `attr` is a valid perf_event_attr of the size it declares; pid 0 / cpu -1 counts
    // the calling thread on any CPU; no group, no flags.
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
    (fd >= 0).then_some(fd as i32)
}

fn open_instructions() -> Option<Vec<i32>> {
    let pmus: Vec<u32> = ["cpu_core", "cpu_atom"]
        .iter()
        .filter_map(|pmu| {
            std::fs::read_to_string(format!("/sys/bus/event_source/devices/{pmu}/type"))
                .ok()?
                .trim()
                .parse()
                .ok()
        })
        .collect();
    if pmus.is_empty() {
        return Some(vec![open(1)?]);
    }
    pmus.iter()
        .map(|&pmu| open((u64::from(pmu) << 32) | 1))
        .collect()
}
