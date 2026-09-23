//! Benchmark definitions, the sample loop, and reports.

use std::fmt::Write as _;
use std::hint::black_box;

use crate::counter::{Counters, Reading};

/// A benchmark: a name, the number of iterations per sample, what one iteration is, and a body
/// that prepares its inputs (not measured) and then calls one of the [`Bencher`] loops.
pub struct Bench {
    pub name: String,
    pub iters: u64,
    /// What one iteration does, for the report ("call", "1024 ops", ...).
    pub unit: &'static str,
    body: Box<dyn Fn(&mut Bencher<'_>)>,
    /// What the work achieved and declined, computed once outside any measurement.
    note: Option<Box<dyn Fn() -> String>>,
}

impl std::fmt::Debug for Bench {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Bench")
            .field("name", &self.name)
            .field("iters", &self.iters)
            .finish_non_exhaustive()
    }
}

impl Bench {
    pub fn new(
        name: impl Into<String>,
        iters: u64,
        unit: &'static str,
        body: impl Fn(&mut Bencher<'_>) + 'static,
    ) -> Bench {
        Bench {
            name: name.into(),
            iters,
            unit,
            body: Box::new(body),
            note: None,
        }
    }

    /// Adds a note: what the benchmarked work achieves and declines (successes, refusals,
    /// sizes), reported next to its costs. Computed once, never measured.
    pub fn with_note(mut self, note: impl Fn() -> String + 'static) -> Bench {
        self.note = Some(Box::new(note));
        self
    }

    /// The note, if any.
    pub fn note(&self) -> Option<String> {
        self.note.as_ref().map(|f| f())
    }
}

/// Runs one sample of a benchmark's routine.
pub struct Bencher<'a> {
    counters: &'a mut Counters,
    iters: u64,
    reading: Option<Reading>,
}

impl std::fmt::Debug for Bencher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Bencher")
            .field("iters", &self.iters)
            .finish()
    }
}

impl Bencher<'_> {
    /// Measures `routine`, called once per iteration. Its results are dropped inside the
    /// measurement (they are usually small).
    pub fn iter<R>(&mut self, mut routine: impl FnMut() -> R) {
        let start = self.counters.start();
        for _ in 0..self.iters {
            black_box(routine());
        }
        self.reading = Some(self.counters.stop(start));
    }

    /// Measures `routine` over an input `setup` builds fresh for every iteration; neither the
    /// setup nor dropping the routine's result is measured.
    pub fn iter_batched<I, R>(
        &mut self,
        mut setup: impl FnMut() -> I,
        mut routine: impl FnMut(I) -> R,
    ) {
        let mut cpu = 0u64;
        let mut wall = 0u64;
        let start = self.counters.start();
        self.counters.pause();
        for _ in 0..self.iters {
            let input = black_box(setup());
            let t = self.counters.clocks();
            self.counters.resume();
            let out = routine(input);
            self.counters.pause();
            let (c, w) = self.counters.since(t);
            cpu += c;
            wall += w;
            drop(black_box(out));
        }
        let mut reading = self.counters.stop(start);
        reading.cpu_ns = cpu;
        reading.wall_ns = wall;
        self.reading = Some(reading);
    }
}

/// The per-iteration result of a benchmark over its samples.
#[derive(Clone, Debug)]
pub struct Summary {
    pub name: String,
    pub unit: String,
    pub iters: u64,
    pub samples: usize,
    /// Instructions per iteration: median, minimum, maximum over the samples.
    pub instructions: Option<(f64, f64, f64)>,
    /// CPU nanoseconds per iteration: minimum and median.
    pub cpu_ns: (f64, f64),
    /// Wall nanoseconds per iteration: median.
    pub wall_ns: f64,
}

impl Summary {
    /// The spread of instruction counts over the samples, relative to the median.
    pub fn instruction_spread(&self) -> Option<f64> {
        self.instructions.map(|(median, lo, hi)| {
            if median > 0.0 {
                (hi - lo) / median
            } else {
                0.0
            }
        })
    }
}

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    let n = v.len();
    if n == 0 {
        0.0
    } else if n % 2 == 1 {
        v[n / 2]
    } else {
        (v[n / 2 - 1] + v[n / 2]) / 2.0
    }
}

/// Runs `bench`: one warm-up sample, then `samples` measured ones.
pub fn run(bench: &Bench, counters: &mut Counters, samples: usize, scale: f64) -> Summary {
    let iters = ((bench.iters as f64 * scale).round() as u64).max(1);
    let sample = |counters: &mut Counters| {
        let mut b = Bencher {
            counters,
            iters,
            reading: None,
        };
        (bench.body)(&mut b);
        b.reading
            .unwrap_or_else(|| panic!("benchmark `{}` never called a Bencher loop", bench.name))
    };
    sample(counters);
    let readings: Vec<Reading> = (0..samples.max(1)).map(|_| sample(counters)).collect();
    let per = |x: u64| x as f64 / iters as f64;
    let instructions = readings
        .iter()
        .map(|r| r.instructions.map(per))
        .collect::<Option<Vec<f64>>>()
        .map(|mut v| {
            let m = median(&mut v);
            (m, v[0], v[v.len() - 1])
        });
    let mut cpu: Vec<f64> = readings.iter().map(|r| per(r.cpu_ns)).collect();
    let cpu_median = median(&mut cpu);
    let mut wall: Vec<f64> = readings.iter().map(|r| per(r.wall_ns)).collect();
    Summary {
        name: bench.name.clone(),
        unit: bench.unit.to_string(),
        iters,
        samples: readings.len(),
        instructions,
        cpu_ns: (cpu[0], cpu_median),
        wall_ns: median(&mut wall),
    }
}

/// A count with a metric suffix: 1234 -> "1.23k".
pub fn si(x: f64) -> String {
    let a = x.abs();
    if a >= 1e9 {
        format!("{:.2}G", x / 1e9)
    } else if a >= 1e6 {
        format!("{:.2}M", x / 1e6)
    } else if a >= 1e3 {
        format!("{:.2}k", x / 1e3)
    } else {
        format!("{x:.1}")
    }
}

/// Nanoseconds as a readable duration.
pub fn duration(ns: f64) -> String {
    if ns >= 1e9 {
        format!("{:.2} s", ns / 1e9)
    } else if ns >= 1e6 {
        format!("{:.2} ms", ns / 1e6)
    } else if ns >= 1e3 {
        format!("{:.2} us", ns / 1e3)
    } else {
        format!("{ns:.0} ns")
    }
}

/// The CSV header of saved results.
pub const CSV_HEADER: &str = "name,unit,iters,samples,instructions_median,instructions_min,instructions_max,cpu_ns_min,cpu_ns_median,wall_ns_median";

/// One saved result line.
pub fn csv_line(s: &Summary) -> String {
    let (im, ilo, ihi) = match s.instructions {
        Some((m, lo, hi)) => (format!("{m:.1}"), format!("{lo:.1}"), format!("{hi:.1}")),
        None => (String::new(), String::new(), String::new()),
    };
    let mut line = String::new();
    let _ = write!(
        line,
        "{},{},{},{},{im},{ilo},{ihi},{:.1},{:.1},{:.1}",
        s.name, s.unit, s.iters, s.samples, s.cpu_ns.0, s.cpu_ns.1, s.wall_ns
    );
    line
}

/// A saved result: name -> (instructions median and spread, CPU time minimum).
#[derive(Clone, Copy, Debug)]
pub struct Saved {
    pub instructions: Option<(f64, f64)>,
    pub cpu_ns_min: f64,
}

/// Parses a file written with `--save`.
pub fn parse_saved(text: &str) -> Result<Vec<(String, Saved)>, String> {
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') || line.starts_with("name,") {
            continue;
        }
        let f: Vec<&str> = line.split(',').collect();
        if f.len() != 10 {
            return Err(format!("line {}: expected 10 fields", n + 1));
        }
        let num = |s: &str| -> Result<f64, String> {
            s.parse()
                .map_err(|_| format!("line {}: bad number `{s}`", n + 1))
        };
        let instructions = if f[4].is_empty() {
            None
        } else {
            let (m, lo, hi) = (num(f[4])?, num(f[5])?, num(f[6])?);
            Some((m, if m > 0.0 { (hi - lo) / m } else { 0.0 }))
        };
        out.push((
            f[0].to_string(),
            Saved {
                instructions,
                cpu_ns_min: num(f[7])?,
            },
        ));
    }
    Ok(out)
}
