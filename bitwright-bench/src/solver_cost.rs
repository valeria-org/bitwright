//! PROTOTYPE, not for release: what the MBA solver's calls cost and how the engine's fuel bounds
//! them (`docs/proposals/solver-budget.md`).
//!
//! `--solver-calls FILE` (feature `probe`): every solver call the engine makes on the MBA rows'
//! corpora, `--corpus-diff`'s and the `--prover-budgets` question, at the default budget (and
//! the question also at fuel 2^14), one tab-separated line per call in FILE: its steps,
//! instructions and time, with the run's totals as `T` lines.
//!
//! `--solver-worst FILE` (feature `probe`): candidate questions for the longest single call
//! within the default limits, asked of the solver directly at its default budget.

#[cfg(feature = "probe")]
pub use probe::*;

#[cfg(feature = "probe")]
mod probe {
    use std::io::Write;
    use std::process::ExitCode;
    use std::time::Instant;

    use bitwright::Context;
    use bitwright::engine::Run;
    use bitwright::mba::probe::{self, Call};
    use bitwright::prove::Config;

    use crate::counter::Counters;
    use crate::symbolic_cost::{corpora, engine, setting, warm_up};

    fn line(out: &mut impl Write, corpus: &str, input: usize, calls: &[Call]) {
        for (j, c) in calls.iter().enumerate() {
            let _ = writeln!(
                out,
                "C\t{corpus}\t{input}\t{j}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
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
    }

    pub fn calls(path: &str) -> ExitCode {
        let Some(clock) = crate::counter::free_running() else {
            eprintln!("instruction counters are unavailable");
            return ExitCode::FAILURE;
        };
        probe::set_clock(clock);
        probe::set_cpu_clock(crate::counter::cpu_clock());
        let over = probe::overhead(10_000);
        let mut out =
            std::io::BufWriter::new(std::fs::File::create(path).expect("create the file"));
        let _ = writeln!(
            out,
            "# {}; span {:.0} instr {:.0} ns",
            setting(),
            over.instr as f64 / 1e4,
            over.nanos as f64 / 1e4
        );
        let mut counters = Counters::open();
        // The prover's MBA-heavy question (`--prover-budgets`): a first ask warms the
        // process-wide engine (its solver remembers answers), as there.
        let src = crate::prover_budgets::identities(48);
        let _ = probe::take_calls();
        let _ = crate::prover_budgets::ask(&src, bitwright::Width::W64, &Config::default());
        let calls = probe::take_calls();
        line(&mut out, "prover/first", 0, &calls);
        for (label, fuel) in [("default", 1u64 << 22), ("2^14", 1 << 14)] {
            let cfg = Config::default()
                .with_simplify_fuel(fuel)
                .with_max_conflicts(crate::prover_budgets::CONFLICTS);
            let _ = probe::take_calls();
            let t = Instant::now();
            let start = counters.start();
            let (answer, s) = crate::prover_budgets::ask(&src, bitwright::Width::W64, &cfg);
            let reading = counters.stop(start);
            let calls = probe::take_calls();
            line(&mut out, &format!("prover/{label}"), 0, &calls);
            let _ = writeln!(
                out,
                "T\tprover/{label}\t{answer}\tinstr={}\tpass={}\tms={:.1}",
                reading.instructions.unwrap_or(0),
                s.simplification.spent.pass_work,
                t.elapsed().as_secs_f64() * 1e3
            );
        }
        warm_up();
        let _ = probe::take_calls();
        for c in corpora() {
            let eng = engine();
            let (mut instr, mut pass, mut nanos, mut n) = (0u64, 0u64, 0u128, 0usize);
            for (i, build) in c.inputs.iter().enumerate() {
                let mut cx = Context::new();
                let roots = build(&mut cx);
                let t = Instant::now();
                let start = counters.start();
                let o = eng.run(&mut cx, &roots, Run::default()).expect("run");
                let reading = counters.stop(start);
                nanos += t.elapsed().as_nanos();
                instr += reading.instructions.unwrap_or(0);
                pass += o.stats.pass_work;
                let calls = probe::take_calls();
                n += calls.len();
                line(&mut out, c.name, i, &calls);
            }
            let _ = writeln!(
                out,
                "T\t{}\t{}\tinstr={instr}\tpass={pass}\tms={:.1}",
                c.name,
                c.inputs.len(),
                nanos as f64 / 1e6
            );
            let _ = out.flush();
            eprintln!(
                "{}: {} inputs, {n} calls, {:.2} G instr",
                c.name,
                c.inputs.len(),
                instr as f64 / 1e9
            );
        }
        ExitCode::SUCCESS
    }

    /// `--solver-dags SPEC FILE`: random DAGs of the shape `count,nodes,symbols,bits[,heavy]`
    /// (seeds as `--corpus-diff`'s) through the MBA rows' engine at the default budget, every
    /// solver call recorded in FILE as `--solver-calls` does (and dumped with `BW_DUMP_*`).
    pub fn dags(spec: &str, path: &str) -> ExitCode {
        use crate::workload::{self, Dag};
        let f: Vec<&str> = spec.split(',').collect();
        let num = |i: usize| f.get(i).and_then(|x| x.parse::<u64>().ok());
        let (Some(count), Some(nodes), Some(symbols), Some(bits)) =
            (num(0), num(1), num(2), num(3))
        else {
            eprintln!("--solver-dags takes count,nodes,symbols,bits[,heavy]");
            return ExitCode::from(2);
        };
        let heavy = f.get(4) == Some(&"heavy");
        let Some(clock) = crate::counter::free_running() else {
            eprintln!("instruction counters are unavailable");
            return ExitCode::FAILURE;
        };
        probe::set_clock(clock);
        probe::set_cpu_clock(crate::counter::cpu_clock());
        let mut out =
            std::io::BufWriter::new(std::fs::File::create(path).expect("create the file"));
        let _ = writeln!(out, "# {}; dags {spec}", setting());
        let mut counters = Counters::open();
        warm_up();
        let _ = probe::take_calls();
        let eng = engine();
        let name = format!("dags/{spec}");
        let (mut instr, mut pass, mut n) = (0u64, 0u64, 0usize);
        for i in 0..count {
            let mut cx = Context::new();
            let root = workload::dag(
                &mut cx,
                0x5eed + i,
                Dag {
                    width: workload::width(bits as u16),
                    symbols: symbols as usize,
                    nodes: nodes as usize,
                    heavy_ops: heavy,
                },
            );
            let start = counters.start();
            let o = eng.run(&mut cx, &[root], Run::default()).expect("run");
            let reading = counters.stop(start);
            instr += reading.instructions.unwrap_or(0);
            pass += o.stats.pass_work;
            let calls = probe::take_calls();
            n += calls.len();
            line(&mut out, &name, i as usize, &calls);
            let _ = writeln!(
                out,
                "R\t{name}\t{i}\tinstr={}\tpass={}\tend={:?}",
                reading.instructions.unwrap_or(0),
                o.stats.pass_work,
                o.roots[0].end
            );
            let _ = out.flush();
        }
        let _ = writeln!(out, "T\t{name}\t{count}\tinstr={instr}\tpass={pass}\tms=0");
        eprintln!("{name}: {n} calls, {:.2} G instr", instr as f64 / 1e9);
        ExitCode::SUCCESS
    }

    /// `--solver-fuel FILE BITS`: each expression of FILE (one per line, at BITS bits) through
    /// the MBA rows' engine at the default budget and fuels 2^18 down to 2^8: instructions, CPU
    /// time, how the run ended, the result's size, solver calls and the longest one.
    pub fn fuel(path: &str, bits: u16) -> ExitCode {
        use bitwright::ParseOptions;
        let Some(clock) = crate::counter::free_running() else {
            eprintln!("instruction counters are unavailable");
            return ExitCode::FAILURE;
        };
        probe::set_clock(clock);
        probe::set_cpu_clock(crate::counter::cpu_clock());
        let text = std::fs::read_to_string(path).expect("read the file");
        let mut counters = Counters::open();
        warm_up();
        println!("# {}", setting());
        for (i, line) in text.lines().enumerate() {
            for fuel in [
                None,
                Some(1u64 << 18),
                Some(1 << 16),
                Some(1 << 14),
                Some(1 << 12),
                Some(1 << 10),
                Some(1 << 8),
            ] {
                // A fresh engine: no answers remembered from another fuel.
                let eng = engine();
                let mut cx = Context::new();
                let e = cx
                    .parse(line, &ParseOptions::width(crate::workload::width(bits)))
                    .expect("parses");
                let _ = probe::take_calls();
                let c0 = (crate::counter::cpu_clock())();
                let start = counters.start();
                let o = eng
                    .run(&mut cx, &[e], crate::symbolic_cost::run_of(fuel))
                    .expect("run");
                let reading = counters.stop(start);
                let cpu = (crate::counter::cpu_clock())().saturating_sub(c0);
                let calls = probe::take_calls();
                let longest = calls.iter().map(|c| c.instr).max().unwrap_or(0);
                let steps: u64 = calls.iter().map(|c| c.steps).sum();
                let size = match cx.dag_size(&[o.roots[0].expr], u32::MAX) {
                    Ok(bitwright::Bounded::Exact(n)) => n,
                    _ => 0,
                };
                println!(
                    "{}\t{}\t{:.3} G\t{:.1} ms\t{:?}\tsize {size}\tcalls {}\tsteps {steps}\tlongest {:.3} G\tpass {}",
                    i + 1,
                    crate::symbolic_cost::fuel_label(fuel),
                    reading.instructions.unwrap_or(0) as f64 / 1e9,
                    cpu as f64 / 1e6,
                    o.roots[0].end,
                    calls.len(),
                    longest as f64 / 1e9,
                    o.stats.pass_work
                );
            }
        }
        ExitCode::SUCCESS
    }

    /// Reads a question written by `probe::question_text`.
    pub fn read_question(text: &str) -> Option<bitwright::mba::MbaExpr> {
        use bitwright::mba::{MOp, MbaExpr};
        use bitwright::{BitVec, Width};
        let width = |s: &str| Width::new(s.parse().ok()?).ok();
        let (vars, nodes) = text.trim().split_once(';')?;
        let vars: Vec<Width> = vars.split(',').map(width).collect::<Option<_>>()?;
        let mut m = MbaExpr::new(vars);
        for tok in nodes.split_whitespace() {
            let (op, args) = match tok.split_once('@') {
                Some((o, a)) => (
                    o,
                    a.split(',')
                        .map(|x| x.parse().ok())
                        .collect::<Option<Vec<u32>>>()?,
                ),
                None => (tok, Vec::new()),
            };
            let r = if let Some(v) = op.strip_prefix('v') {
                m.push(MOp::Var(v.parse().ok()?), &[])
            } else if let Some(c) = op.strip_prefix('c') {
                let (hex, w) = c.split_once(':')?;
                let w = width(w)?;
                let mut limbs = Vec::new();
                let digits = hex.as_bytes();
                let mut end = digits.len();
                while end > 0 {
                    let start = end.saturating_sub(16);
                    let chunk = std::str::from_utf8(&digits[start..end]).ok()?;
                    limbs.push(u64::from_str_radix(chunk, 16).ok()?);
                    end = start;
                }
                m.push(MOp::Const(BitVec::from_limbs(w, &limbs).ok()?), &[])
            } else if let Some(k) = op.strip_prefix("<<") {
                m.push(MOp::Shl(k.parse().ok()?), &args)
            } else if let Some(k) = op.strip_prefix(">>") {
                m.push(MOp::LShr(k.parse().ok()?), &args)
            } else if let Some((c, w)) = op.split_once(':') {
                let cast = match c {
                    "zx" => MOp::Zext,
                    "sx" => MOp::Sext,
                    "tr" => MOp::Trunc,
                    _ => return None,
                };
                m.push_cast(cast, *args.first()?, width(w)?)
            } else {
                let o = match op {
                    "+" => MOp::Add,
                    "-" => MOp::Sub,
                    "*" => MOp::Mul,
                    "n" => MOp::Neg,
                    "&" => MOp::And,
                    "|" => MOp::Or,
                    "^" => MOp::Xor,
                    "~" => MOp::Not,
                    _ => return None,
                };
                m.push(o, &args)
            };
            r.ok()?;
        }
        Some(m)
    }

    /// One question asked of a fresh solver at the engine's budget (evidence off, as the
    /// engine asks when backend certificates are not trusted): instructions, CPU nanoseconds,
    /// steps, answer.
    pub fn ask_once(
        counters: &mut Counters,
        m: &bitwright::mba::MbaExpr,
        steps: u64,
    ) -> (u64, u64, u64, &'static str) {
        use bitwright::mba::{MbaAnswer, MbaBudget, MbaSolver, NormalFormSolver};
        let solver = NormalFormSolver::default();
        let budget = MbaBudget::default().with_steps(steps).with_evidence(false);
        let _ = probe::take_solver_steps_pub();
        let c0 = (crate::counter::cpu_clock())();
        let start = counters.start();
        let a = solver.solve(m, &budget);
        let reading = counters.stop(start);
        let cpu = (crate::counter::cpu_clock())().saturating_sub(c0);
        let spent = probe::take_solver_steps_pub();
        let answer = match a {
            MbaAnswer::Simplified { .. } => "simplified",
            MbaAnswer::NoSimpler => "no simpler",
            MbaAnswer::Unsupported(_) => "unsupported",
            _ => "exhausted",
        };
        (reading.instructions.unwrap_or(0), cpu, spent, answer)
    }

    /// `--solver-search FILE ITERS`: a hill climb from each question in FILE towards a longer
    /// solver call (instructions at the default 2^20 steps, evidence off): random mutations of
    /// one node (an operator, an operand, a constant, a variable) kept when the call takes
    /// longer, within the default limits (at most 8 variables, 2,048 nodes). Prints each
    /// improvement and the best question.
    pub fn search(path: &str, iters: u64) -> ExitCode {
        use bitwright::mba::{MOp, MbaExpr};
        use bitwright::{BitVec, Width};
        let text = std::fs::read_to_string(path).expect("read the file");
        let mut counters = Counters::open();
        warm_up();
        let mut rng = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move |n: u64| {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng % n.max(1)
        };
        // Rebuilds `m` with node `i` replaced by `op` over `args` (operands must stay earlier).
        let rebuild = |m: &MbaExpr, i: usize, op: MOp, args: [u32; 2]| -> Option<MbaExpr> {
            let mut out = MbaExpr::new(m.vars().to_vec());
            for (j, n) in m.nodes().iter().enumerate() {
                let (o, a) = if j == i { (op, args) } else { (n.op, n.args) };
                let r = match o {
                    MOp::Zext | MOp::Sext | MOp::Trunc => out.push_cast(o, a[0], n.width),
                    _ => out.push(o, &a[..o.arity()]),
                };
                r.ok()?;
            }
            Some(out)
        };
        for (qi, line) in text.lines().enumerate() {
            let q = line.rsplit('\t').next().unwrap_or(line);
            let Some(mut best) = read_question(q) else {
                continue;
            };
            let _ = ask_once(&mut counters, &best, 1 << 10);
            let (mut score, _, _, _) = ask_once(&mut counters, &best, 1 << 20);
            println!("question {}: start {:.3} G", qi + 1, score as f64 / 1e9);
            for it in 0..iters {
                let n = best.nodes().len();
                let i = next(n as u64) as usize;
                let node = best.nodes()[i];
                let w = node.width;
                let same_width: Vec<u32> = (0..i as u32)
                    .filter(|&j| best.nodes()[j as usize].width == w)
                    .collect();
                let pick = |r: u64| {
                    same_width
                        .get(r as usize % same_width.len().max(1))
                        .copied()
                };
                let ops = [MOp::Add, MOp::Sub, MOp::Mul, MOp::And, MOp::Or, MOp::Xor];
                let cand = match (&node.op, next(4)) {
                    (MOp::Const(_), _) => {
                        let v = next(u64::MAX);
                        let k = BitVec::from_limbs(w, &[v]).ok().or_else(|| {
                            BitVec::from_u64(w, v & ((1u64 << w.bits().min(63)) - 1)).ok()
                        });
                        k.and_then(|k| rebuild(&best, i, MOp::Const(k), [0, 0]))
                    }
                    (MOp::Var(_), _) => {
                        let vars = best.vars().len() as u64;
                        let v = next(vars) as u32;
                        (best.vars()[v as usize] == w)
                            .then(|| rebuild(&best, i, MOp::Var(v), [0, 0]))
                            .flatten()
                    }
                    (op, 0) if op.arity() == 2 => {
                        rebuild(&best, i, ops[next(6) as usize], node.args)
                    }
                    (op, 1 | 2) if op.arity() == 2 => {
                        let mut a = node.args;
                        let k = next(2) as usize;
                        match pick(next(1 << 20)) {
                            Some(x) => {
                                a[k] = x;
                                rebuild(&best, i, *op, a)
                            }
                            None => None,
                        }
                    }
                    (op, _)
                        if op.arity() == 1 && !matches!(op, MOp::Zext | MOp::Sext | MOp::Trunc) =>
                    {
                        let o = [MOp::Not, MOp::Neg][next(2) as usize];
                        rebuild(&best, i, o, node.args)
                    }
                    _ => None,
                };
                let Some(cand) = cand else {
                    continue;
                };
                if cand.width() != Some(Width::new(w.bits()).unwrap_or(w)) && i + 1 == n {
                    continue;
                }
                let (instr, cpu, spent, answer) = ask_once(&mut counters, &cand, 1 << 20);
                if instr > score {
                    score = instr;
                    best = cand;
                    println!(
                        "  {it}: {:.3} G instr, {:.1} ms CPU, {spent} steps, {answer}",
                        instr as f64 / 1e9,
                        cpu as f64 / 1e6
                    );
                }
            }
            println!("best\t{score}\t{}", probe::question_text(&best));
        }
        ExitCode::SUCCESS
    }

    /// `--solver-worst FILE`: every question in FILE (one per line, the question last after a
    /// tab, as `BW_DUMP_FILE` writes them), asked of a fresh solver at 2^16, 2^20 (the
    /// default) and 2^24 steps.
    pub fn worst(path: &str) -> ExitCode {
        let text = std::fs::read_to_string(path).expect("read the file");
        let mut counters = Counters::open();
        // Process-wide tables (synthesis) first.
        warm_up();
        let mut rows = Vec::new();
        for (i, line) in text.lines().enumerate() {
            let q = line.rsplit('\t').next().unwrap_or(line);
            let Some(m) = read_question(q) else {
                eprintln!("line {}: not a question", i + 1);
                continue;
            };
            // The narrow synthesis index of this width, once.
            let _ = ask_once(&mut counters, &m, 1 << 10);
            for steps in [1u64 << 16, 1 << 20, 1 << 24] {
                let (instr, cpu, spent, answer) = ask_once(&mut counters, &m, steps);
                println!(
                    "{}\t2^{}\t{instr}\t{:.2}\t{spent}\t{answer}\t{:.0}\t{}\t{}",
                    i + 1,
                    steps.trailing_zeros(),
                    cpu as f64 / 1e6,
                    instr as f64 / spent.max(1) as f64,
                    m.nodes().len(),
                    m.vars().len()
                );
                rows.push((instr, i));
            }
        }
        ExitCode::SUCCESS
    }
}
