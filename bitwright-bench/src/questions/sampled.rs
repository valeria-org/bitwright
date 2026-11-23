//! Check a sampled word, not the claim that the exporter's samples were exhaustive.
use super::{Dump, read};
use bitwright::batch::{self, Answer, Ask, Session, Split};
use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, NfOptions, NormalFormSolver};
use bitwright::prove::{self, Config, Outcome, Simplifiers};
use bitwright::{Assumptions, BitVec, Context, Facts, FnEnv, ParseOptions, SymbolKey, Width};
use std::{collections::BTreeMap, error::Error, fs, sync::Arc};

type Result<T, E = Box<dyn Error>> = std::result::Result<T, E>;

fn word(s: &str, width: Width) -> Result<BitVec> {
    Ok(BitVec::from_u64(
        width,
        u64::from_str_radix(s.strip_prefix("0x").ok_or("expected hex word")?, 16)?,
    )?)
}

struct Retry {
    stock: Simplifiers,
    forms: MbaConfig,
    solver: Arc<NormalFormSolver>,
    word: Engine,
}

impl Retry {
    fn new() -> Result<Self> {
        let solver = Arc::new(NormalFormSolver::new(
            NfOptions::default()
                .with_memo(1 << 14)
                .with_basis_sums(true),
        ));
        let stock = MbaConfig::default().with_opaque_sweep(true);
        let forms = stock.clone().with_noise_forms(true).with_known_atoms(true);
        Ok(Self {
            stock: Simplifiers::new()
                .with_mba(stock)
                .with_mba_solver(solver.clone()),
            forms: forms.clone(),
            solver: Arc::clone(&solver),
            word: Engine::builder()
                .builtin()
                .strategy(Strategy::deobfuscate().with_mba(forms))
                .mba_solver(solver)
                .build()?,
        })
    }

    fn check(&self, dump: &Dump, sample: &str, deep: u64) -> Result<(&'static str, &'static str)> {
        let [root] = dump.roots.as_slice() else {
            return Err("expected one root".into());
        };
        let mut cx = Context::new();
        let parse = ParseOptions::width(Width::W64);
        let value = cx.parse(root.trim(), &parse)?;
        let target = word(sample, cx.width(value)?)?;
        let k = cx.constant(&target)?;
        let original = cx.eq(value, k)?;
        let mut checks = vec![original];
        let mut assumptions = Assumptions::new();
        for (literal, text) in &dump.assumes {
            let e = cx.parse(text.trim(), &parse)?;
            let v = word(literal, cx.width(e)?)?;
            assumptions.assume(&mut cx, e, Facts::constant(&v))?;
            let w = cx.constant(&v)?;
            checks.push(cx.eq(e, w)?);
        }
        let under = (!dump.assumes.is_empty()).then_some(&assumptions);
        if !dump.config.split_whitespace().any(|s| s == "simplify=true") {
            return Err("expected simplify=true".into());
        }
        let number = |key: &str| -> Result<u64> {
            Ok(dump
                .config
                .split_whitespace()
                .find_map(|s| s.strip_prefix(key))
                .ok_or_else(|| format!("missing {key}"))?
                .parse()?)
        };
        let cfg = Config::default()
            .with_max_nodes(number("nodes=")?.try_into()?)
            .with_max_conflicts(number("conflicts=")?)
            .with_max_propagations(number("propagations=")?)
            .with_sweeping(false);
        for (stage, fuel) in [("stock", number("fuel=")?), ("deep", deep), ("forms", deep)] {
            let proof = cfg.with_simplify_fuel(fuel);
            let (outcome, stage) = if stage == "forms" {
                let run = Run::default().with_per_call(Budget::fuel(fuel));
                let run = match under {
                    None => run,
                    Some(a) => run.with_assumptions(a),
                };
                let out = self.word.run(&mut cx, &[value], run)?;
                let goal = cx.eq(out.roots[0].expr, k)?;
                if cx.as_const(goal)?.is_some_and(|v| !v.is_zero()) {
                    return Ok(("proved", stage));
                }
                // Ask the residual whole once. Only a budget/size stop can
                // trigger a single split; no nested splits or hub searches.
                let cases = Session::with_simplifiers(
                    batch::Config::default()
                        .with_threads(1)
                        .with_prove(proof)
                        .with_split(Split::none().with_cases(1)),
                    Simplifiers::new()
                        .with_mba(self.forms.clone())
                        .with_mba_solver(self.solver.clone()),
                );
                let ask = match under {
                    Some(a) => Ask::valid(goal).under(a),
                    None => Ask::valid(goal),
                };
                let reply = cases
                    .run(&mut cx, &[ask])?
                    .pop()
                    .ok_or("missing validity reply")?;
                let verdict = match reply.answer {
                    Answer::Proved => Outcome::Proved(None),
                    Answer::Refuted(m) => Outcome::Refuted(m),
                    Answer::Unknown(why) => Outcome::Unknown(why),
                    _ => return Err("unexpected validity reply".into()),
                };
                (
                    verdict,
                    if cases.stats().case_splits > 0 {
                        "cases"
                    } else {
                        stage
                    },
                )
            } else {
                (
                    prove::valid_under_with(&mut cx, original, under, &proof, &self.stock)?,
                    stage,
                )
            };
            match outcome {
                Outcome::Proved(_) => return Ok(("proved", stage)),
                Outcome::Refuted(model) => {
                    // A rewrite may erase a symbol. Complete it before evaluating the
                    // original, never report a witness of just the residual.
                    let env = FnEnv(|s: &SymbolKey, w: Width| {
                        Some(
                            model
                                .iter()
                                .find(|(k, _)| k == s)
                                .map_or_else(|| BitVec::zero(w), |(_, v)| *v),
                        )
                    });
                    let vals = cx.eval(&checks, &env)?;
                    if !vals[0].is_zero() || vals[1..].iter().any(BitVec::is_zero) {
                        return Err("counterexample failed original question replay".into());
                    }
                    return Ok(("refuted", stage));
                }
                Outcome::Unknown(_) if matches!(stage, "cases" | "forms") => {
                    return Ok(("unknown", stage));
                }
                Outcome::Unknown(_) => (),
                _ => return Err("unhandled proof outcome".into()),
            }
        }
        unreachable!("the final forms stage returns its verdict")
    }
}

pub(crate) fn sampled(dir: &str) -> Result<()> {
    let mut files = fs::read_dir(dir)?.collect::<std::io::Result<Vec<_>>>()?;
    files.sort_by_key(|f| f.file_name());
    let retry = Retry::new()?;
    let mut tally = BTreeMap::new();
    for f in files {
        if !f.file_type()?.is_file() || f.path().extension().is_none_or(|ext| ext != "txt") {
            continue;
        }
        let text = fs::read_to_string(f.path())?;
        let header = |key: &str| {
            text.lines()
                .take_while(|l| !l.starts_with("## "))
                .find_map(|l| l.strip_prefix(key))
                .map(str::trim)
        };
        if header("# kind:") != Some("constant") {
            continue;
        }
        let Some(sample) = header("# sampled:") else {
            continue;
        };
        let name = f.file_name();
        let name = name.to_string_lossy();
        let deep = header("# deep fuel:")
            .ok_or_else(|| format!("{name}: missing deep fuel"))?
            .parse()?;
        let (verdict, stage) = retry
            .check(&read(&name, &text), sample, deep)
            .map_err(|e| format!("{name}: {e}"))?;
        println!("{name}\t{verdict}\t{stage}");
        *tally.entry((verdict, stage)).or_insert(0usize) += 1;
    }
    if tally.is_empty() {
        return Err("no sampled constant questions found".into());
    }
    for ((verdict, stage), count) in tally {
        eprintln!("{stage}\t{verdict}\t{count}");
    }
    Ok(())
}
