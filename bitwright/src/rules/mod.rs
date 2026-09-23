//! The rule language (`.bwr`): typed, width-polymorphic rewrite rules and identities, compiled
//! into [`RuleProgram`]s. See `docs/design.md` §7.
//!
//! ```
//! use bitwright::rules::RuleProgram;
//! let src = r#"
//! bitwright 1;
//! group demo {
//!     #[example("(p & q) + (p | q)" => "p + q")]
//!     identity add_and_or<W>(x: W, y: W) { (x & y) + (x | y) <=> x + y }
//! }
//! "#;
//! let program = RuleProgram::compile(src).unwrap();
//! assert_eq!(program.rules().len(), 1);
//! assert!(program.rules()[0].is_directed()); // the left side is larger: usable left to right
//! ```

// The reference rule application; the engine (next milestone) is its non-test consumer.
#[cfg_attr(not(all(test, feature = "check")), allow(dead_code))]
pub(crate) mod apply;
pub(crate) mod compile;
pub(crate) mod corpus;
mod diag;
pub(crate) mod eval;
pub mod ir;
mod ledger;
pub(crate) mod matcher;
pub(crate) mod order;

pub use compile::CompileLimits;
pub use diag::{CompileError, Diagnostic, Level, explain};
pub use ir::{
    ConstPred, FactPred, Group, LetDef, Literal, NodeId, Param, ParamKind, RNode, Rule, RuleId,
    RuleKind, Sort, WCmp, WCons, WExpr,
};
pub use ledger::Ledger;

/// The built-in rule files and their proof ledgers, as `(file name, source, ledger)`: the local
/// rules the engine links by default, and the equations of the equality-saturation service.
pub fn builtin_sources() -> [(&'static str, &'static str, &'static str); 2] {
    [
        ("core.bwr", corpus::CORE, corpus::CORE_LEDGER),
        ("eqsat.bwr", corpus::EQSAT, corpus::EQSAT_LEDGER),
    ]
}

#[cfg(any(test, feature = "check"))]
pub(crate) use compile::width_assignments;

/// Options for [`RuleProgram::compile_with`].
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct CompileOptions {
    /// Size limits (rule text may be untrusted).
    pub limits: CompileLimits,
}

setters!(CompileOptions {
    with_limits: limits: CompileLimits,
});

/// A compiled rule program: named groups of rules in priority order.
#[derive(Clone, Debug)]
pub struct RuleProgram {
    groups: Vec<Group>,
    rules: Vec<Rule>,
    diagnostics: Vec<Diagnostic>,
}

impl RuleProgram {
    /// Compiles `.bwr` source with the default limits.
    pub fn compile(src: &str) -> Result<RuleProgram, CompileError> {
        Self::compile_with(src, &CompileOptions::default())
    }

    /// Compiles `.bwr` source.
    pub fn compile_with(src: &str, opts: &CompileOptions) -> Result<RuleProgram, CompileError> {
        let (groups, rules, diagnostics) = compile::compile(src, &opts.limits)?;
        Ok(RuleProgram {
            groups,
            rules,
            diagnostics,
        })
    }

    /// Every rule, in source order.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Every group, in source order.
    pub fn groups(&self) -> &[Group] {
        &self.groups
    }

    /// The rule named `group::name`.
    pub fn rule(&self, name: &str) -> Option<&Rule> {
        self.rules.iter().find(|r| r.name == name)
    }

    /// Warnings and notes produced while compiling.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}
