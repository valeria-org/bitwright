# Valeria rule coverage

The default simplifier missed carry/borrow comparisons, BMI2 cancellation and
support-mask identities, truncation factoring, and some canonical arithmetic,
shift and conditional min/max forms. Seventy-seven local rules close the measured
gaps. Algebra already handled by the linear, bitwise and comparison passes was
not copied wholesale from Valeria's Rust tables.

## Paired measurement

Baseline: Bitwright 0.4.1 at `c529dd3`. Source corpus: Valeria
`9336e36f8653c889b553bc02e8a2da4772fcab06`, the five committed
`crates/engine/valeria-symex/rules-src/**/*.vrl` files. Both sides used the same
release build conditions and input TSV, at widths 8, 16, 32 and 64.

There are 3,010 source rules. The bounded instantiator produced 24,527 cases
from 2,912 rules. Ninety-eight rules had no admitted instance: unsupported host
queries, symbolic guards, unexercised guard conditions and unsupported forms
are reported explicitly in the inventory. They are not evidence of coverage.

| Measure | Standard before | Standard after | Deobfuscate before | Deobfuscate after |
|-|-|-|-|-|
| Same normalized form as reference | 19,456 | 20,166 | 19,522 | 20,174 |
| Different form, no larger than reference | 4,427 | 4,361 | 4,393 | 4,353 |
| Output larger than reference | 644 | 0 | 612 | 0 |
| Sum of output expression tree sizes | 53,655 | 51,657 | 53,467 | 51,625 |
| Refuted reference instances / parse errors | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |

No case produced a larger expression than its own baseline output. These are
expression-shape measurements, not executable size or runtime benchmarks.
The fixed corpus SHA-256 is
`e50ece62c517df4645af4f842e71e974d84f7e0c8c164b28b7d467c21feab5e2`.

The probe evaluates each input/reference pair at 32 deterministic points before
measuring simplification. This rejects bad instances; agreement is not a proof.
Each imported rule separately passes the existing rule checker, which exhausts
small widths and samples larger widths through 512 bits. The regenerated ledger
contains 114 checked rules total, with no unsound/inconclusive results or failed
examples. This is the existing Bitwright evidence policy, not a universal SMT
proof. The default-strategy regression reaches all 77 added examples.

## Reproduce

Generate probes without executing Valeria or changing its rule packs:

```sh
python tools/valeria_rule_cases.py --rules ../valeria/crates/engine/valeria-symex/rules-src --output cases.tsv --inventory inventory.json
cargo run --release -p bitwright --example valeria_rule_audit < cases.tsv > standard.tsv
cargo run --release -p bitwright --example valeria_rule_audit -- --deobfuscate < cases.tsv > deobfuscate.tsv
```

To reproduce the baseline, use a separate checkout at `c529dd3`, copy only the
audit example into it, and use its own target directory. Feed it the same TSV.
Do not replace the baseline with another historical report.

Validation performed:

```sh
cargo run --release -p bitwright-cli -- check bitwright/src/rules/corpus/core.bwr --ledger bitwright/src/rules/corpus/core.bwr.proof
cargo test --release -p bitwright --lib check::tests::corpus_
cargo test --release -p bitwright --test recovery_rules
```

Five corpus tests passed (192 other library tests filtered out), including
ledger freshness and application correctness. One integration test passed,
checking all 77 default-strategy examples. No ignored tests or full workspace
suite were run.

## Semantic boundary

The new rules use Bitwright's total bit-vector semantics. Valeria's ISA-masked
shift counts are made explicit by the audit translator; they must remain
explicit in a runtime adapter too. Typed casts keep their actual widths.
Unknown source guards are skipped, never silently assumed true. The inventory
does not justify removing Valeria's compatibility evaluator, host queries or
legacy fallback, nor does this upstream port switch Valeria's runtime pipeline.
