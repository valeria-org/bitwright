# Valeria rule coverage

## As merged (against 0.6.0)

The ports landed on top of 0.6.0, together with the signed-comparison flag rules
(`core.sign`). Measured there, some of them made results larger, and those were
left out or narrowed:

- **Rules that do not see sharing.** A rule rewrites one node; if an operand it
  consumes has other users, the operand stays and the result adds nodes. On the
  generated random DAGs of `bitwright-bench --corpus-diff`, 23 of 200 inputs per
  width ended larger through `factor_mul_add`, `factor_mul_sub`, `collect_mul_add`,
  `collect_shift_add`, `neg_mul_constant`, `ones_minus`, `ult_add_carry`,
  `lshr_mask_constant`, `boolean_mask_clear` and the bitwise `xor_and_self`,
  `xor_or_self`, `and_xor_self`. They are left out. (`factor_mul_sub` also takes
  bitwuzla 78 s at 16 bits and over 600 s at 33, past the nightly proof's limit.)
- **Rules that reshape an MBA question.** `not_plus_constant`, `negative_plus_ones`,
  `not_add_constant` and `shl_or_constant` rewrote subterms before the MBA service
  read them, and six lines of CoBRA's datasets were no longer solved. Left out;
  the linear pass decides the same algebra.
- **Construction.** The extraction of a constant logical shift, and `(x >>u c) & 1`,
  gave the same value a second spelling next to the shift it came from
  (`x >>u 6` beside `zext(extract<6, 2>(x))`). Left out; they closed no audit case
  on 0.6.0. The concatenation of adjacent constants stays.
- **Dead or subsumed rules.** `recombine_shifted_field_add` never fires (`add_disjoint`
  turns its `+` into `|` first), and `recombine_masked_field_or`/`_add` are reached
  through `shifted_masked_add`; all three are left out.
- **Changed.** `split_mask_add` needs only disjoint masks (`(x & m) + ((x & n) + c)`
  is `(x & (m | n)) + c`); `mask_or_add_constant_carry` covers a constant that
  carries into the kept bits; `split_mask_increment` reads the linear pass's `a - ~b`.
  The guarded negation rules' examples use `| 2`, since `neg_or_one` now turns
  `-(x | 1)` into `~x` first. Rules that complement both sides of a comparison, and
  that drop bits set outside both operands' masks, keep those results no larger
  than 0.6.0's.

Audit, paired against 0.6.0 (`b691766`), Valeria `0ed081dff` (the sign guards of
r0181/r0182 already fixed there, so no patch is applied), 28,134 cases from all
3,010 rules, TSV SHA-256
`51d3ebd7dee9c91a4e28073b5698f254c82e0a60649395866fe06f7423f001d8`:

| Measure | Standard 0.6.0 | Standard merged | Deobfuscate 0.6.0 | Deobfuscate merged |
|-|-|-|-|-|
| Same normalized form as reference | 21,992 | 23,548 | 22,200 | 23,664 |
| Different form, no larger than reference | 4,591 | 4,418 | 4,507 | 4,360 |
| Output larger than reference | 1,551 | 168 | 1,427 | 110 |
| Sum of output expression tree sizes | 69,958 | 63,068 | 69,198 | 62,753 |
| Outputs larger / smaller than 0.6.0's | | 0 / 1,512 | | 0 / 1,539 |

No output is larger than 0.6.0's. The generator (`tools/valeria_rule_cases.py`)
now reads a rule only at the start of a line: Valeria's rule sources gained a
comment header ("the Rust rule tables"), which it took for a rule.

The sections below are the port's record as measured against 0.4.1, with the
rules and construction changes it had then.

## Complete guarded follow-up

The follow-up accounts for the remaining 98 source rules. `--complete` adds
constructive known-bit witnesses, one-bit and 33–128-bit widths, independent
shift counts, exact aliases for equality guards, and nonzero truthiness for
Valeria's binary `If`/`Select`. Unsupported legacy SAR and partial division
remain explicit refusals. Every source rule now has admitted probes; a complete
inventory with a zero-case rule fails instead of silently claiming coverage.

Thirty-four additional built-in rules and three construction canonicalizations
close the newly measured gaps. Rules already handled by Bitwright are not
duplicated. Negation comparisons retain the `INT_MIN` exclusion, Boolean-mask
rules retain their 0/1 premise, and masked field rewrites retain their carry and
width conditions. The complete corpus contains **28,134 cases from all 3,010
rules**, not an exhaustive enumeration of every rule's possible bindings.

The paired baseline for this follow-up is `c19a5c0` (the first 77 ports). The
input TSV and evaluator are the same on both sides; full-width refutation
samples now exercise bits above 64 and check simplified outputs as well.

| Measure | Standard before | Standard after | Deobfuscate before | Deobfuscate after |
|-|-|-|-|-|
| Same normalized form as reference | 22,654 | 23,599 | 22,779 | 23,639 |
| Different form, no larger than reference | 4,608 | 4,535 | 4,599 | 4,495 |
| Output larger than reference | 872 | 0 | 756 | 0 |
| Sum of output expression tree sizes | 67,422 | 63,352 | 66,851 | 63,155 |
| Refuted references / outputs / parse errors | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |

No individual output grew relative to its baseline. The complete TSV SHA-256 is
`c4b811afb9974f0d78c6b6f1954f71a08b7dfb5467d78a0c0e4a634c98ae3d1b`.

### A source defect found by the audit

The original Valeria `universal.r0181` / `r0182` guards treated a written shift
of W−1 as an effective sign-bit shift. At W=33–63, Valeria masks that count with
31. Reconstruction from W=32 into U=33–63 also masks its left shift of 32 to
zero. Additionally, legacy SAR is modeled only through 64 bits with a
same-width count. These invalid cases must not be ported as identities.

The consuming Valeria change tightens both guards, adds a regression that fails
before the fix, and regenerates its VRL, legacy pack and production VMDL pack.
For reproducing the audit from the original source revision, apply
`tools/fixtures/valeria-sign-guards.patch` to the **typed rule sources** in that
Valeria checkout. This fixture is sufficient for the audit; it is not the full
runtime fix. Both sides of the paired measurement use the corrected corpus.

```sh
python tools/valeria_rule_cases.py --rules ../valeria/crates/engine/valeria-symex/rules-src --complete --output complete.tsv --inventory complete.json
cargo run --release -p bitwright --example valeria_rule_audit < complete.tsv > standard.tsv
cargo run --release -p bitwright --example valeria_rule_audit -- --deobfuscate < complete.tsv > deobfuscate.tsv
python -m unittest discover -s tools -p test_valeria_rule_cases.py
cargo test --release -p bitwright --test remaining_rules --test recovery_rules
cargo test --release -p bitwright --lib check::tests::corpus_
cargo test --release -p bitwright --lib expr::tests::construction_table_is_sound
```

The corpus checker now covers 148 rules. The follow-up tests cover all 34 new
examples, rejected unguarded signed-negation cancellation, and extraction /
concatenation against the independent bit-serial evaluator, including clipped
slices, huge counts and 512-bit boundaries. Six Python tests pin the audit's
guard, mask, truthiness and partial-operation contracts. Valeria's four sign
reconstruction tests and four production-artifact tests pass under `rapid`.

These remain exhaustive small-width and sampled wide-width checks, not universal
SMT proofs. All source rules have exercised witnesses; this does not prove a
wholesale runtime migration or justify deleting the legacy evaluator.

## Initial portable pass

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
