# The command line

`bitwright-cli` builds a `bitwright` binary for rule authors. Reports go to standard output
(also when a check fails); errors, including a rule file's compile diagnostics, go to standard
error. A command exits with 0 on success, 1 when a check fails (or `lint` finds errors), and 2
on bad usage or unreadable input. `--` ends the options, for an expression starting with `-`.

| Command | What it does |
|-|-|
| `bitwright check rules.bwr` | Checks every rule's soundness and examples; exits 1 unless every rule is sound and every example holds. `--thorough` checks more widths and bits exhaustively; `--ledger out.proof` writes the proof ledger; `--against rules.bwr.proof` compares with an existing ledger. |
| `bitwright lint rules.bwr` | Prints every diagnostic, rendered with its position. |
| `bitwright smt rules.bwr` | Prints each rule's soundness obligation as SMT-LIB, separated by `(reset)`, at every admitted assignment of the widths 8, 32 and 64; a rule admitted at none of those gets three other admitted assignments. `--widths 13` (one width per width variable) and `--rule group::name` narrow it. A rule with no obligation prints a line the solver echoes (`SKIPPED …`) and the command exits 1. |
| `bitwright catalog [rules.bwr]` | A Markdown catalog of the rules: the built-in rules without a file. |
| `bitwright explain BW0302` | What a diagnostic code means and how to fix it. |
| `bitwright simplify '<expr>'` | Simplifies an expression (`--width 32`), deobfuscating: the rules, the normal-form passes and the MBA service with the native normal-form solver, every answer proved by bitwright itself; `--standard` runs only the rules and the standard passes. Each `--assume '<predicate>'` adds a 1-bit constraint; a result that relies on constraints is followed by `# relies on 0, 2` (their positions among the `--assume` options). |

A typical workflow for a rule file:

```text
bitwright lint my.bwr
bitwright check my.bwr --ledger my.bwr.proof
bitwright smt my.bwr | z3 -in | sort | uniq -c      # every line should be `unsat` (or `| bitwuzla`)
```

and in continuous integration:

```text
bitwright check my.bwr --against my.bwr.proof
```

which fails when a rule changed without its ledger being regenerated, when a rule is not sound,
or when an example stopped holding.
