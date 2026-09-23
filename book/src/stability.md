# Stability

bitwright stays at 0.x until its API has been used in production for a release cycle. Within
that, the rules below already hold.

**API.** Every public enum (other than closed sets such as `Truth`) and every configuration
struct is `#[non_exhaustive]`, so adding a variant or a field is not a breaking change.
Configuration structs have `Default` (or a constructor such as `Deadline::new`) and a `with_*`
setter per field; build them that way:

```rust
use bitwright::engine::{Budget, Run};

let run = Run::default().with_per_call(Budget::default().with_rewrites(1_000));
# let _ = run;
```

`cargo-semver-checks` runs against the last release in continuous integration. The minimum
supported Rust version is 1.88; raising it is a minor-version change.

**Results.** Users snapshot printed output, so simplification results have their own contract:
a patch release never changes a result except to fix unsoundness (named in the changelog by rule
id); a minor release may, and lists the changes under "Behavior changes". The printer's format and
the canonical order change only in minor releases.

**Rule files.** The rule-language edition (`bitwright 1;`) is frozen within a major version, and
diagnostic codes are stable: a code is never reused for a different meaning.

**Determinism.** The same input gives the same output on every run and every platform: no
global state, no hash-map iteration order in results, no environment variables, and no clock
unless you supply a deadline (which then decides only when to stop).
