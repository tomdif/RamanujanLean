# Contributing

Use the toolchain in [lean-toolchain](lean-toolchain) and the Mathlib revision in
[lake-manifest.json](lake-manifest.json). Module names begin with `RamanujanTau`.
Build the affected module first, then run `lake build` before publishing a change
to the public import graph.

## Proofs and certificates

- Do not introduce `sorry`, `admit`, custom axioms, or `native_decide`.
- State missing mathematical inputs as explicit hypotheses. A theorem with an
  explicit hypothesis is not an unconditional proof of its intended application.
- Treat Python and other discovery programs as certificate generators. The Lean
  proof must check the certificate and identify it with the actual arithmetic
  object, including any infinite remainder or truncation bound.
- Add public results to the appropriate axiom audit. Expected dependencies are
  `propext`, `Classical.choice`, and `Quot.sound` only.
- Keep expensive certificates stable when changing downstream proofs. Their
  initial kernel checks can take substantial time and memory.

For finite-arithmetic changes, run:

```sh
lake build
lake env lean scripts/audit/finite_arithmetic.lean
python3 scripts/boylanwebb/check_cert29_error.py
```

Regeneration commands and the distinction between discovery, checking, and
evaluation are documented in [the finite-arithmetic guide](docs/FINITE_ARITHMETIC.md).

## Documentation and repository checks

Keep the [overview](README.md) concise. Put detailed theorem statements in the
[catalog](docs/RESULTS.md), current verification boundaries in
[STATUS.md](docs/STATUS.md), and link research records from the
[documentation guide](docs/README.md). Date historical notes and state when a
later proof supersedes them. Distinguish a sufficient threshold from a proved
minimal threshold, and a finite experiment from an infinite theorem.

Run `python3 scripts/check_repository.py` and `git diff --check` before publishing.
The repository checker validates local Markdown links, project imports, and
proof-source hygiene. It is not a Lean parser or a proof checker.

Commit intended sources, reproducible certificate generators, and documented
data. Leave unrelated local experiments, generated executables, and private
scratch work outside a change. Do not remove another contributor's local work
to make a working tree appear clean.
