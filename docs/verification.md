# Verification record

Checks of release v1.0.0, commit `6280393739de142f3c54160ce7083110ed55f194`, on 2026-10-14. Each run started from a fresh clone of this repository, followed the [build steps in the README](../README.md#build-and-verify) and used 12 threads on the author's Mac. Later releases change only comments, documentation and `comparator.json`; no Lean statement or proof differs from v1.0.0.

| Check | Command | Result |
| --- | --- | --- |
| Build | `lake build` | exit 0, 9986 jobs |
| Axioms | `#print axioms Erdos824.erdos_824` | `'Erdos824.erdos_824' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| Kernel replay | `lake env leanchecker --fresh Erdos824.Theorem` | exit 0 |
| Comparator | `comparator.json` with `definition_names` empty, nanoda enabled | exit 0: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" |

Comparator compares `Erdos824.erdos_824` and the definition `Erdos824.h` against [Challenge.lean](../Challenge.lean), which uses Mathlib definitions only and states Formal Conjectures' `h` and the right-hand side of its `erdos_824`, with `σ 1` written as `ArithmeticFunction.sigma 1`. It was not run against an export of the Formal Conjectures repository.

Tool versions: Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`, lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`. Comparator ran with its development `fake-landrun.sh`, not the Landrun sandbox.

## Controls

- nanoda accepted a correct proof and rejected a proof by `sorry` (exit 1) and an export with a tampered numeral (exit 101).
- With `h` in `Challenge.lean` changed from `a < b` to `a ≤ b`, Comparator rejected the solution: "Const does not match between challenge and target 'Erdos824.h'".

## `definition_names`

In v1.0.0 to v1.0.2, `comparator.json` listed `Erdos824.h` under `definition_names`. Comparator then checks that definition by name and type only, not its body. Since v1.0.3 the list is empty, so the body of `h` is compared as well; the run above used that configuration. `scripts/verify.sh` compares `h` with `Challenge.lean` at `pp.all` in every release.
