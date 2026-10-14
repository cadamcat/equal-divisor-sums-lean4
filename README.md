# Coprime pairs with equal divisor sums in Lean 4

Let `h(x)` count the pairs `1 ≤ a < b < x` with `gcd(a, b) = 1` and `σ(a) = σ(b)`. This repository proves in Lean 4 that `h(x) > x^(2−ε)` for every `ε > 0` and all sufficiently large `x`. This is [Erdős Problem #824](https://www.erdosproblems.com/824).

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- Developed with AI assistance (Claude Code and Codex); all proofs are verified by the Lean 4 kernel.

Each interface between the parts of the proof is stated as a proposition (`…_statement`) and discharged by a proved theorem in the final assembly. The only `sorry` is in `Challenge.lean`, Comparator's statement placeholder.

## Main result

```lean
theorem Erdos824.erdos_824 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ)
```

`h` is Formal Conjectures' definition (`FormalConjectures/ErdosProblems/824.lean`), and the theorem is the right-hand side of its `erdos_824`, whose answer is `True`. [Challenge.lean](Challenge.lean) states it with Mathlib definitions only, and [comparator.json](comparator.json) configures [Comparator](https://github.com/leanprover/comparator) to compare the two.

## Route

1. **Conditional bound** ([Erdos824/LiZhuang](Erdos824/LiZhuang)). Li and Zhuang's Theorem 1.3, following Pollack and Pomerance: if for every `0 < δ < 1/4` at least `y^(1−o(1))` primes `p ≤ 5y` have every prime factor of `p + 1` at most `y^δ`, then the bound holds. This is their Lean code, ported.
2. **Supply of primes with smooth successors** ([Erdos824/Succ](Erdos824/Succ)). Li and Zhuang's Theorem 1.4: the weighted-dilation-graph argument that gives primes `p` with `p − 1` smooth also gives primes `p = 2u − 1` with `p + 1 = 2u` smooth. The sign-free parts come from the author's [totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4/tree/dfce35707a67fce7362cb2bd95af8b80a0b0373e) formalization, included as [Erdos821](Erdos821); the sign-dependent modules are adapted under `Erdos824.Succ`.
3. **Assembly** ([Erdos824/Final.lean](Erdos824/Final.lean)) composes the two.

## Build and verify

Requirements: Git, and [elan](https://github.com/leanprover/elan) with `lake` on `PATH`. From the repository root:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook may exit with an error beginning `iut: Lake resolved an unexpected checkout at …` after it has resolved the dependencies; run the patch script next. It applies OpenAI's Lean 4.34.1 compatibility patches to the fetched packages and can be run again. `lake exe cache get` fetches compiled Mathlib; the other dependencies are compiled from source.

`scripts/verify.sh` builds the libraries and the challenge, compares the elaborated challenge and library statements and the definition of `h`, rejects forbidden constructs, and checks the theorem's axioms. An open proof shows up as `sorryAx` and makes it exit with status 2.

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- OpenAI's library [`openai/math`](https://github.com/openai/math) at `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (`lean/`), which fixes Mathlib and its other dependencies; all revisions are in [lake-manifest.json](lake-manifest.json).

See [THIRD_PARTY.md](THIRD_PARTY.md) for the included code and its licenses, and [LICENSE](LICENSE) for this repository's license (Apache-2.0).

The exported libraries contain 826 modules from `Erdos821` and 160 modules from `Erdos824`.
