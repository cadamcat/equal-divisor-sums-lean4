# Third-party code and mathematical sources

## Lean libraries

| Library | Revision | License | Use |
|---|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | fixed in [lake-manifest.json](lake-manifest.json) | Apache-2.0 | general mathematics |
| OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), `lean/` | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | Apache-2.0 | analytic number theory (Siegel–Walfisz, Bombieri–Vinogradov, the large sieve, sieve estimates) |

OpenAI's library pins Mathlib and its own dependencies; this project requires only OpenAI's library directly. Their licenses and notices remain with those packages.

The Lean source imports these OpenAI modules directly:

- `OAI.NumberTheory.EgyptianFractions.CorrelationPhase`
- `OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative`
- `OAI.NumberTheory.EgyptianFractions.DiscreteSecondDerivative`
- `OAI.NumberTheory.EgyptianFractions.ReciprocalDerivatives`
- `OAI.NumberTheory.EgyptianFractions.SecondDifference`
- `OAI.NumberTheory.PrimeGaps.AdditiveSieve`
- `OAI.NumberTheory.PrimeGaps.Main`
- `OAI.NumberTheory.PrimeGaps.MangoldtBounds`
- `OAI.NumberTheory.PrimeGaps.MultiplicativeSieve`
- `OAI.NumberTheory.PrimeGaps.OrthantIntegrals`
- `OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem`
- `OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare`

Other imported packages pinned by OpenAI's library:

The project imports `PrimeNumberTheoremAnd.Erdos970.MertensClassical` from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (commit `c39a751132c88b6e8080b74c74023fd95b3d8be0`, Apache-2.0) for Mertens' theorems; OpenAI's library pins this package.

Mathlib is pinned at commit `d13f23b723b8a846827a245b89c10fc7d3f11612` in [lake-manifest.json](lake-manifest.json). Its license and notices remain with the package.

## Code included in this repository

- **`Erdos824/LiZhuang/`** is ported from Shisheng Li and Zhong Zhuang's conditional formalization, [daizisheng/erdos-824](https://github.com/daizisheng/erdos-824) at commit `b4b7099bb8ab9c1c7fc61dae18a73cdbe503fe5a`, MIT license; the license text is in [Erdos824/LiZhuang/LICENSE](Erdos824/LiZhuang/LICENSE). The port moves the code to Lean v4.34.1 without the module system and renames the namespace to `Erdos824.LiZhuang`; each file names its source.
- **`Erdos821/`** is the formalization of the weighted-dilation-graph argument from [cadamcat/totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4/tree/dfce35707a67fce7362cb2bd95af8b80a0b0373e) (Erdős Problem 821) by the same author, Apache-2.0. The files under `Erdos824/Succ/` adapt its sign-dependent modules from `2u + 1` to `2u − 1`; they keep their module paths under the `Erdos824.Succ` prefix.
- **`Challenge.lean`** and `Erdos824/Challenge.lean` follow the statement of `Erdos824.erdos_824` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (`FormalConjectures/ErdosProblems/824.lean`, Apache-2.0).

## Mathematical sources

- Shisheng Li and Zhong Zhuang, *Coprime pairs with equal sum of divisors, assuming smooth shifted primes* (2026): Theorem 1.3 reduces the bound to a supply of primes `p` with `p + 1` smooth; Theorem 1.4 adapts the weighted-dilation-graph argument to that supply.
- OpenAI, *Weighted dilation graphs, smooth shifted primes and totient fibers* (2026): the supply of primes `p` with `p − 1` smooth.
- P. Pollack and C. Pomerance, *Some problems of Erdős on the sum-of-divisors function*, Trans. Amer. Math. Soc. Ser. B 3 (2016), Section 6.
