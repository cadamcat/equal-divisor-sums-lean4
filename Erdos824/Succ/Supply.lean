import Mathlib

/-!
# The smooth successor-prime supply

The successor form of Theorem 1.2 of the WD paper (Li–Zhuang, Theorem 1.4): for every fixed
`0 < δ < 1/4`, at least `x ^ (1 - o(1))` primes `p` with `2x - 2 < p ≤ 5x` have no prime factor of
`p + 1` above `x ^ δ`. The interval is that of Li–Zhuang's `SmoothSuccessorHyp`; the primes produced
are `p = 2u - 1` with `x ≤ u ≤ 2x`.
-/

namespace Erdos824.Succ

open Filter

open scoped Classical in
/-- The primes `p` with `⌊2x - 2⌋ < p ≤ ⌊5x⌋` all of whose prime factors of `p + 1` are at most
`x ^ δ`. -/
noncomputable def smoothSuccessorPrimes (δ x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊2 * x - 2⌋₊ ⌊5 * x⌋₊).filter fun p =>
    p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p + 1 → (q : ℝ) ≤ x ^ δ

/-- The successor supply, with `x ^ (1 - o(1))` written as: for every `σ > 0`, eventually at least
`x ^ (1 - σ)`. -/
def SmoothSuccessorSupply : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∀ σ : ℝ, 0 < σ →
    ∀ᶠ x : ℝ in atTop, x ^ (1 - σ) ≤ ((smoothSuccessorPrimes δ x).card : ℝ)

end Erdos824.Succ
