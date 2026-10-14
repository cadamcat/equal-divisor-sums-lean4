import Mathlib

/-!
# Erdős Problem 824

Let `h x` count the pairs `1 ≤ a < b < x` with `gcd(a, b) = 1` and `σ(a) = σ(b)`. Then
`h x > x ^ (2 - ε)` for every `ε > 0` and all sufficiently large `x`.

`h` is Formal Conjectures' `Erdos824.h` (Apache-2.0), with `σ 1` written out as
`ArithmeticFunction.sigma 1`; `Statement` is the right-hand side of its `erdos_824`, whose answer is
`True`.
-/

namespace Erdos824

/-- The number of pairs `1 ≤ a < b < x` with `gcd(a, b) = 1` and `σ(a) = σ(b)`. -/
noncomputable def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter fun (a, b) ↦
    a < b ∧ a.Coprime b ∧ ArithmeticFunction.sigma 1 a = ArithmeticFunction.sigma 1 b).card

/-- Erdős 824: `h x > x ^ (2 - ε)` for every `ε > 0` and all large `x`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ)

end Erdos824
