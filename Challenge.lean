import Mathlib

/-!
# Erdős Problem 824: the target statement

Mathlib definitions only. `h` and the statement follow Formal Conjectures'
`FormalConjectures/ErdosProblems/824.lean` (Apache-2.0), with `σ 1` written as
`ArithmeticFunction.sigma 1` and the answer `True`.
-/

namespace Erdos824

/-- The number of pairs `1 ≤ a < b < x` with `gcd(a, b) = 1` and `σ(a) = σ(b)`. -/
noncomputable def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter fun (a, b) ↦
    a < b ∧ a.Coprime b ∧ ArithmeticFunction.sigma 1 a = ArithmeticFunction.sigma 1 b).card

theorem erdos_824 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ) := by
  sorry

end Erdos824
