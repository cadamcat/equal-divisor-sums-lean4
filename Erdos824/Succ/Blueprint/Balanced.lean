import Erdos824.Succ.Blueprint.Proxy

/-!
# P9 for the successor sign
-/

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos824.Succ
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The balanced rough sum with `u = (mn + 1) / 2`. -/
def balancedRoughSum (C : CandidateData) (x M N : ℝ) (jstar : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (rough (W x)),
    ∑ n ∈ (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (rough (W x)),
      if Odd (m * n) ∧ 1 < m * n then C.weighted x jstar ((m * n + 1) / 2) else 0

def BalancedRoughBound (C : CandidateData) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ jstar : ℕ, C.j₀ ≤ jstar →
    ∀ᶠ x : ℝ in atTop, ∀ M N : ℝ,
      x ^ (0.46 : ℝ) ≤ M → M ≤ x ^ (0.54 : ℝ) →
      x ^ (0.46 : ℝ) ≤ N → N ≤ x ^ (0.54 : ℝ) →
      balancedRoughSum C x M N jstar ≤ K * C.mass x jstar * sieveProduct (W x) ^ 2

abbrev balanced_rough_bound_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs)
    (δ : ℝ) (C : CandidateData) (_hC : C.Geometry δ) (_hb : C.Bounds δ),
    BalancedRoughBound C
end Erdos824.Succ
