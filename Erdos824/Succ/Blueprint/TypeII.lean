import Erdos821.Blueprint.TypeII

/-!
# P6 for the successor sign: the Type II sum over `mn = 2u - 1`
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos824.Succ
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The Type II sum with `u = (mn + 1) / 2`, i.e. `mn = 2u - 1`. -/
def typeIISum (D : BandData) (x : ℝ) (jstar : ℕ) (U V : ℝ)
    (psi : ℝ → ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ico ⌈U⌉₊ ⌈2 * U⌉₊, ∑ n ∈ Finset.Ico ⌈V⌉₊ ⌈2 * V⌉₊,
    if Odd (m * n) ∧ 1 < m * n then
      (D.weight x jstar ((m * n + 1) / 2) * psi (((m * n + 1) / 2 : ℕ) / x) : ℝ) * a m * b n
    else 0

/-- The Type II estimate for `typeIISum`; otherwise identical to the Erdős 821
formalization's. -/
def TypeIIEstimate : Prop :=
  ∀ D : BandData, D.Valid → ∀ Dsave bstar C : ℝ,
    0 < Dsave → 0 < bstar → 0 < C → ∀ jstar : ℕ,
      D.c₂ * D.s' / D.ratio ^ jstar < bstar / 4 →
      ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi →
        Function.support psi ⊆ Set.Icc 1 2 →
        ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
          ∀ (U V : ℝ) (a b : ℕ → ℂ),
            x / 8 ≤ U * V → U * V ≤ 8 * x →
            x ^ bstar ≤ U → U ≤ x ^ (1 - bstar) →
            x ^ bstar ≤ V → V ≤ x ^ (1 - bstar) →
            (∀ n, ‖a n‖ ≤ L x ^ C ∧ ‖b n‖ ≤ L x ^ C) →
            (∀ n, a n ≠ 0 → rough (W x) n) →
            discrepancy x B (restricted U a) →
            ‖typeIISum D x jstar U V psi a b‖ ≤ K * x * L x ^ (-Dsave)

abbrev typeII_estimate_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hshift : ShiftEstimate),
    TypeIIEstimate
end Erdos824.Succ
