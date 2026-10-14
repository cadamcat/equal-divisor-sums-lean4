import Erdos824.Main
import Erdos824.LiZhuang.Main

/-! The bridge from the successor supply to Li–Zhuang's conditional theorem. -/

namespace Erdos824

noncomputable section

/-- The two count the same pairs of coprime integers with equal divisor sums. -/
theorem liZhuang_h_eq : LiZhuang.h = h := by
  rfl

/-- The successor supply implies Li–Zhuang's weakened smooth-successor hypothesis. -/
theorem weak_of_supply : Succ.SmoothSuccessorSupply → LiZhuang.SmoothSuccessorHypWeak := by
  letI : DecidableLE ℝ := Real.decidableLE
  intro hsupply δ hδ hδ4 η hη
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 (hsupply δ hδ hδ4 η hη)
  refine ⟨y₀, fun y hy => ?_⟩
  have hcount := hy₀ y hy
  letI : DecidablePred (fun p : ℕ => p.Prime ∧
      ∀ q : ℕ, q ∈ (p + 1).primeFactors → (q : ℝ) ≤ y ^ δ) := by infer_instance
  have hsubset : Succ.smoothSuccessorPrimes δ y ⊆
      (Finset.Iic ⌊5 * y⌋₊).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q ∈ (p + 1).primeFactors → (q : ℝ) ≤ y ^ δ) := by
    intro p hp
    have hpParts := by
      classical
      exact Finset.mem_filter.mp hp
    rcases hpParts with ⟨hpI, hpProp⟩
    rcases hpProp with ⟨hpPrime, hpSmooth⟩
    have hpUpper : p ∈ Finset.Iic ⌊5 * y⌋₊ :=
      Finset.mem_Iic.mpr (Finset.mem_Ioc.mp hpI).2
    refine Finset.mem_filter.mpr ⟨hpUpper, hpPrime, ?_⟩
    intro q hq
    rcases (Nat.mem_primeFactors).mp hq with ⟨hqPrime, hqDvd, _⟩
    exact hpSmooth q hqPrime hqDvd
  have hcount' :
      ((Succ.smoothSuccessorPrimes δ y).card : ℝ) ≤
        (((Finset.Iic ⌊5 * y⌋₊).filter (fun p => p.Prime ∧
          ∀ q : ℕ, q ∈ (p + 1).primeFactors → (q : ℝ) ≤ y ^ δ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcount.trans hcount'

/-- The supply theorem follows from Li–Zhuang's conditional theorem. -/
theorem statement_of_supply_proof : Erdos824.statement_of_supply_statement := by
  intro hsupply ε hε
  obtain ⟨X, hX⟩ := LiZhuang.erdos824_of_smoothSuccessorWeak (weak_of_supply hsupply) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt X
  apply Filter.eventually_atTop.2
  refine ⟨N, ?_⟩
  intro x hx
  have hxReal : X ≤ (x : ℝ) := by
    exact le_of_lt (lt_of_lt_of_le hN (by exact_mod_cast hx))
  simpa only [liZhuang_h_eq] using hX x hxReal

end

end Erdos824
