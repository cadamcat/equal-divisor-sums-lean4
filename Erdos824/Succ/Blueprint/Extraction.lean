import Erdos824.Succ.Blueprint.Candidate
import Erdos824.Succ.Blueprint.TypeII
import Erdos824.Succ.Blueprint.Balanced
import Erdos824.Succ.Supply

/-!
# P10 for the successor sign: prime extraction and the count
-/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos824.Succ
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def PrimeExtraction (C : CandidateData) : Prop :=
  ∃ jstar : ℕ, C.j₀ ≤ jstar ∧ ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, c * C.mass x jstar / L x ≤ C.succPrimeMass x jstar

abbrev prime_extraction_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs)
    (_hii : TypeIIEstimate) (_hp : ProxyInputs) (δ : ℝ) (C : CandidateData)
    (_hC : C.Geometry δ) (_hb : C.Bounds δ) (_htI : C.SuccTypeI)
    (_hbal : BalancedRoughBound C),
    PrimeExtraction C
abbrev count_from_weighted_mass_statement : Prop :=
  ∀ (δ : ℝ) (hδ : 0 < δ) (C : CandidateData)
    (hb : C.Bounds δ) (hp : PrimeExtraction C),
    ∀ σ : ℝ, 0 < σ → ∀ᶠ x : ℝ in atTop,
      x ^ (1 - σ) ≤ ((smoothSuccessorPrimes δ x).card : ℝ)
end Erdos824.Succ
