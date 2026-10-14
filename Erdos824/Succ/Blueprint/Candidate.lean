import Erdos821.Blueprint.Candidate

/-!
# P7 for the successor sign: prime mass, Type I remainder

The candidate data, geometry, bounds and weighted mass of the Erdős 821 formalization
(totient-fibers-lean4) do not involve `2u + 1` and are reused unchanged. Only the prime mass,
the Type I remainder and the Type I estimate change, from `2u + 1` to `2u - 1`. They are added to
the `CandidateData` namespace with a `succ` prefix so that dot notation (`C.succPrimeMass`) works
on the shared structure.
-/

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.CandidateData
open Analytic
variable (C : CandidateData)

/-- The weighted mass on `u` with `2u - 1` prime. -/
def succPrimeMass (x : ℝ) (jstar : ℕ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => Nat.Prime (2 * u - 1)), C.weighted x jstar u

/-- The Type I remainder for `d ∣ 2u - 1`. -/
def succRemainder (x : ℝ) (jstar d : ℕ) : ℝ :=
  (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1), C.weighted x jstar u) -
    C.mass x jstar / (Nat.totient d : ℝ)

/-- The Type I estimate for `2u - 1`. -/
def SuccTypeI : Prop :=
  ∀ θ D : ℝ, θ < 1 / 2 → 0 < D →
    ∀ jstar : ℕ, C.j₀ ≤ jstar → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |C.succRemainder x jstar d|) ≤
        K * (x * L x ^ (-D) + C.mass x jstar * L x ^ (-18 : ℝ))

end Erdos821.Blueprint.CandidateData

namespace Erdos824.Succ
open Erdos821.Blueprint

abbrev candidate_typeI_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (δ : ℝ) (C : CandidateData)
    (_hC : C.Geometry δ) (_hb : C.Bounds δ),
    C.SuccTypeI
end Erdos824.Succ
