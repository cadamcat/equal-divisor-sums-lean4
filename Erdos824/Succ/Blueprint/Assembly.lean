import Erdos824.Succ.Blueprint.Extraction
import Erdos821.P1.ClassicalInputs

/-!
# The successor supply from the package interfaces

The packages of the Erdős 821 formalization, with the sign-bearing ones (P6 Type II, P7 Type I,
P8 densities, P9, P10 prime extraction) and the final count replaced by their `Erdos824.Succ` forks.
The glue proof has no placeholder.
-/

namespace Erdos824.Succ
open Erdos821.Blueprint

/-- Proof functions expose the dependency order without using placeholder proofs. -/
structure PackageInterfaces : Prop where
  classical : ClassicalInputs
  sieve : ClassicalInputs → SieveInputs
  transference : ClassicalInputs → TransferenceInputs
  ideal : ClassicalInputs → IdealInputs
  shift : ClassicalInputs → SieveInputs → TransferenceInputs → IdealInputs → ShiftEstimate
  typeII : ClassicalInputs → ShiftEstimate → Succ.TypeIIEstimate
  proxies : ClassicalInputs → SieveInputs → Succ.ProxyInputs
  candidateGeometry : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∃ C : CandidateData, C.Geometry δ
  candidateBounds : ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ
  candidateTypeI : ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ → C.SuccTypeI
  balanced : ∀ (δ : ℝ) (C : CandidateData),
    C.Geometry δ → C.Bounds δ → Succ.BalancedRoughBound C
  extraction : ClassicalInputs → SieveInputs → Succ.TypeIIEstimate → Succ.ProxyInputs →
    ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ → C.SuccTypeI →
      Succ.BalancedRoughBound C → Succ.PrimeExtraction C
  count : ∀ (δ : ℝ), 0 < δ → ∀ C : CandidateData, C.Bounds δ → Succ.PrimeExtraction C →
    ∀ σ : ℝ, 0 < σ → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (1 - σ) ≤ ((smoothSuccessorPrimes δ x).card : ℝ)

theorem supply_of_package_interfaces (h : PackageInterfaces) : SmoothSuccessorSupply := by
  have hc := h.classical
  have hs := h.sieve hc
  have ht := h.transference hc
  have hi := h.ideal hc
  have hshift := h.shift hc hs ht hi
  have hii := h.typeII hc hshift
  have hp := h.proxies hc hs
  intro δ hδ hδ'
  obtain ⟨C, hC⟩ := h.candidateGeometry δ hδ hδ'
  have hb := h.candidateBounds δ C hC
  have htypeI := h.candidateTypeI δ C hC hb
  have hbal := h.balanced δ C hC hb
  have hextract := h.extraction hc hs hii hp δ C hC hb htypeI hbal
  exact h.count δ hδ C hb hextract

end Erdos824.Succ
