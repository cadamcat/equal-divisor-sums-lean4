import Erdos824.Bridge
import Erdos824.Succ.Count.Count
import Erdos824.Succ.P8.ProxyInputs
import Erdos824.Succ.P7Char.Combine
import Erdos824.Succ.S9.FinalProof
import Erdos824.Succ.S10.Extraction
import Erdos824.Succ.S56.TypeIIProof
import Erdos821.P1.ClassicalInputs
import Erdos821.P7.Geometry
import Erdos821.P7.FinalBounds
import Erdos821.S34.IdealInputs
import Erdos821.Prelim.SieveInputsProof
import Erdos821.P3Final.Transference
import Erdos821.P3Rare.Proof
import Erdos821.P5.ShiftTwoTasks
import Erdos821.P5MinorAdapter.Proof
import Erdos821.P5MarkedEnergy.Main

/-!
# Erdős 824 assembled from the proved packages

The supply of primes with smooth successors is assembled from the sign-free packages of the Erdős 821
formalization and the sign-changed packages in `Erdos824.Succ`; the bridge to Li and Zhuang's
conditional theorem then gives `Erdos824.Statement`.
-/

namespace Erdos824.Final

open Erdos821.Blueprint

/-! Exact type checks for every package theorem used below. -/
example : Erdos821.Blueprint.sieve_inputs_statement := @Erdos821.Blueprint.sieve_inputs_proof
example : Erdos821.Blueprint.ideal_inputs_statement := @Erdos821.Blueprint.ideal_inputs_proof
example : Erdos821.Blueprint.candidate_geometry_statement :=
  @Erdos821.Blueprint.candidate_geometry_proof
example : Erdos821.Blueprint.candidate_bounds_statement :=
  @Erdos821.Blueprint.candidate_bounds_proof
example : Erdos824.Succ.proxy_inputs_statement := @Erdos824.Succ.proxy_inputs_proof
example : Erdos824.Succ.candidate_typeI_statement := @Erdos824.Succ.candidate_typeI_proof
example : Erdos824.Succ.count_from_weighted_mass_statement :=
  @Erdos824.Succ.count_from_weighted_mass_proof
example : Erdos824.Succ.balanced_rough_bound_statement :=
  @Erdos824.Succ.balanced_rough_bound_proof
example : Erdos824.Succ.prime_extraction_statement :=
  @Erdos824.Succ.prime_extraction_proof
example : Erdos824.statement_of_supply_statement := @Erdos824.statement_of_supply_proof
example : Erdos824.Succ.typeII_estimate_statement := @Erdos824.Succ.typeII_estimate_proof
example : Erdos821.Blueprint.transference_inputs_statement :=
  Erdos821.P3Final.transference_inputs_of_rare Erdos821.S2Core.MemoryRareTask_proof

/-- The package interfaces, each discharged by its proof. -/
theorem packageInterfaces : Erdos824.Succ.PackageInterfaces where
  classical := classical_inputs
  sieve := sieve_inputs_proof
  transference := Erdos821.P3Final.transference_inputs_of_rare Erdos821.S2Core.MemoryRareTask_proof
  ideal := ideal_inputs_proof
  shift := Erdos821.P5Core.shifted_cancellation_of_two_tasks
    Erdos821.P5Core.ComparisonMinorArcAdapterTask_proof
    Erdos821.P5Core.MarkedEndpointEnergyTask_proof
  typeII := Erdos824.Succ.typeII_estimate_proof
  proxies := Erdos824.Succ.proxy_inputs_proof
  candidateGeometry := fun δ hδ hδ' => candidate_geometry_proof classical_inputs δ hδ hδ'
  candidateBounds := candidate_bounds_proof classical_inputs
  candidateTypeI := Erdos824.Succ.candidate_typeI_proof classical_inputs
  balanced := Erdos824.Succ.balanced_rough_bound_proof classical_inputs
    (sieve_inputs_proof classical_inputs)
  extraction := Erdos824.Succ.prime_extraction_proof
  count := Erdos824.Succ.count_from_weighted_mass_proof

theorem supply : Erdos824.Succ.SmoothSuccessorSupply :=
  Erdos824.Succ.supply_of_package_interfaces packageInterfaces

/-- Erdős 824 from the proved packages. -/
theorem statement : Erdos824.Statement :=
  Erdos824.statement_of_supply_proof supply

/-- Formal Conjectures' form, with the answer `True`. -/
theorem erdos_824 : True ↔ Erdos824.Statement :=
  ⟨fun _ => statement, fun _ => trivial⟩

end Erdos824.Final
