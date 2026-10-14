import Erdos824.Succ.S10.BalancedAssembly
import Erdos824.Succ.S10.ConditionalAssembly
import Erdos824.Succ.S10Sharp.TaskProof
import Erdos824.Succ.S10Bfac.Proof
import Erdos824.Succ.S10Cover.CompositeCoverage
import Erdos824.Succ.S10Brough.BalancedWindowRough
import Erdos824.Succ.S10Prime.Proof
import Erdos824.Succ.P10.UnbalancedMesh

noncomputable section
namespace Erdos824.Succ.P7Core
open Erdos821.Blueprint

/-- All but the unbalanced mesh task are supplied by concrete proofs. -/
theorem prime_extraction_of_remaining_tasks
    (hMesh : UnbalancedMeshTask) : Erdos824.Succ.prime_extraction_statement :=
  prime_extraction_of_tasks S10Sharp.SharpPresieveTask_proof hMesh
    S10Cover.CompositeCoverageTask_proof
    (balanced_composite_of_window_tasks S10Bfac.BalancedFactorCoverageTask_proof
      S10Brough.BalancedWindowRoughTask_proof BalancedWindowPrimeTask_proof)

example (hMesh : UnbalancedMeshTask) : Erdos824.Succ.prime_extraction_statement :=
  prime_extraction_of_remaining_tasks hMesh

end Erdos824.Succ.P7Core

namespace Erdos824.Succ

/-- Prime extraction with all six helper tasks supplied by concrete proofs. -/
theorem prime_extraction_proof : Erdos824.Succ.prime_extraction_statement :=
  P7Core.prime_extraction_of_remaining_tasks P7Core.UnbalancedMeshTask_proof

example : Erdos824.Succ.prime_extraction_statement := @prime_extraction_proof

end Erdos824.Succ
