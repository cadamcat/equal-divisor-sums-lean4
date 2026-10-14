import Erdos824.Succ.S56.TypeIISplitAssembly
import Erdos824.Succ.S56.BlueprintDeterminant
import Erdos824.Succ.P6Split.Basic
namespace Erdos824.Succ.S56Core

theorem slot_coefficient_split : SlotCoefficientSplitTask := by
  change Erdos824.Succ.P6Split.SlotCoefficientSplitTask
  exact Erdos824.Succ.P6Split.SlotCoefficientSplitTask_proof

end Erdos824.Succ.S56Core

namespace Erdos824.Succ
open Erdos821.Blueprint
/-- Section 5 Type II estimate, with shifted cancellation as its input. -/
theorem typeII_estimate_proof (hc : ClassicalInputs) (hshift : ShiftEstimate) :
    TypeIIEstimate :=
  S56Core.typeII_of_slot_split hc hshift S56Core.slot_coefficient_split

example : Erdos824.Succ.typeII_estimate_statement := @typeII_estimate_proof

end Erdos824.Succ
