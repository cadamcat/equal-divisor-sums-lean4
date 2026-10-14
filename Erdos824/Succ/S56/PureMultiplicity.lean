import Erdos821.S56.MultiplicityTasks
import Erdos821.P6Slot.SlotMultiplicity

namespace Erdos824.Succ.S56Core
open Erdos821.S56Core

theorem pure_slot_multiplicity : PureSlotMultiplicityTask :=
  Erdos821.P6Slot.pureSlotMultiplicityTask_proof

example : PureSlotMultiplicityTask = Erdos821.P6Slot.PureSlotMultiplicityTask := rfl


end Erdos824.Succ.S56Core
