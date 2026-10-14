import Erdos824.Succ.P6Off.Driver
import Erdos824.Succ.P6Off.ReindexBridge
import Erdos824.Succ.P6Off.SeparationBridge
import Erdos824.Succ.P6Off.TailBridge
import Erdos824.Succ.P6Off.AbsoluteBridge
namespace Erdos824.Succ.P6Off

/-- The literal off-diagonal estimate, with all derivative data and K₀ fixed
before the discrepancy exponent. -/
theorem offDiagonalShiftTask_proof : OffDiagonalShiftTask :=
  offDiagonalShiftTask_of_tasks offDiagonalReindexTask_proof pulledCutoffSeparationTask_proof
    absoluteDeterminantDyadTask_proof endpointSquareTask_proof

example : Erdos824.Succ.S56Core.OffDiagonalShiftTask := offDiagonalShiftTask_proof


end Erdos824.Succ.P6Off
