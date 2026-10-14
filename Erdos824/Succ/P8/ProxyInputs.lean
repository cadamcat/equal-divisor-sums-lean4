import Erdos821.P8Grid.ProxyInputs
import Erdos824.Succ.P8.RoughProxyDensity
import Erdos824.Succ.Blueprint.Proxy

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos824.Succ
open Erdos821.Blueprint

theorem proxy_inputs_proof : Erdos824.Succ.proxy_inputs_statement := by
  intro hc hs
  have hbase : Erdos821.Blueprint.ProxyInputs :=
    Erdos821.Blueprint.proxy_inputs_proof hc hs
  refine ⟨hbase.discrepancy, ?_, hbase.identities, hbase.products⟩
  refine ⟨hbase.densities.1, ?_⟩
  exact Erdos824.Succ.P8.rough_proxy_density_from_tasks hc hs
    Erdos821.P8Core.roughResidueIntervalTask_proof
    Erdos821.P8Core.roughCellDensityTask_proof

example : Erdos824.Succ.proxy_inputs_statement := @proxy_inputs_proof

end Erdos824.Succ

