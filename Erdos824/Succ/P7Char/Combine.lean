import Erdos824.Succ.P7Char.Main

/-! Combine the successor nonprincipal estimate with the sign-free principal correction. -/

noncomputable section

namespace Erdos824.Succ

open Erdos821.Blueprint

theorem candidate_typeI_proof : Erdos824.Succ.candidate_typeI_statement := by
  intro hc δ C hC hb
  exact Erdos824.Succ.P7B.candidate_typeI_of_nonprincipal_bounds hc C δ hb
    (Erdos824.Succ.P7Char.nonprincipalTypeITask_proof hc δ C hC hb)

example : Erdos824.Succ.candidate_typeI_statement := @candidate_typeI_proof

end Erdos824.Succ
