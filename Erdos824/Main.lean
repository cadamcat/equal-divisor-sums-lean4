import Erdos824.Challenge
import Erdos824.Succ.Blueprint.Assembly

/-! # Erdős 824 from the successor supply -/

namespace Erdos824

abbrev statement_of_supply_statement : Prop :=
  ∀ (_h : Succ.SmoothSuccessorSupply),
    Statement

end Erdos824
