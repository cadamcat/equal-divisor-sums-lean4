import Erdos824.Succ.Blueprint.TypeII
import Erdos824.Succ.S56.Determinant
import Erdos824.Succ.S56.DeterminantConverse
namespace Erdos824.Succ
theorem determinant_forward (m m' n e h h' k : ℤ)
    (hm : m * n + 1 = 2 * e * h) (hm' : m' * n + 1 = 2 * e * h')
    (he : e ≠ 0) (hk : m' - m = -2 * e * k) :
    h' - h = -k * n ∧ m * h' - m' * h = k :=
  Erdos824.Succ.S56.determinant_forward_of_increment m m' n e h h' k hm hm' he hk


theorem determinant_converse (m m' e h h' k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : m' - m = -2 * e * k) (hcross : m * h' - m' * h = k)
    (hcop : IsCoprime m k) :
    ∃ n : ℤ, 0 < n ∧ m * n + 1 = 2 * e * h ∧ m' * n + 1 = 2 * e * h' :=
  (Erdos824.Succ.S56.determinant_converse_unique m m' e h h' k
    hm he hh hdelta hcross hcop).exists



end Erdos824.Succ