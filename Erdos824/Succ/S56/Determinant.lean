import Mathlib

/-! Exact integer determinant identities for §5's Type II parametrization. -/

namespace Erdos824.Succ.S56

/-- The forward identities, with the architect's increment hypothesis. -/
theorem determinant_forward_of_increment (m m' n e h h' k : ℤ)
    (hm : m * n + 1 = 2 * e * h) (hm' : m' * n + 1 = 2 * e * h')
    (he : e ≠ 0) (hk : m' - m = -2 * e * k) :
    h' - h = -k * n ∧ m * h' - m' * h = k := by
  have hrel : (2 * e) * (h' - h) = (m' - m) * n := by
    nlinarith [hm, hm']
  have hc : (2 * e) * (h' - h + k * n) = 0 := by
    calc
      (2 * e) * (h' - h + k * n) = (2 * e) * (h' - h) + (2 * e) * k * n := by ring
      _ = (m' - m) * n + (2 * e) * k * n := by rw [hrel]
      _ = 0 := by rw [hk]; ring
  have he₂ : 2 * e ≠ 0 := mul_ne_zero (by norm_num) he
  have hd : h' - h = -k * n := by
    have hz := (mul_eq_zero.mp hc).resolve_left he₂
    linarith
  refine ⟨hd, ?_⟩
  calc
    m * h' - m' * h = m * (h' - h) - (m' - m) * h := by ring
    _ = m * (-k * n) - (-2 * e * k) * h := by rw [hd, hk]
    _ = k := by linear_combination -k * hm


end Erdos824.Succ.S56
