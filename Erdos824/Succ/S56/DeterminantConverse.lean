import Mathlib

/-! Converse reconstruction for §6. Coprimality retains exact divisibility. -/

namespace Erdos824.Succ.S56

/-- A determinant representation reconstructs exactly one positive common factor.
The shift may be zero; the algebraic reconstruction does not need that restriction. -/
theorem determinant_converse_unique (m m' e h h' k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : m' - m = -2 * e * k) (hcross : m * h' - m' * h = k)
    (hcop : IsCoprime m k) :
    ∃! n : ℤ, 0 < n ∧ m * n + 1 = 2 * e * h ∧ m' * n + 1 = 2 * e * h' := by
  have hidentity : m * (h' - h) = -k * (2 * e * h - 1) := by
    linear_combination hcross + h * hdelta
  have hdiv : m ∣ 2 * e * h - 1 := by
    apply hcop.dvd_of_dvd_mul_left
    refine ⟨-(h' - h), ?_⟩
    linear_combination hidentity
  obtain ⟨n, hn⟩ := hdiv
  have hfirst : m * n + 1 = 2 * e * h := by linarith [hn]
  have hnpos : 0 < n := by
    by_contra hn0
    have hnonpos : m * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_gt hn0)
    have hprod : 0 < 2 * e * h - 1 := by nlinarith
    linarith
  have hincrement : h' - h = -k * n := by
    apply mul_left_cancel₀ hm.ne'
    rw [hidentity, hn]
    ring
  have hsecond : m' * n + 1 = 2 * e * h' := by
    linear_combination n * hdelta - (2 * e) * hincrement + hfirst
  refine ⟨n, ⟨hnpos, hfirst, hsecond⟩, ?_⟩
  intro n' hn'
  apply mul_left_cancel₀ hm.ne'
  have hmul : m * n' = m * n := by linarith [hn'.2.1, hfirst]
  exact hmul


end Erdos824.Succ.S56
