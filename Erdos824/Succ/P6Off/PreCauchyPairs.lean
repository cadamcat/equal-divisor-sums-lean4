import Erdos824.Succ.P6Off.PreCauchyError
import Erdos821.S56.RoughDivisorBound

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos824.Succ.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos824.Succ.S56Core

def pairSum (U V : ℝ) (H alpha beta : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyad U, ∑ n ∈ dyad V,
    if Odd (m*n) ∧ 1 < m*n then H ((m*n + 1)/2)*alpha m*beta n else 0

theorem odd_shift_identity (v : ℕ) (hv : Odd v) (hv1 : 1 < v) :
    0 < (v + 1)/2 ∧ 2*((v + 1)/2) = v + 1 := by
  obtain ⟨k, hk⟩ := hv
  have hnum : v + 1 = 2 * (k + 1) := by omega
  have hquot : (v + 1) / 2 = k + 1 := by
    rw [hnum]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < (2 : ℕ))
  constructor
  · rw [hquot]
    omega
  · rw [hquot, hnum]

theorem shifted_gate (v e : ℕ) (he : 0 < e) :
    (1 < v ∧ 2*e ∣ v + 1) ↔ (Odd v ∧ 1 < v ∧ e ∣ (v + 1)/2) := by
  constructor
  · rintro ⟨hv, ⟨k, hk⟩⟩
    rw [mul_assoc] at hk
    have hEk : 0 < e*k := by omega
    have hvodd : Odd v := ⟨e*k-1, by omega⟩
    have hquot : (v+1)/2 = e*k := by
      rw [hk]
      exact Nat.mul_div_cancel_left _ (by norm_num : 0 < (2 : ℕ))
    exact ⟨hvodd, hv, k, by rw [hquot]⟩
  · rintro ⟨hvodd, hv, ⟨k, hk⟩⟩
    have hid := (odd_shift_identity v hvodd hv).2
    refine ⟨hv, k, ?_⟩
    calc
      v + 1 = 2 * ((v + 1) / 2) := hid.symm
      _ = 2 * (e*k) := by rw [hk]
      _ = (2*e)*k := by ring

theorem separatedSum_as_pairSum (emin E U V : ℝ) (ae ah alpha beta : ℕ → ℂ)
    (hepos : ∀ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊, 0 < e) :
    separatedSum emin E U V ae ah alpha beta =
      pairSum U V (fun u => ∑ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊,
        if e ∣ u then ae e*ah (u/e) else 0) alpha beta := by
  unfold separatedSum pairSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ho : Odd (m*n) ∧ 1 < m*n
  · rw [if_pos ho]
    apply Finset.sum_congr rfl
    intro e he
    have hep := hepos e he
    have hg := shifted_gate (m*n) e hep
    have hquot : ((m*n + 1)/2)/e = (m*n + 1)/(2*e) := Nat.div_div_eq_div_mul _ _ _
    by_cases hd : e ∣ (m*n + 1)/2
    · have hgate : 0 < e ∧ 1 < m*n ∧ 2*e ∣ m*n + 1 := ⟨hep, (hg.mpr ⟨ho.1, ho.2, hd⟩)⟩
      simp only [if_pos ho, if_pos hd, if_pos hgate, hquot]
      ring
    · have hgate : ¬(0 < e ∧ 1 < m*n ∧ 2*e ∣ m*n + 1) :=
        fun h => hd (hg.mp h.2).2.2
      simp only [ite_eq_right hgate, ite_eq_right hd, mul_zero, zero_mul]
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro e he
    have hg := shifted_gate (m*n) e (hepos e he)
    have hgate : ¬(0 < e ∧ 1 < m*n ∧ 2*e ∣ m*n + 1) :=
      fun h => ho ⟨(hg.mp h.2).1, h.2.1⟩
    simp [hgate]

theorem sum_shifted_rough_pairs_le (s t : Finset ℕ) (N : ℕ) (R : ℝ) (H : ℕ → ℝ)
    (hH : ∀ u, 0 ≤ H u) :
    (∑ m ∈ s, ∑ n ∈ t,
      if Odd (m*n) ∧ 1 < m*n ∧ rough R m ∧ (m*n + 1)/2 ≤ N then H ((m*n + 1)/2) else 0) ≤
    ∑ u ∈ Finset.Icc 1 N, (((2*u-1).divisors.filter (rough R)).card : ℝ)*H u := by
  let q := (s ×ˢ t).filter (fun p => Odd (p.1*p.2) ∧ 1 < p.1*p.2 ∧
    rough R p.1 ∧ (p.1*p.2+1)/2 ≤ N)
  have heq : (∑ m ∈ s, ∑ n ∈ t,
      if Odd (m*n) ∧ 1 < m*n ∧ rough R m ∧ (m*n + 1)/2 ≤ N then H ((m*n + 1)/2) else 0) =
      ∑ p ∈ q, H ((p.1*p.2+1)/2) := by
    simp only [q, Finset.sum_filter, Finset.sum_product]
  have hmap : ∀ p ∈ q, (p.1*p.2+1)/2 ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨_, ho, hv, hr, hn⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr (odd_shift_identity _ ho hv).1, hn⟩
  rw [heq, ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => (p.1*p.2+1)/2)
    hmap (fun p => H ((p.1*p.2+1)/2))]
  apply Finset.sum_le_sum
  intro u hu
  let fiber := q.filter (fun p => (p.1*p.2+1)/2 = u)
  have hproduct (p : ℕ × ℕ) (hp : p ∈ fiber) : p.1*p.2 + 1 = 2*u := by
    obtain ⟨hpq, hpu⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, ho, hv, _, _⟩ := Finset.mem_filter.mp hpq
    have hid := (odd_shift_identity _ ho hv).2
    rw [hpu] at hid
    exact hid.symm
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1) (↑fiber : Set (ℕ × ℕ)) := by
    intro p hp p' hp' h
    change p.1 = p'.1 at h
    have hprod := (hproduct p hp).trans (hproduct p' hp').symm
    have hpq := (Finset.mem_filter.mp hp).1
    obtain ⟨_, _, hlarge, _, _⟩ := Finset.mem_filter.mp hpq
    have hp1 : 0 < p.1 := by
      by_contra h
      have hp0 : p.1 = 0 := by omega
      rw [hp0] at hlarge
      omega
    apply Prod.ext h
    rw [← h] at hprod
    exact Nat.eq_of_mul_eq_mul_left hp1 (by omega)
  have hsub : fiber.image Prod.fst ⊆ (2*u-1).divisors.filter (rough R) := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hpq, _⟩ := Finset.mem_filter.mp hp
    have hr := (Finset.mem_filter.mp hpq).2.2.2.1
    have hprod : p.1*p.2 = 2*u-1 := by
      have hfactor := hproduct p hp
      have hu1 := (Finset.mem_Icc.mp hu).1
      omega
    have hdivisor_ne : 2*u-1 ≠ 0 := by
      have hu1 := (Finset.mem_Icc.mp hu).1
      omega
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hdivisor_ne⟩, hr⟩
    exact ⟨p.2, hprod.symm⟩
  have hcard : (fiber.card : ℝ) ≤ ((2*u-1).divisors.filter (rough R)).card := by
    exact_mod_cast (Finset.card_image_of_injOn hinj).symm.trans_le (Finset.card_le_card hsub)
  calc
    _ = (fiber.card : ℝ)*H u := by
      have hf : (∑ p ∈ fiber, H ((p.1*p.2+1)/2)) = ∑ _p ∈ fiber, H u := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      rw [hf]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hH u)


end Erdos824.Succ.P6Off
