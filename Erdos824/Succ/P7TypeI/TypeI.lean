import Erdos821.P7TypeI.TypeI
import Erdos824.Succ.Blueprint.Candidate

/-! Successor-sign principal correction and the final Type I combination.
The geometry, weight estimates, and non-coprime correction are reused from 677. -/

noncomputable section
open scoped BigOperators
open Filter
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P7B

namespace Erdos824.Succ.P7B

theorem coprime_of_dvd_two_mul_sub_one {d u : ℕ} (hu : 0 < u)
    (h : d ∣ 2 * u - 1) : Nat.Coprime u d := by
  apply Nat.coprime_of_dvd'
  intro p hp hpu hpd
  have hpN : p ∣ 2 * u - 1 := dvd_trans hpd h
  have hp2u : p ∣ 2 * u := hpu.mul_left 2
  have hdiff : 2 * u - (2 * u - 1) = 1 := by omega
  have hp1 : p ∣ 1 := by
    rw [← hdiff]
    exact Nat.dvd_sub hp2u hpN
  exact (hp.not_dvd_one hp1).elim

theorem candidate_remainder_principal_split (C : CandidateData) (x : ℝ)
    (jstar d : ℕ) :
    C.succRemainder x jstar d +
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) =
      (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
        C.weighted x jstar u) - coprimeMass C x jstar d / (Nat.totient d : ℝ) := by
  unfold CandidateData.succRemainder
  rw [Erdos821.P7B.candidate_mass_coprime_split]
  ring

theorem candidate_remainder_abs_le_nonprincipal_add_correction
    (C : CandidateData) (x : ℝ) (jstar d : ℕ)
    (hd : 0 < d) (hweight0 : ∀ u, 0 ≤ C.weighted x jstar u) :
    |C.succRemainder x jstar d| ≤
      |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
          C.weighted x jstar u) - coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
      nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
  have hsplit := candidate_remainder_principal_split C x jstar d
  have hphi : 0 < (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hnonneg : 0 ≤ nonCoprimeMass C x jstar d := by
    unfold nonCoprimeMass
    apply Finset.sum_nonneg
    intro u hu
    exact hweight0 u
  have hcorrection : 0 ≤ nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) :=
    div_nonneg hnonneg hphi.le
  have hrewrite : C.succRemainder x jstar d =
      (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
        C.weighted x jstar u) -
        coprimeMass C x jstar d / (Nat.totient d : ℝ) -
        nonCoprimeMass C x jstar d / (Nat.totient d : ℝ) := by
    linarith
  calc
    |C.succRemainder x jstar d| =
        |((∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
            C.weighted x jstar u) -
          coprimeMass C x jstar d / (Nat.totient d : ℝ)) -
          nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)| := by rw [hrewrite]
    _ ≤ |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
          C.weighted x jstar u) -
        coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
        |nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)| := abs_sub _ _
    _ = _ := by rw [abs_of_nonneg hcorrection]

theorem candidate_remainder_sum_bound_of_nonprincipal
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ)
    (hB : C.Bounds δ) (jstar : ℕ) (hjstar : C.j₀ ≤ jstar)
    (θ D : ℝ) (hθ : θ < 1 / 2) (_hD : 0 < D)
    (hNonprincipal : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
            C.weighted x jstar u) -
          coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
        K * (x * L x ^ (-D))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |C.succRemainder x jstar d|) ≤
        K * (x * L x ^ (-D) + C.mass x jstar * L x ^ (-18 : ℝ)) := by
  obtain ⟨Knp, hKnp, hnp⟩ := hNonprincipal
  have hB0 := hB
  have hB' := hB
  obtain ⟨KB, CA, cmin, cmax, hKB, hcmin, hcmax, hBounds⟩ := hB'
  by_cases hθpos : 0 < θ
  · have hθle : θ ≤ 1 := by linarith
    obtain ⟨Kp, hKp, hp⟩ :=
      Erdos821.P7B.candidate_nonCoprimeMass_oddSquarefree_sum_small
        hc C δ hB0 jstar hjstar θ hθpos hθle
    refine ⟨Knp + Kp, add_pos hKnp hKp, ?_⟩
    filter_upwards [hnp, hp, hBounds jstar hjstar,
      eventually_gt_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 2]
      with x hnpX hpX hBX hx hlog
    rcases hBX with ⟨_, _, _, hweight0, _, _⟩
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L x := by change 0 < Real.log x; linarith
    have hmass0 : 0 ≤ C.mass x jstar := by
      unfold CandidateData.mass
      apply Finset.sum_nonneg
      intro u hu
      exact hweight0 u
    have hterm1 : 0 ≤ x * L x ^ (-D) :=
      mul_nonneg hxpos.le (Real.rpow_nonneg hLpos.le _)
    have hterm2 : 0 ≤ C.mass x jstar * L x ^ (-18 : ℝ) :=
      mul_nonneg hmass0 (Real.rpow_nonneg hLpos.le _)
    have hpow : (L x ^ (18 : ℕ) : ℝ)⁻¹ = L x ^ (-18 : ℝ) := by
      rw [Real.rpow_neg hLpos.le]
      exact (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (L x) 18)).symm
    have hpX' :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) ≤
          Kp * C.mass x jstar * L x ^ (-18 : ℝ) := by
      calc
        _ ≤ Kp * C.mass x jstar * (L x ^ (18 : ℕ))⁻¹ := hpX
        _ = Kp * C.mass x jstar * L x ^ (-18 : ℝ) := by rw [hpow]
    have hsum :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |C.succRemainder x jstar d|) ≤
          (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
                C.weighted x jstar u) -
              coprimeMass C x jstar d / (Nat.totient d : ℝ)|) +
          (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) := by
      calc
        _ ≤ ∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
            (|(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
                C.weighted x jstar u) -
              coprimeMass C x jstar d / (Nat.totient d : ℝ)| +
              nonCoprimeMass C x jstar d / (Nat.totient d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdpos : 0 < d := by
            have hdi := (Finset.mem_filter.mp hd).1
            exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdi).1
          exact candidate_remainder_abs_le_nonprincipal_add_correction
            C x jstar d hdpos hweight0
        _ = _ := by rw [Finset.sum_add_distrib]
    have hbound :
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |C.succRemainder x jstar d|) ≤
          Knp * (x * L x ^ (-D)) +
            Kp * C.mass x jstar * L x ^ (-18 : ℝ) :=
      hsum.trans (add_le_add hnpX hpX')
    refine hbound.trans ?_
    nlinarith [mul_nonneg hKnp.le hterm2, mul_nonneg hKp.le hterm1]
  · have hθnonpos : θ ≤ 0 := le_of_not_gt hθpos
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [hBounds jstar hjstar, eventually_gt_atTop (2 : ℝ)] with x hBX hx
    rcases hBX with ⟨_, _, _, hweight0, _, _⟩
    have hxpos : 0 < x := by linarith
    have hxone : 1 < x := by linarith
    have hlog : 0 ≤ Real.log x := (Real.log_pos hxone).le
    have hθlog : Real.log x * θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlog hθnonpos
    have hpow : x ^ θ ≤ 1 := by
      rw [Real.rpow_def_of_pos hxpos]
      exact Real.exp_le_one_iff.mpr hθlog
    let S := (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d)
    have hsumzero : (∑ d ∈ S, |C.succRemainder x jstar d|) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdI := (Finset.mem_filter.mp hd).1
      have hdle : d ≤ ⌊x ^ θ⌋₊ := (Finset.mem_Icc.mp hdI).2
      have hdleR : (d : ℝ) ≤ 1 := by
        calc
          (d : ℝ) ≤ (⌊x ^ θ⌋₊ : ℝ) := by exact_mod_cast hdle
          _ ≤ x ^ θ := Nat.floor_le (Real.rpow_nonneg hxpos.le θ)
          _ ≤ 1 := hpow
      have hdge : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
      have hdleNat : d ≤ 1 := by exact_mod_cast hdleR
      have hdEq : d = 1 := by omega
      subst d
      have hrem : C.succRemainder x jstar 1 = 0 := by
        unfold CandidateData.succRemainder CandidateData.mass
        have hfilter :
            (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => 1 ∣ 2 * u - 1) =
              Finset.Icc 1 ⌊2 * x⌋₊ := by
          ext u
          simp
        rw [hfilter]
        simp [Nat.totient_one]
      rw [hrem]
      simp
    rw [hsumzero]
    have hLpos : 0 < L x := by change 0 < Real.log x; exact Real.log_pos hxone
    have hmass0 : 0 ≤ C.mass x jstar := by
      unfold CandidateData.mass
      apply Finset.sum_nonneg
      intro u hu
      exact hweight0 u
    have hterm1 : 0 ≤ x * L x ^ (-D) :=
      mul_nonneg hxpos.le (Real.rpow_nonneg hLpos.le _)
    have hterm2 : 0 ≤ C.mass x jstar * L x ^ (-18 : ℝ) :=
      mul_nonneg hmass0 (Real.rpow_nonneg hLpos.le _)
    positivity

theorem candidate_typeI_of_nonprincipal_bounds
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ) (hB : C.Bounds δ)
    (hNonprincipal : ∀ θ D : ℝ, θ < 1 / 2 → 0 < D →
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |(∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u - 1),
              C.weighted x jstar u) -
            coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
          K * (x * L x ^ (-D))) : C.SuccTypeI := by
  intro θ D hθ hD jstar hjstar
  exact candidate_remainder_sum_bound_of_nonprincipal hc C δ hB jstar hjstar
    θ D hθ hD (hNonprincipal θ D hθ hD jstar hjstar)

end Erdos824.Succ.P7B
