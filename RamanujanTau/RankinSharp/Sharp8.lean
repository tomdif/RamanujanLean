/-
# Milestone 1: every exponent `δ < 1/8`, directly for `D(s)`

With the convexity bound `‖E(s)‖ ≪ ‖s+3‖³` on `1/2 ≤ Re s ≤ 5/2` (`Efun_bound`, `σ_L = 1/2`)
the function `F(s) = D(s) − c₀/(s−1) = E(s)/((s−1)ζ(2s)) − c₀/(s−1)` of `RankinError.Landau3`
grows like `(1+|t|)²` on `σ₁ ≤ Re s ≤ 5/2` for every `σ₁ > 1/2` (`Ffun_bound2`). So the Riesz
mean of order `3` has saving `1 − σ₁`, and one third-order difference (`riesz_kdiff`) gives
`δ = (1 − σ₁)/4`, any `δ < 1/8` (`rankinSelberg_power_saving_lt_eighth`).

The abscissa hypothesis `D` absolutely convergent on `Re s > 1` comes from the bound
`∑_{n≤N} aₙ = O(N)` of `rankinSelberg_power_saving_84` (`abscissa_aTau_le_one`).
-/
import RamanujanTau.RankinSharp.Convex

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal

/-- `‖1/ζ(w)‖ ≤ Z` for `Re w ≥ σ > 1`. -/
lemma exists_norm_inv_zeta_le' {σ : ℝ} (hσ : 1 < σ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ w : ℂ, σ ≤ w.re → ‖(riemannZeta w)⁻¹‖ ≤ Z := by
  have hμ : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by simpa using hσ)
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℝ) : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun w hw => ?_⟩
  have hw1 : 1 < w.re := by linarith
  have := LSeries_one_mul_Lseries_moebius hw1
  rw [LSeries_one_eq_riemannZeta hw1] at this
  rw [inv_eq_of_mul_eq_one_right this]
  exact norm_LSeries_le hμ (by simpa using hw)

lemma norm_add_three_le {s : ℂ} (h1 : -3 ≤ s.re) (h2 : s.re ≤ 3) : ‖s + 3‖ ≤ 6 * (1 + |s.im|) := by
  have := Complex.norm_le_abs_re_add_abs_im (s + 3)
  simp only [add_re, re_ofNat, add_im, im_ofNat, add_zero] at this
  rw [abs_of_nonneg (by linarith)] at this
  linarith [abs_nonneg s.im]

section F

variable {a : ℕ → ℝ} {κ : ℝ} (d : RSData a κ)

lemma Ffun_eq_Efun {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Ffun d s = Efun d s / (s - 1) * (riemannZeta (2 * s))⁻¹ - (κ * rsConst : ℝ) / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [Ffun_eq d h0 h1, Efun_eq d h0 h1]
  unfold gfun Lam
  field_simp

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
/-- `‖D(s) − c₀/(s−1)‖ ≤ B (1+|t|)²` on `σ₁ ≤ Re s ≤ 5/2`, any `σ₁ > 1/2`. -/
theorem Ffun_bound2 {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) :
    ∃ B : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 5 / 2 → ‖Ffun d s‖ ≤ B * (1 + |s.im|) ^ 2 := by
  obtain ⟨B₀, hB₀⟩ := Efun_bound d habs (σL := 1 / 2) (n := 2) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_inv_zeta_le' (σ := 2 * σ₁) (by linarith)
  have hK : IsCompact (Icc σ₁ (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (Ffun d) (Icc σ₁ (5 / 2) ×ℂ Icc (-1 : ℝ) 1) := by
    refine (differentiableOn_Ffun d).continuousOn.mono ?_
    intro z hz; rw [mem_reProdIm] at hz; simp; linarith [hz.1.1]
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  set B : ℝ := |B₀| * 180 * Z + |κ * rsConst| + |C₂| with hB
  refine ⟨B, fun s h1 h2 => ?_⟩
  have hT : 1 ≤ (1 + |s.im|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  have hB0 : 0 ≤ |B₀| * 180 * Z + |κ * rsConst| := by positivity
  rcases le_or_gt |s.im| 1 with ht | ht
  · have := hC₂ s (by rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.1 ht⟩)
    calc ‖Ffun d s‖ ≤ |C₂| := this.trans (le_abs_self _)
      _ ≤ B * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · have hs0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hs1n : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
    have hs3 : ‖s + 3‖ ≤ 5 * ‖s - 1‖ := by
      have := norm_add_le (s - 1) 4
      rw [show s - 1 + 4 = s + 3 by ring, show ‖(4 : ℂ)‖ = 4 by simp] at this
      linarith
    have hs6 := norm_add_three_le (s := s) (by linarith) (by linarith)
    have hE := hB₀ s (by linarith) h2
    have hE' : ‖Efun d s‖ ≤ |B₀| * ‖s + 3‖ ^ 3 :=
      hE.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hz := hZ (2 * s) (by simp; linarith)
    have hq : ‖Efun d s‖ / ‖s - 1‖ ≤ |B₀| * 180 * (1 + |s.im|) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have h36 : ‖s + 3‖ ^ 2 ≤ 36 * (1 + |s.im|) ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hs6 2; nlinarith
      calc ‖Efun d s‖ ≤ |B₀| * (‖s + 3‖ ^ 2 * ‖s + 3‖) := by rw [← pow_succ]; exact hE'
        _ ≤ |B₀| * ((36 * (1 + |s.im|) ^ 2) * (5 * ‖s - 1‖)) := by gcongr
        _ = |B₀| * 180 * (1 + |s.im|) ^ 2 * ‖s - 1‖ := by ring
    rw [Ffun_eq_Efun d hs0 hs1]
    have e2 : ‖((κ * rsConst : ℝ) : ℂ) / (s - 1)‖ ≤ |κ * rsConst| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (abs_nonneg _) hs1n
    calc _ ≤ ‖Efun d s / (s - 1) * (riemannZeta (2 * s))⁻¹‖ +
          ‖((κ * rsConst : ℝ) : ℂ) / (s - 1)‖ := norm_sub_le _ _
      _ ≤ |B₀| * 180 * (1 + |s.im|) ^ 2 * Z + |κ * rsConst| := by
          rw [norm_mul, norm_div]; gcongr
      _ ≤ B * (1 + |s.im|) ^ 2 := by
          rw [hB]; nlinarith [abs_nonneg C₂, abs_nonneg (κ * rsConst)]

end F

/-- **Every `δ < 1/8`** from the Rankin–Selberg data and absolute convergence on `Re s > 1`. -/
theorem power_saving_lt_eighth_of_RSData (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (d : RSData a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 8) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConst * N| ≤ C * (N : ℝ) ^ (1 - δ) := by
  have hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    have h := LSeriesSummable_of_one_lt habs (s := ((5 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    have := h.norm
    refine this.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha0]
    · rw [if_neg h.ne', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
        Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]
  obtain ⟨B, hB⟩ := Ffun_bound2 d habs (σ₁ := 1 - 4 * δ) (by linarith)
  have hR := rieszAsymp_of_continuation a ha ha0 (K := 2) (c := 5 / 2) (σ₀ := 1 / 2)
    (σ₁ := 1 - 4 * δ) (c₀ := κ * rsConst) (B := B) (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) hsum (Ffun d) (differentiableOn_Ffun d)
    (fun s hs => LSeries_eq_Ffun d (by rw [hs]; norm_num)) hB
  have hc0 : 0 ≤ κ * rsConst := mul_nonneg hκ (by unfold rsConst; positivity)
  have hD := riesz_kdiff a ha hc0 3 (θ := 1 - (1 - 4 * δ)) (by linarith) (by linarith) hR
  obtain ⟨C, hC⟩ := partial_sum_of_riesz0 a hD
  refine ⟨C, fun N hN => ?_⟩
  have := hC N hN
  convert this using 3
  push_cast; ring

/-- `D(s) = ∑ τ(n)² n^{−s−11}` converges absolutely on `Re s > 1`, from
`∑_{n≤N} τ(n)²/n¹¹ = O(N)`. -/
lemma abscissa_aTau_le_one :
    LSeries.abscissaOfAbsConv (fun n => (aTau n : ℂ)) ≤ ((1 : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_84
  set c : ℝ := 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ)
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, aTau k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound (|c| + |C|) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := hC N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (N : ℝ) ^ (1 - 1 / 84 : ℝ) ≤ N := by
      calc (N : ℝ) ^ (1 - 1 / 84 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = N := Real.rpow_one _
    have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N, aTau k := Finset.sum_nonneg fun k _ => aTau_nonneg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS0, Real.rpow_one,
      abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have h1 := (abs_le.1 h).2
    have h2 : C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) ≤ |C| * N :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg C))
    have h3 : c * N ≤ |c| * N := mul_le_mul_of_nonneg_right (le_abs_self c) (Nat.cast_nonneg N)
    have e : ∑ k ∈ Finset.Icc 1 N, aTau k = ∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 :=
      rfl
    rw [e]
    linarith
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO aTau_nonneg (by norm_num) (by simpa using hy)

/-- **Rankin–Selberg with error `O(N^{1−δ})` for every `δ < 1/8`, unconditionally.** -/
theorem rankinSelberg_power_saving_lt_eighth {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 8) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := power_saving_lt_eighth_of_RSData aTau aTau_nonneg aTau_zero
    petNormSq_pos.le (rsData_of_unfold rsUnfold) abscissa_aTau_le_one hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : petNormSq * rsConst = 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) := by
    unfold rsConst
    have hπ := Real.pi_pos
    field_simp
  rw [e] at h
  exact h

end RamanujanTau.RankinSharp

#print axioms RamanujanTau.RankinSharp.rankinSelberg_power_saving_lt_eighth
