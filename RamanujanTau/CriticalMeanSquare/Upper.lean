/-
# Mean square of `L(Δ, 6+it)` on the critical line: upper bound `≪ T log T`

**Theorem** (`dyadic_upper`). There is `C` such that for all `T ≥ 1`

    ∫_T^{2T} |L(Δ, 6+it)|² dt ≤ C · T · (1 + log T).

Proof: the Hecke–Hafner Plancherel route of `HardyCountHafner.MeanSquare`, at `x = 0`.
With `β = π/2 − 1/T`, `c = cos β`, `F(t) = Λ(6+it)e^{βt} = ∫ Φ_6(−2πξ+iβ) e^{−2πiξt} dξ`.
The new input is the evenness `Φ_6(−w) = Φ_6(w)` (from `Λ(12−s) = Λ(s)`), which gives
both `|Φ_6(u+iβ)| ≤ 2πMc^{−6} e^{−πce^{u}}` and `≤ 2πMc^{−6} e^{−πce^{−u}}`.  Hence the
majorant `2πMc^{−6} (1_{|u| ≤ log(1/c)} + 3/(1+(u+log c)²) + 3/(1+(u−log c)²))`, with sup
`≤ 7·2πMc^{−6}` and integral `≍ c^{−6} log(1/c)`; the Schur test and Stirling from below
then give `T^{12} log T / T^{11}`.
-/
import RamanujanTau.HardyCountHafner.MeanSquare

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquare

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
  RamanujanTau.HardyCountLinear RamanujanTau.HardyCountHafner
open scoped Real FourierTransform

/-- `Λ(6−it) = Λ(6+it)`. -/
lemma Zs_six_neg (t : ℝ) : Zs 6 (-t) = Zs 6 t := by
  unfold Zs
  rw [← heckeLambda_functional_equation (((6 : ℝ) : ℂ) + t * I)]
  congr 1; push_cast; ring

/-- `Φ_6` is even. -/
lemma Phis_six_neg (w : ℂ) : Phis 6 (-w) = Phis 6 w := by
  unfold Phis
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [Zs_six_neg]
  congr 1; push_cast; ring_nf

/-- Both cusp bounds for `Φ_6` on the line `Im w = β`. -/
lemma norm_gS_six_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p : ℍ, ‖Δf p‖ * p.im ^ 6 * Real.exp (π * p.im) ≤ M)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) (ξ : ℝ) :
    ‖gS 6 β ξ‖ ≤ 2 * π * (M / Real.cos β ^ 6) *
      min (Real.exp (-(π * Real.cos β * Real.exp (-2 * π * ξ))))
        (Real.exp (-(π * Real.cos β * Real.exp (2 * π * ξ)))) := by
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have hβabs' : |-β| < π / 2 := by rw [abs_neg]; exact hβabs
  have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hs1 : (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hs2 : (((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) ∈ strip := by
    show |(((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I).im| < π / 2; simpa using hβabs
  have hK0 : 0 ≤ 2 * π * (M / Real.cos β ^ 6) := by
    have := Real.cos_pos_of_mem_Ioo (x := β) ⟨by linarith [Real.pi_pos], hβ⟩
    positivity
  rw [mul_min_of_nonneg _ _ hK0]
  refine le_min ?_ ?_
  · rw [gS, Phis_eq_strip (le_refl 6) (by norm_num) hs1, norm_mul, h2π]
    have hG := norm_Gs_le hM 6 (u := -2 * π * ξ) hβabs
    rw [sub_self, zero_mul, Real.exp_zero, one_mul] at hG
    have : 2 * π * ‖Gs 6 (((-2 * π * ξ : ℝ) : ℂ) + β * I)‖ ≤
        2 * π * (M / Real.cos β ^ 6 * Real.exp (-(π * Real.cos β * Real.exp (-2 * π * ξ)))) := by
      gcongr
    linarith
  · have e : (((-2 * π * ξ : ℝ) : ℂ) + β * I) =
        -(((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) := by push_cast; ring
    rw [gS, e, Phis_six_neg, Phis_eq_strip (le_refl 6) (by norm_num) hs2, norm_mul, h2π]
    have hG := norm_Gs_le hM 6 (u := 2 * π * ξ) hβabs'
    rw [sub_self, zero_mul, Real.exp_zero, one_mul, Real.cos_neg] at hG
    have : 2 * π * ‖Gs 6 (((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I)‖ ≤
        2 * π * (M / Real.cos β ^ 6 * Real.exp (-(π * Real.cos β * Real.exp (2 * π * ξ)))) := by
      gcongr
    linarith

/-- Past the turning point: `e^{−πce^u} ≤ 3/(1+(u+log c)²)` when `u + log c ≥ 0`. -/
lemma exp_tail_le {c : ℝ} (hc : 0 < c) {u : ℝ} (h : 0 ≤ u + Real.log c) :
    Real.exp (-(π * c * Real.exp u)) ≤ 3 * (1 + (u + Real.log c) ^ 2)⁻¹ := by
  set w := u + Real.log c with hw
  have hce : c * Real.exp u = Real.exp w := by
    rw [hw, Real.exp_add, Real.exp_log hc]; ring
  have h1 : w ≤ π * c * Real.exp u := by
    rw [mul_assoc, hce]
    have := Real.add_one_le_exp w
    have := Real.exp_pos w
    nlinarith [Real.pi_gt_three]
  exact (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_le_three_div h)

/-- The middle interval `|u| ≤ log(1/c)`, in the variable `ξ = −u/(2π)`. -/
noncomputable def midI (c : ℝ) : Set ℝ := Icc (Real.log c / (2 * π)) (-Real.log c / (2 * π))

/-- The majorant (without the factor `2πM c^{−6}`). -/
noncomputable def maj (c ξ : ℝ) : ℝ :=
  (midI c).indicator (fun _ => (1 : ℝ)) ξ + 3 * (1 + (1 * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹ +
    3 * (1 + (1 * (-2 * π * ξ + -Real.log c)) ^ 2)⁻¹

lemma integrable_maj (c : ℝ) : Integrable (maj c) := by
  have h1 : Integrable ((midI c).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  exact (h1.add ((integrable_lorentz one_pos _).const_mul 3)).add
    ((integrable_lorentz one_pos _).const_mul 3)

lemma integral_maj {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ ξ, maj c ξ = -Real.log c / π + 3 := by
  have hl : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
  have h1 : Integrable ((midI c).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hL := fun a => (integrable_lorentz one_pos a).const_mul 3
  unfold maj
  rw [integral_add (f := fun ξ => (midI c).indicator (fun _ : ℝ => (1 : ℝ)) ξ +
      3 * (1 + (1 * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹)
      (g := fun ξ => 3 * (1 + (1 * (-2 * π * ξ + -Real.log c)) ^ 2)⁻¹) (h1.add (hL _)) (hL _),
    integral_add (f := (midI c).indicator (fun _ : ℝ => (1 : ℝ)))
      (g := fun ξ => 3 * (1 + (1 * (-2 * π * ξ + Real.log c)) ^ 2)⁻¹) h1 (hL _),
    integral_const_mul,
    integral_const_mul, integral_lorentz one_pos, integral_lorentz one_pos,
    midI, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le (by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith)]
  field_simp; ring

lemma maj_le_seven (c ξ : ℝ) : maj c ξ ≤ 7 := by
  unfold maj
  have h1 : (midI c).indicator (fun _ : ℝ => (1 : ℝ)) ξ ≤ 1 := by
    by_cases h : ξ ∈ midI c
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]; norm_num
  have h2 : ∀ a : ℝ, (1 + a ^ 2)⁻¹ ≤ 1 := fun a =>
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg a])
  linarith [h2 (1 * (-2 * π * ξ + Real.log c)), h2 (1 * (-2 * π * ξ + -Real.log c))]

lemma min_le_maj {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    min (Real.exp (-(π * c * Real.exp (-2 * π * ξ))))
      (Real.exp (-(π * c * Real.exp (2 * π * ξ)))) ≤ maj c ξ := by
  have hi0 : 0 ≤ (midI c).indicator (fun _ : ℝ => (1 : ℝ)) ξ :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  have hl0 : ∀ a : ℝ, 0 ≤ 3 * (1 + a ^ 2)⁻¹ := fun a => by positivity
  unfold maj
  rw [one_mul, one_mul]
  by_cases hA : 0 ≤ -2 * π * ξ + Real.log c
  · have := exp_tail_le hc hA
    have := hl0 (-2 * π * ξ + -Real.log c)
    have := min_le_left (Real.exp (-(π * c * Real.exp (-2 * π * ξ))))
      (Real.exp (-(π * c * Real.exp (2 * π * ξ))))
    linarith
  by_cases hB : 0 ≤ 2 * π * ξ + Real.log c
  · have h := exp_tail_le hc hB
    have e : (2 * π * ξ + Real.log c) ^ 2 = (-2 * π * ξ + -Real.log c) ^ 2 := by ring
    rw [e] at h
    have := hl0 (-2 * π * ξ + Real.log c)
    have := min_le_right (Real.exp (-(π * c * Real.exp (-2 * π * ξ))))
      (Real.exp (-(π * c * Real.exp (2 * π * ξ))))
    linarith
  · push Not at hA hB
    have hπ := Real.pi_pos
    have hmem : ξ ∈ midI c := by
      unfold midI
      constructor
      · rw [div_le_iff₀ (by positivity)]; linarith
      · rw [le_div_iff₀ (by positivity)]; linarith
    rw [indicator_of_mem hmem]
    have h1 : Real.exp (-(π * c * Real.exp (-2 * π * ξ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_pos (mul_pos hπ hc) (Real.exp_pos (-2 * π * ξ)); linarith
    have := min_le_left (Real.exp (-(π * c * Real.exp (-2 * π * ξ))))
      (Real.exp (-(π * c * Real.exp (2 * π * ξ))))
    linarith [hl0 (-2 * π * ξ + Real.log c), hl0 (-2 * π * ξ + -Real.log c)]

/-- **Mean square of `F(t) = Λ(6+it)e^{βt}`** on `[T, 2T]`. -/
theorem mean_sq_Fs_six : ∃ M : ℝ, 0 ≤ M ∧ ∀ β : ℝ, 0 ≤ β → β < π / 2 →
    ∀ T : ℝ, 0 < T → ∫ t in Icc T (2 * T), ‖Fs 6 β t‖ ^ 2 ≤
      14 * (2 * π * M / Real.cos β ^ 6) ^ 2 * (-Real.log (Real.cos β) / π + 3) := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  refine ⟨M, hM0, fun β hβ0 hβ T hT => ?_⟩
  set c : ℝ := Real.cos β with hcdef
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hc1 : c ≤ 1 := Real.cos_le_one β
  set A : ℝ := 2 * π * M / c ^ 6 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set k : ℝ → ℝ := fun ξ => A * maj c ξ with hk
  have hki : Integrable k := (integrable_maj c).const_mul A
  have hkK : ∀ ξ, k ξ ≤ 7 * A := fun ξ => by
    have := maj_le_seven c ξ
    show A * maj c ξ ≤ 7 * A
    nlinarith
  have hkint : ∫ ξ, k ξ = A * (-Real.log c / π + 3) := by
    rw [hk, integral_const_mul, integral_maj hc0 hc1]
  have hstrip : ∀ ξ : ℝ, (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    intro ξ
    have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
    show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hgb : ∀ ξ, ‖gS 6 β ξ‖ ≤ k ξ := by
    intro ξ
    refine (norm_gS_six_le hM0 hM hβ0 hβ ξ).trans ?_
    rw [← hcdef]
    have := min_le_maj hc0 ξ
    show 2 * π * (M / c ^ 6) * _ ≤ A * maj c ξ
    rw [hA, mul_div_assoc]
    gcongr
  have hgc : Continuous (gS 6 β) := by
    unfold gS
    exact (differentiableOn_Phis (le_refl 6) (by norm_num)).continuousOn.comp_continuous
      (by fun_prop) hstrip
  have hgi : Integrable (gS 6 β) := hki.mono' hgc.aestronglyMeasurable (Eventually.of_forall hgb)
  have hFeq : ∀ t, Fs 6 β t = fI (gS 6 β) t := Fs_eq_fI (le_refl 6) (by norm_num) hβ0 hβ hgi
  have hmain := integral_tri_norm_fI_sq_le_gen hgc hki hgb hkK hT.le (3 * T / 2)
  rw [hkint] at hmain
  have hsq : ∀ t, ‖fI (gS 6 β) t‖ ^ 2 = ‖Fs 6 β t‖ ^ 2 := fun t => by rw [hFeq]
  simp only [hsq] at hmain
  set B : ℝ := ∫ ξ, ‖gS 6 β ξ‖ with hB
  have hBd : ∀ t, ‖Fs 6 β t‖ ≤ B := fun t => by rw [hFeq]; exact norm_fI_le t
  have hFc : Continuous fun t => ‖Fs 6 β t‖ ^ 2 := ((continuous_Fs 6 β).norm.pow 2)
  have hWI : Integrable fun t => tri T (t - 3 * T / 2) * ‖Fs 6 β t‖ ^ 2 := by
    have h1 : Integrable fun t => tri T (t - 3 * T / 2) := (integrable_tri T).comp_sub_right _
    have h2 := h1.bdd_mul (f := fun t => ‖Fs 6 β t‖ ^ 2) (c := B ^ 2)
      hFc.aestronglyMeasurable (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hBd t) 2)
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  have hpt : ∀ t ∈ Icc T (2 * T), ‖Fs 6 β t‖ ^ 2 ≤
      2 / T * (tri T (t - 3 * T / 2) * ‖Fs 6 β t‖ ^ 2) := by
    intro t ht
    have habs : |t - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htri : T / 2 ≤ tri T (t - 3 * T / 2) := by
      rw [tri_of_abs_le (by linarith)]; linarith
    have hsq0 := sq_nonneg ‖Fs 6 β t‖
    rw [← mul_assoc]
    have : 1 ≤ 2 / T * tri T (t - 3 * T / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith
    nlinarith
  calc ∫ t in Icc T (2 * T), ‖Fs 6 β t‖ ^ 2
      ≤ ∫ t in Icc T (2 * T), 2 / T * (tri T (t - 3 * T / 2) * ‖Fs 6 β t‖ ^ 2) :=
        setIntegral_mono_on (hFc.integrableOn_Icc) (hWI.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ t, 2 / T * (tri T (t - 3 * T / 2) * ‖Fs 6 β t‖ ^ 2) :=
        setIntegral_le_integral (hWI.const_mul _) (Eventually.of_forall fun t =>
          mul_nonneg (by positivity) (mul_nonneg (tri_nonneg _ _) (sq_nonneg _)))
    _ = 2 / T * ∫ t, tri T (t - 3 * T / 2) * ‖Fs 6 β t‖ ^ 2 := integral_const_mul _ _
    _ ≤ 2 / T * (7 * A * (A * (-Real.log c / π + 3)) * T) := by gcongr
    _ = 14 * A ^ 2 * (-Real.log c / π + 3) := by field_simp; ring

/-- **Critical-line mean square, dyadic upper bound**:
`∫_T^{2T} |L(Δ,6+it)|² ≤ C T (1 + log T)` for `T ≥ 1`. -/
theorem dyadic_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) := by
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Fs_six
  have hcH := cH_pos
  refine ⟨56 * (2 * π * M) ^ 2 * (π / 2) ^ 12 / cH ^ 2, by positivity, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  set β : ℝ := π / 2 - 1 / T with hβ
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith [Real.pi_gt_three]
  have hβπ : β < π / 2 := by rw [hβ]; linarith
  have hm := hmean β hβ0 hβπ T hTpos
  set c : ℝ := Real.cos β with hc
  have hcpos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβπ⟩
  have hcge : 2 / (π * T) ≤ c := by
    rw [hc, hβ, Real.cos_pi_div_two_sub]
    have := Real.mul_le_sin hinvpos.le (by linarith [Real.pi_gt_three])
    calc 2 / (π * T) = 2 / π * (1 / T) := by field_simp
      _ ≤ _ := this
  have hcinv : c⁻¹ ≤ π * T / 2 := by
    rw [inv_le_comm₀ hcpos (by positivity)]
    calc (π * T / 2)⁻¹ = 2 / (π * T) := by field_simp
      _ ≤ c := hcge
  set Q : ℝ := π * T / 2 with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith [Real.pi_gt_three]
  have hc6 : (c ^ 6)⁻¹ ≤ Q ^ 6 := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hcinv 6
  -- `−log c ≤ log Q ≤ 1 + log T`
  have hlogc : -Real.log c ≤ 1 + Real.log T := by
    have h1 : -Real.log c ≤ Real.log Q := by
      rw [← Real.log_inv]; exact Real.log_le_log (by positivity) hcinv
    have h2 : Real.log Q = Real.log (π / 2) + Real.log T := by
      rw [hQ, show π * T / 2 = (π / 2) * T by ring, Real.log_mul (by positivity) hTpos.ne']
    have h3 : Real.log (π / 2) ≤ 1 := by
      have := Real.add_one_le_exp (π / 2 - 1)
      have h4 : π / 2 ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        have : Real.exp 1 > 2.7 := by
          have := Real.exp_one_gt_d9; linarith
        linarith [Real.pi_lt_d2]
      calc Real.log (π / 2) ≤ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h4
        _ = 1 := Real.log_exp 1
    linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hfac : -Real.log c / π + 3 ≤ 4 * (1 + Real.log T) := by
    have hπ := Real.pi_gt_three
    have : -Real.log c / π ≤ 1 + Real.log T := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  set A : ℝ := 2 * π * M / c ^ 6 with hA
  have hAle : A ≤ 2 * π * M * Q ^ 6 := by
    rw [hA, div_eq_mul_inv]; gcongr
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  -- pointwise lower bound (Stirling)
  set P : ℝ := cH * (T ^ (11 / 2 : ℝ) * T ^ (0 : ℝ)) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have hpt : ∀ t ∈ Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ ‖Fs 6 β t‖ ^ 2 / P ^ 2 := by
    intro t ht
    have hl := Fs_lower (x := 0) le_rfl zero_le_one hT ht.1 ht.2
    rw [← hβ, ← hP, add_zero] at hl
    push_cast at hl
    rw [le_div_iff₀ (by positivity), ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) hl 2
  have hLc : Continuous fun t : ℝ => ‖tauL (6 + t * I)‖ ^ 2 :=
    ((tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2)
  have hFc : Continuous fun t => ‖Fs 6 β t‖ ^ 2 / P ^ 2 :=
    ((continuous_Fs _ _).norm.pow 2).div_const _
  have h1 : ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤
      (∫ t in Icc T (2 * T), ‖Fs 6 β t‖ ^ 2) / P ^ 2 := by
    rw [← integral_div]
    exact setIntegral_mono_on hLc.integrableOn_Icc hFc.integrableOn_Icc measurableSet_Icc hpt
  refine h1.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine hm.trans ?_
  have hT112 : (T ^ (11 / 2 : ℝ)) ^ 2 = T ^ 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]; norm_num
  have hP2 : P ^ 2 = cH ^ 2 * T ^ 11 := by
    rw [hP, Real.rpow_zero, mul_one, mul_pow, hT112]
  rw [hP2]
  have hA2 : A ^ 2 ≤ (2 * π * M * Q ^ 6) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
  have hQ12 : (2 * π * M * Q ^ 6) ^ 2 = (2 * π * M) ^ 2 * (π / 2) ^ 12 * T ^ 12 := by
    rw [hQ]; ring
  have hfac0 : 0 ≤ -Real.log c / π + 3 := by
    have : 0 ≤ -Real.log c := by
      have := Real.log_nonpos hcpos.le (Real.cos_le_one β); linarith
    positivity
  calc 14 * A ^ 2 * (-Real.log c / π + 3)
      ≤ 14 * ((2 * π * M) ^ 2 * (π / 2) ^ 12 * T ^ 12) * (4 * (1 + Real.log T)) := by
        rw [← hQ12]; gcongr
    _ = 56 * (2 * π * M) ^ 2 * (π / 2) ^ 12 / cH ^ 2 * T * (1 + Real.log T) *
          (cH ^ 2 * T ^ 11) := by field_simp; ring

end RamanujanTau.CriticalMeanSquare
