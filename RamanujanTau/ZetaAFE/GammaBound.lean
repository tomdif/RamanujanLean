/-
# `R_t(z) = (t/2π)^z (1 + O(e^{y²/2}/t))` on the line `Re z = c`

`gamma_ratio_line`: for `1/2 < c ≤ 1` there is `K` with, for all `t ≥ 8` and real `y`,

    ‖R_t(c+iy) · e^{−(c+iy) log(t/2π)} − 1‖ ≤ K e^{y²/2} / t.

* `|y| ≤ t/4`: `R_t e^{−zℓ} = Q_t(z) e^{E_t(z)}` (`Rt_decomp`, Weierstrass `log Γ`), with
  `Q_t − 1 = (z²(2t²−1/2)+z⁴)/(1/4+t²)²` and `‖E_t‖ ≤ 200(1+|y|)²/t` (`norm_E_le`).
* `|y| > t/4`: crude bounds `|Γ(w)| ≤ Γ(Re w)` and the reflection lower bound for `|Γ(1/4 ± it/2)|`;
  the factor `e^{πt} ≤ e^{4π|y|}` and `1 ≤ 4|y|/t` are absorbed by `e^{y²/2}`.
-/
import RamanujanTau.ZetaAFE.Digamma
import RamanujanTau.RankinError.GammaBound

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZeroCountRvM

lemma gfac_exp {s : ℂ} (hs : 0 < s.re) :
    gfac s = s * (1 - s) * cexp (-(s / 2) * (Real.log Real.pi : ℂ) + LG (s / 2)) := by
  unfold gfac
  rw [Gammaℝ_def, Gamma_eq_exp_LG (by simpa using hs), Complex.exp_add,
    cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero), Complex.ofReal_log Real.pi_pos.le]
  ring_nf

/-- `Q_t(z) = s₊(1−s₊)s₋(1−s₋) / (same at z = 0)`. -/
noncomputable def Qr (t : ℝ) (z : ℂ) : ℂ :=
  (sp t z * (1 - sp t z) * (sm t z * (1 - sm t z))) / (sp t 0 * (1 - sp t 0) * (sm t 0 * (1 - sm t 0)))

lemma Q0_eq (t : ℝ) : sp t 0 * (1 - sp t 0) * (sm t 0 * (1 - sm t 0)) = (((1 / 4 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold sp sm; push_cast
  linear_combination (-(t : ℂ) ^ 2 * (2 * (1 / 4) - (t : ℂ) ^ 2 * I ^ 2 + (t : ℂ) ^ 2)) * I_sq

lemma Q0_ne (t : ℝ) : sp t 0 * (1 - sp t 0) * (sm t 0 * (1 - sm t 0)) ≠ 0 := by
  rw [Q0_eq]; exact_mod_cast (by positivity : (0:ℝ) < (1 / 4 + t ^ 2) ^ 2).ne'

lemma Qr_sub_one (t : ℝ) (z : ℂ) :
    Qr t z - 1 = (z ^ 2 * (2 * t ^ 2 - 1 / 2) + z ^ 4) / (((1 / 4 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold Qr
  rw [Q0_eq]
  have h : (((1 / 4 + t ^ 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0:ℝ) < (1 / 4 + t ^ 2) ^ 2).ne'
  rw [div_sub_one h]
  congr 1
  unfold sp sm; push_cast
  linear_combination (-(t : ℂ) ^ 2 * (2 * (1 / 4 - z ^ 2) - (t : ℂ) ^ 2 * I ^ 2 + (t : ℂ) ^ 2) -
    4 * (t : ℂ) ^ 2 * z ^ 2) * I_sq

lemma norm_Qr_sub_one_le {t : ℝ} (ht : 1 ≤ t) (z : ℂ) :
    ‖Qr t z - 1‖ ≤ (3 * ‖z‖ ^ 2 + ‖z‖ ^ 4) / t ^ 2 := by
  rw [Qr_sub_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have ht0 : 0 < t := by linarith
  have hnum : ‖z ^ 2 * (2 * t ^ 2 - 1 / 2) + z ^ 4‖ ≤ ‖z‖ ^ 2 * (3 * t ^ 2) + ‖z‖ ^ 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, norm_pow]
    have : ‖(2 * (t : ℂ) ^ 2 - 1 / 2)‖ ≤ 3 * t ^ 2 := by
      have h1 : (2 * (t : ℂ) ^ 2 - 1 / 2) = ((2 * t ^ 2 - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith)]; nlinarith
    have := sq_nonneg ‖z‖
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hz2 := sq_nonneg ‖z‖
  have hz4 : 0 ≤ ‖z‖ ^ 4 := by positivity
  have hA : t ^ 4 ≤ (1 / 4 + t ^ 2) ^ 2 := by nlinarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  calc ‖z ^ 2 * (2 * ↑t ^ 2 - 1 / 2) + z ^ 4‖ * t ^ 2
      ≤ (‖z‖ ^ 2 * (3 * t ^ 2) + ‖z‖ ^ 4) * t ^ 2 := by gcongr
    _ ≤ (3 * ‖z‖ ^ 2 + ‖z‖ ^ 4) * t ^ 4 := by
        have h24 : t ^ 2 ≤ t ^ 4 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h24 hz4]
    _ ≤ (3 * ‖z‖ ^ 2 + ‖z‖ ^ 4) * (1 / 4 + t ^ 2) ^ 2 := by gcongr

/-- `R_t(z) e^{−z log(t/2π)} = Q_t(z) e^{E_t(z)}`. -/
lemma Rt_decomp {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    Rt t z * cexp (-(z * (Real.log (t / (2 * Real.pi)) : ℂ))) = Qr t z * cexp (Efun t z) := by
  have hp : 0 < (sp t z).re := by simp [sp]; linarith
  have hm : 0 < (sm t z).re := by simp [sm]; linarith
  have hp0 : 0 < (sp t 0).re := by simp [sp]
  have hm0 : 0 < (sm t 0).re := by simp [sm]
  unfold Rt G0
  rw [gfac_exp hp, gfac_exp hm, gfac_exp hp0, gfac_exp hm0]
  unfold Qr Efun
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring, Real.log_div (by positivity) Real.pi_ne_zero]
  rw [hlog]
  have hQ := Q0_ne t
  have hE : ∀ a : ℂ, cexp a ≠ 0 := Complex.exp_ne_zero
  have e1 : sp t z * (1 - sp t z) * cexp (-(sp t z / 2) * (Real.log Real.pi : ℂ) + LG (sp t z / 2)) *
      (sm t z * (1 - sm t z) * cexp (-(sm t z / 2) * (Real.log Real.pi : ℂ) + LG (sm t z / 2))) =
      (sp t z * (1 - sp t z) * (sm t z * (1 - sm t z))) *
      cexp (-(sp t z / 2) * (Real.log Real.pi : ℂ) + LG (sp t z / 2) +
        (-(sm t z / 2) * (Real.log Real.pi : ℂ) + LG (sm t z / 2))) := by
    simp only [Complex.exp_add]; ring
  have e0 : sp t 0 * (1 - sp t 0) * cexp (-(sp t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sp t 0 / 2)) *
      (sm t 0 * (1 - sm t 0) * cexp (-(sm t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sm t 0 / 2))) =
      (sp t 0 * (1 - sp t 0) * (sm t 0 * (1 - sm t 0))) *
      cexp (-(sp t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sp t 0 / 2) +
        (-(sm t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sm t 0 / 2))) := by
    simp only [Complex.exp_add]; ring
  rw [e1, e0]
  have hexp : cexp (-(sp t z / 2) * (Real.log Real.pi : ℂ) + LG (sp t z / 2) +
        (-(sm t z / 2) * (Real.log Real.pi : ℂ) + LG (sm t z / 2))) *
      cexp (-(z * ((Real.log (t / 2) - Real.log Real.pi : ℝ) : ℂ))) =
      cexp (-(sp t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sp t 0 / 2) +
        (-(sm t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sm t 0 / 2))) *
      cexp (LG (aP t z) - LG (aP t 0) + LG (aM t z) - LG (aM t 0) - z * (Real.log (t / 2) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    unfold aP aM sp sm; push_cast; ring
  have hX0 : cexp (-(sp t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sp t 0 / 2) +
        (-(sm t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sm t 0 / 2))) ≠ 0 := Complex.exp_ne_zero _
  set Xz := cexp (-(sp t z / 2) * (Real.log Real.pi : ℂ) + LG (sp t z / 2) +
        (-(sm t z / 2) * (Real.log Real.pi : ℂ) + LG (sm t z / 2))) with hXz
  set X0 := cexp (-(sp t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sp t 0 / 2) +
        (-(sm t 0 / 2) * (Real.log Real.pi : ℂ) + LG (sm t 0 / 2))) with hX0d
  set Y := cexp (-(z * ((Real.log (t / 2) - Real.log Real.pi : ℝ) : ℂ))) with hY
  set cE := cexp (LG (aP t z) - LG (aP t 0) + LG (aM t z) - LG (aM t 0) - z * (Real.log (t / 2) : ℂ))
    with hcE
  set Nz := sp t z * (1 - sp t z) * (sm t z * (1 - sm t z)) with hNz
  set N0 := sp t 0 * (1 - sp t 0) * (sm t 0 * (1 - sm t 0)) with hN0
  calc Nz * Xz / (N0 * X0) * Y = Nz * (Xz * Y) / (N0 * X0) := by ring
    _ = Nz * (X0 * cE) / (N0 * X0) := by rw [hexp]
    _ = Nz / N0 * cE := by field_simp

/-- Region `|y| ≤ t/4`. -/
theorem gamma_ratio_near {t c y : ℝ} (ht : 8 ≤ t) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hy : |y| ≤ t / 4) :
    ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (Real.log (t / (2 * Real.pi)) : ℂ))) - 1‖ ≤
      204 * Real.exp 100 * ((1 + |y|) ^ 4 * Real.exp (100 * |y|)) / t := by
  have ht0 : 0 < t := by linarith
  set z : ℂ := (c : ℂ) + y * I with hz
  rw [Rt_decomp ht0 (by simp [hz, hc])]
  have hzn : ‖z‖ ≤ 1 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    simp [hz, abs_of_nonneg hc]; linarith
  have hE := norm_E_le ht hc hc1 hy
  rw [← hz] at hE
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hEs : ‖Efun t z‖ ≤ 100 * (1 + |y|) := by
    refine hE.trans ?_
    rw [div_le_iff₀ ht0]
    have : (1 + |y|) ≤ t / 2 := by linarith
    nlinarith
  have hQ := norm_Qr_sub_one_le (by linarith : (1:ℝ) ≤ t) z
  have hQ' : ‖Qr t z - 1‖ ≤ 4 * (1 + |y|) ^ 4 / t := by
    refine hQ.trans ?_
    have h2 : ‖z‖ ^ 2 ≤ (1 + |y|) ^ 4 := by
      calc ‖z‖ ^ 2 ≤ (1 + |y|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
        _ ≤ (1 + |y|) ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
    have h4 : ‖z‖ ^ 4 ≤ (1 + |y|) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hzn 4
    rw [div_le_div_iff₀ (by positivity) ht0]
    have : t ≤ t ^ 2 := by nlinarith
    have h0 : 0 ≤ 3 * ‖z‖ ^ 2 + ‖z‖ ^ 4 := by positivity
    nlinarith
  have hexpE : ‖cexp (Efun t z)‖ ≤ Real.exp (100 * (1 + |y|)) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hEs)
  have hsub : ‖cexp (Efun t z) - 1‖ ≤ ‖Efun t z‖ * Real.exp (100 * (1 + |y|)) := by
    have := Complex.norm_exp_sub_sum_le_norm_mul_exp (Efun t z) 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one] at this
    exact this.trans (by gcongr)
  have heq : Qr t z * cexp (Efun t z) - 1 = (Qr t z - 1) * cexp (Efun t z) + (cexp (Efun t z) - 1) := by
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hEt : ‖Efun t z‖ ≤ 200 * (1 + |y|) ^ 4 / t := by
    exact hE.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hy1 (by norm_num)) (by norm_num)) ht0.le)
  have hexp100 : Real.exp (100 * (1 + |y|)) = Real.exp 100 * Real.exp (100 * |y|) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Qr t z - 1‖ * ‖cexp (Efun t z)‖ + ‖cexp (Efun t z) - 1‖
      ≤ 4 * (1 + |y|) ^ 4 / t * Real.exp (100 * (1 + |y|)) +
        200 * (1 + |y|) ^ 4 / t * Real.exp (100 * (1 + |y|)) := by
        gcongr
        exact hsub.trans (by gcongr)
    _ = _ := by rw [hexp100]; ring

lemma norm_gfac_le {s : ℂ} (hs : 0 < s.re) :
    ‖gfac s‖ ≤ (1 + ‖s‖) ^ 2 * Real.Gamma (s.re / 2) := by
  unfold gfac
  rw [norm_mul, norm_mul, Gammaℝ_def, norm_mul,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : ‖1 - s‖ ≤ 1 + ‖s‖ := (norm_sub_le _ _).trans (by simp)
  have h2 : Real.pi ^ (-s / 2).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith
  have h3 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have := RankinError.norm_Gamma_le_Gamma_re (w := s / 2) (by simp; linarith)
    simpa using this
  have hG : 0 ≤ Real.Gamma (s.re / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc ‖s‖ * ‖1 - s‖ * (Real.pi ^ (-s / 2).re * ‖Complex.Gamma (s / 2)‖)
      ≤ (1 + ‖s‖) * (1 + ‖s‖) * (1 * Real.Gamma (s.re / 2)) := by
        gcongr
        linarith
    _ = _ := by ring

lemma norm_inv_gfac_half_le (t : ℝ) (σ : ℝ) (hσ : |σ| = 1) :
    ‖(gfac (1 / 2 + σ * t * I))⁻¹‖ ≤ 16 * Real.Gamma (3 / 4) * Real.exp (Real.pi * (|t| / 2)) /
      Real.pi := by
  set s : ℂ := 1 / 2 + σ * t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = σ * t := by simp [hs]
  unfold gfac
  rw [Gammaℝ_def]
  have hsplit : (s * (1 - s) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)))⁻¹ =
      (s * (1 - s))⁻¹ * (((Real.pi : ℂ) ^ (-s / 2))⁻¹ * (Complex.Gamma (s / 2))⁻¹) := by
    simp only [mul_inv]
  rw [hsplit, norm_mul, norm_mul]
  have hss : ‖(s * (1 - s))⁻¹‖ ≤ 4 := by
    have : s * (1 - s) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring_nf; rw [I_sq]
      have : (σ : ℂ) ^ 2 = 1 := by
        have h := sq_abs σ; rw [hσ] at h; exact_mod_cast (by nlinarith : σ ^ 2 = 1)
      rw [this]; ring
    rw [this, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hpi : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ ≤ 4 := by
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-s / 2).re = -(1 / 4) := by simp [hre]; norm_num
    rw [this, Real.rpow_neg Real.pi_pos.le, inv_inv]
    have : Real.pi ^ (1 / 4 : ℝ) ≤ Real.pi ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by norm_num)
    rw [Real.rpow_one] at this
    linarith [Real.pi_lt_four]
  have hG := RankinError.norm_inv_Gamma_le_left (w := s / 2) (by simp [hre]; try norm_num)
  have hG' : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ Real.Gamma (3 / 4) * Real.exp (Real.pi * (|t| / 2)) /
      Real.pi := by
    refine hG.trans (le_of_eq ?_)
    have h1 : (s / 2).re = 1 / 4 := by simp [hre]; norm_num
    have h2 : |(s / 2).im| = |t| / 2 := by
      simp only [Complex.div_ofNat_im, him]
      rw [abs_div, abs_mul, hσ, one_mul, abs_two]
    rw [h1, h2]; norm_num
  have hpos : 0 ≤ Real.Gamma (3 / 4) * Real.exp (Real.pi * (|t| / 2)) / Real.pi := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3 / 4)
    positivity
  calc ‖(s * (1 - s))⁻¹‖ * (‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ * ‖(Complex.Gamma (s / 2))⁻¹‖)
      ≤ 4 * (4 * (Real.Gamma (3 / 4) * Real.exp (Real.pi * (|t| / 2)) / Real.pi)) := by
        gcongr
    _ = _ := by ring

/-- Region `|y| ≥ t/4`. -/
theorem gamma_ratio_far {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t y : ℝ, 8 ≤ t → t / 4 ≤ |y| →
      ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (Real.log (t / (2 * Real.pi)) : ℂ))) - 1‖ ≤
        K * ((1 + |y|) ^ 5 * Real.exp (4 * Real.pi * |y|)) / t := by
  set G1 : ℝ := Real.Gamma ((1 / 2 + c) / 2) with hG1
  set G3 : ℝ := 16 * Real.Gamma (3 / 4) / Real.pi with hG3
  have hG1p : 0 < G1 := Real.Gamma_pos_of_pos (by linarith)
  have hG3p : 0 < G3 := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3 / 4); rw [hG3]; positivity
  refine ⟨4 * (625 * G1 ^ 2 * G3 ^ 2 + 1), by positivity, fun t y ht hy => ?_⟩
  have ht0 : 0 < t := by linarith
  set z : ℂ := (c : ℂ) + y * I with hz
  set ℓ : ℝ := Real.log (t / (2 * Real.pi)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four])
  have hy0 : 0 ≤ |y| := abs_nonneg y
  -- ‖R_t‖
  have hsp : ‖sp t z‖ ≤ 2 + |t| + |y| := by
    have := norm_s_le t c y (by rw [abs_of_pos (by linarith)]; exact hc1) 1 (by simp)
    simpa [sp, hz] using this
  have hsm : ‖sm t z‖ ≤ 2 + |t| + |y| := by
    have := norm_s_le t c y (by rw [abs_of_pos (by linarith)]; exact hc1) (-1) (by simp)
    have e : (1 / 2 : ℂ) + ((c : ℂ) + y * I) + ((-1 : ℝ) : ℂ) * t * I = sm t z := by
      rw [hz]; unfold sm; push_cast; ring
    rwa [e] at this
  have hre_p : (sp t z).re = 1 / 2 + c := by simp [sp, hz]
  have hre_m : (sm t z).re = 1 / 2 + c := by simp [sm, hz]
  have hgp := norm_gfac_le (s := sp t z) (by rw [hre_p]; linarith)
  have hgm := norm_gfac_le (s := sm t z) (by rw [hre_m]; linarith)
  rw [hre_p] at hgp; rw [hre_m] at hgm
  have hA : 1 + (2 + |t| + |y|) ≤ 5 * (1 + |y|) := by rw [abs_of_pos ht0]; linarith
  have hgp' : ‖gfac (sp t z)‖ ≤ (5 * (1 + |y|)) ^ 2 * G1 := by
    refine hgp.trans ?_; gcongr; linarith
  have hgm' : ‖gfac (sm t z)‖ ≤ (5 * (1 + |y|)) ^ 2 * G1 := by
    refine hgm.trans ?_; gcongr; linarith
  have hi1 := norm_inv_gfac_half_le t 1 (by simp)
  have hi2 := norm_inv_gfac_half_le t (-1) (by simp)
  have e1 : sp t 0 = 1 / 2 + ((1 : ℝ) : ℂ) * t * I := by unfold sp; push_cast; ring
  have e2 : sm t 0 = 1 / 2 + ((-1 : ℝ) : ℂ) * t * I := by unfold sm; push_cast; ring
  have hexpt : Real.exp (Real.pi * (|t| / 2)) ^ 2 ≤ Real.exp (4 * Real.pi * |y|) := by
    rw [← Real.exp_nat_mul]; push_cast
    apply Real.exp_le_exp.mpr
    rw [abs_of_pos ht0]; nlinarith [Real.pi_pos]
  have hR : ‖Rt t z‖ ≤ 625 * G1 ^ 2 * G3 ^ 2 * ((1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|)) := by
    unfold Rt G0
    rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, e1, e2]
    have hi1' : ‖(gfac (1 / 2 + ((1:ℝ):ℂ) * t * I))⁻¹‖ ≤ G3 * Real.exp (Real.pi * (|t| / 2)) := by
      refine hi1.trans (le_of_eq ?_); rw [hG3]; ring
    have hi2' : ‖(gfac (1 / 2 + ((-1:ℝ):ℂ) * t * I))⁻¹‖ ≤ G3 * Real.exp (Real.pi * (|t| / 2)) := by
      refine hi2.trans (le_of_eq ?_); rw [hG3]; ring
    calc ‖gfac (sp t z)‖ * ‖gfac (sm t z)‖ * (‖(gfac (1 / 2 + ((1:ℝ):ℂ) * t * I))⁻¹‖ *
          ‖(gfac (1 / 2 + ((-1:ℝ):ℂ) * t * I))⁻¹‖)
        ≤ ((5 * (1 + |y|)) ^ 2 * G1) * ((5 * (1 + |y|)) ^ 2 * G1) *
          ((G3 * Real.exp (Real.pi * (|t| / 2))) * (G3 * Real.exp (Real.pi * (|t| / 2)))) := by
          gcongr
      _ = 625 * G1 ^ 2 * G3 ^ 2 * ((1 + |y|) ^ 4 * Real.exp (Real.pi * (|t| / 2)) ^ 2) := by ring
      _ ≤ _ := by gcongr
  have hexpz : ‖cexp (-(z * (ℓ : ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have : (-(z * (ℓ : ℂ))).re = -(c * ℓ) := by simp [hz]
    rw [this, Real.exp_le_one_iff]
    have : 0 ≤ c * ℓ := mul_nonneg (by linarith) hℓ0
    linarith
  have hX : 1 ≤ (1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|) := by
    have h1 : 1 ≤ (1 + |y|) ^ 4 := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ Real.exp (4 * Real.pi * |y|) := Real.one_le_exp (by positivity)
    nlinarith
  have hbig : ‖Rt t z * cexp (-(z * (ℓ : ℂ))) - 1‖ ≤
      (625 * G1 ^ 2 * G3 ^ 2 + 1) * ((1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_one]
    have := norm_nonneg (Rt t z)
    calc ‖Rt t z‖ * ‖cexp (-(z * (ℓ : ℂ)))‖ + 1 ≤ ‖Rt t z‖ * 1 + 1 := by gcongr
      _ ≤ _ := by nlinarith
  refine hbig.trans ?_
  rw [le_div_iff₀ ht0]
  have hpos : 0 ≤ (625 * G1 ^ 2 * G3 ^ 2 + 1) * ((1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|)) := by
    positivity
  have h4 : t ≤ 4 * (1 + |y|) := by linarith
  calc (625 * G1 ^ 2 * G3 ^ 2 + 1) * ((1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|)) * t
      ≤ (625 * G1 ^ 2 * G3 ^ 2 + 1) * ((1 + |y|) ^ 4 * Real.exp (4 * Real.pi * |y|)) *
        (4 * (1 + |y|)) := by gcongr
    _ = _ := by ring

/-- `(1+|y|)⁵ e^{100|y|} ≤ 120 e^{1+101²/2} e^{y²/2}`. -/
lemma poly_exp_le_gauss (y : ℝ) :
    (1 + |y|) ^ 5 * Real.exp (100 * |y|) ≤ 120 * Real.exp (1 + 101 ^ 2 / 2) * Real.exp (y ^ 2 / 2) := by
  have h1 : (1 + |y|) ^ 5 ≤ 120 * Real.exp (1 + |y|) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + |y|) (by positivity) 5
    rw [div_le_iff₀ (by positivity)] at this
    have h5 : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [h5] at this; linarith
  have h2 : Real.exp (1 + |y|) * Real.exp (100 * |y|) ≤ Real.exp (1 + 101 ^ 2 / 2) * Real.exp (y ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg (|y| - 101)]
  calc (1 + |y|) ^ 5 * Real.exp (100 * |y|) ≤ 120 * Real.exp (1 + |y|) * Real.exp (100 * |y|) := by
        gcongr
    _ = 120 * (Real.exp (1 + |y|) * Real.exp (100 * |y|)) := by ring
    _ ≤ _ := by rw [mul_assoc]; gcongr

/-- **The Gamma-ratio estimate on the line.** -/
theorem gamma_ratio_line {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t y : ℝ, 8 ≤ t →
      ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (Real.log (t / (2 * Real.pi)) : ℂ))) - 1‖ ≤
        K * Real.exp (y ^ 2 / 2) / t := by
  obtain ⟨KB, hKB, hfar⟩ := gamma_ratio_far hc hc1
  set K₁ : ℝ := 204 * Real.exp 100 + KB with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨K₁ * (120 * Real.exp (1 + 101 ^ 2 / 2)), by positivity, fun t y ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hP := poly_exp_le_gauss y
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hmono : (1 + |y|) ^ 4 * Real.exp (100 * |y|) ≤ (1 + |y|) ^ 5 * Real.exp (100 * |y|) := by
    gcongr <;> first | exact hy1 | norm_num
  have hmono2 : (1 + |y|) ^ 5 * Real.exp (4 * Real.pi * |y|) ≤ (1 + |y|) ^ 5 * Real.exp (100 * |y|) := by
    gcongr; nlinarith [Real.pi_lt_four, abs_nonneg y]
  have hX : 0 ≤ (1 + |y|) ^ 5 * Real.exp (100 * |y|) := by positivity
  rcases le_or_gt |y| (t / 4) with h | h
  · refine (gamma_ratio_near ht (by linarith) hc1 h).trans ?_
    rw [div_le_div_iff_of_pos_right ht0]
    calc 204 * Real.exp 100 * ((1 + |y|) ^ 4 * Real.exp (100 * |y|))
        ≤ K₁ * ((1 + |y|) ^ 5 * Real.exp (100 * |y|)) :=
          mul_le_mul (by rw [hK₁]; linarith) hmono (by positivity) hK₁0
      _ ≤ K₁ * (120 * Real.exp (1 + 101 ^ 2 / 2) * Real.exp (y ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hP hK₁0
      _ = _ := by ring
  · refine (hfar t y ht h.le).trans ?_
    rw [div_le_div_iff_of_pos_right ht0]
    calc KB * ((1 + |y|) ^ 5 * Real.exp (4 * Real.pi * |y|))
        ≤ K₁ * ((1 + |y|) ^ 5 * Real.exp (100 * |y|)) :=
          mul_le_mul (by rw [hK₁]; linarith [Real.exp_pos 100]) hmono2 (by positivity) hK₁0
      _ ≤ K₁ * (120 * Real.exp (1 + 101 ^ 2 / 2) * Real.exp (y ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hP hK₁0
      _ = _ := by ring

lemma continuousAt_gfac {s : ℂ} (hs : 0 < s.re) : ContinuousAt gfac s := by
  have h1 : ContinuousAt (fun s => (Gammaℝ s)⁻¹) s := differentiable_Gammaℝ_inv.continuous.continuousAt
  have h2 : (Gammaℝ s)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
  have h3 : ContinuousAt (fun s => ((Gammaℝ s)⁻¹)⁻¹) s := h1.inv₀ h2
  simp only [inv_inv] at h3
  unfold gfac
  exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id))).mul h3

lemma continuous_Rt_line (t : ℝ) {c : ℝ} (hc : 0 ≤ c) : Continuous fun y : ℝ => Rt t (c + y * I) := by
  unfold Rt
  refine Continuous.div_const ?_ _
  refine Continuous.mul ?_ ?_
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.comp (g := gfac) (continuousAt_gfac (by simp [sp]; linarith)) ?_
    unfold sp; fun_prop
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.comp (g := gfac) (continuousAt_gfac (by simp [sm]; linarith)) ?_
    unfold sm; fun_prop

end RamanujanTau.ZetaAFE
