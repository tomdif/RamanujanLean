/-
# `‖R_t(c+iy) (t/2π)^{−2(c+iy)} − 1‖ ≤ K e^{y²/2}/t²` (all `y`, `t ≥ 16`)

`|y| ≤ t/4`: `R_t e^{−2zℓ} = e^{E_t}` with `‖E_t‖ ≤ 150(1+|y|)³/t²` (`norm_EfD_le`).
`|y| > t/4`: `|Γ(6+c+iv)| ≤ Γ(6+c)` and `|Γ(6+it)|² = Pq(t) πt/sinh(πt) ≥ e^{−πt}`; the loss `e^{πt}`
and `1 ≤ 16y²/t²` are absorbed by `e^{y²/2}`.
-/
import RamanujanTau.GoodSecondTerm.GammaD

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL RamanujanTau.ZeroCountRvM

theorem gamma_ratio_near_D {t c y : ℝ} (ht : 16 ≤ t) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hy : |y| ≤ t / 4) :
    ‖RtD t (c + y * I) * cexp (-(2 * ((c : ℂ) + y * I) * (ellT t : ℂ))) - 1‖ ≤
      150 * Real.exp 15 * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [RtD_decomp ht0 (by simp [hc])]
  have hE := norm_EfD_le ht hc hc1 hy
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hEs : ‖EfD t ((c : ℂ) + y * I)‖ ≤ 15 * (1 + |y|) := by
    refine hE.trans ?_
    have hr : (1 + |y|) / t ≤ 5 / 16 := by rw [div_le_iff₀ ht0]; linarith
    have h0 : 0 ≤ (1 + |y|) / t := by positivity
    rw [show 150 * (1 + |y|) ^ 3 / t ^ 2 = 150 * (1 + |y|) * ((1 + |y|) / t) ^ 2 by
      field_simp]
    have : ((1 + |y|) / t) ^ 2 ≤ (5 / 16) ^ 2 := pow_le_pow_left₀ h0 hr 2
    nlinarith
  have hsub : ‖cexp (EfD t ((c : ℂ) + y * I)) - 1‖ ≤
      ‖EfD t ((c : ℂ) + y * I)‖ * Real.exp (15 * (1 + |y|)) := by
    have := Complex.norm_exp_sub_sum_le_norm_mul_exp (EfD t ((c : ℂ) + y * I)) 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one] at this
    exact this.trans (by gcongr)
  refine hsub.trans ?_
  have hexp : Real.exp (15 * (1 + |y|)) = Real.exp 15 * Real.exp (15 * |y|) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖EfD t ((c : ℂ) + y * I)‖ * Real.exp (15 * (1 + |y|))
      ≤ 150 * (1 + |y|) ^ 3 / t ^ 2 * Real.exp (15 * (1 + |y|)) := by gcongr
    _ = _ := by rw [hexp]; ring

lemma norm_gD_le {s : ℂ} (hs : 0 ≤ s.re) (hs0 : 0 < s.re) : ‖gD s‖ ≤ Real.Gamma s.re := by
  unfold gD
  rw [norm_mul, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have h1 : (2 * Real.pi) ^ (-s).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by simp; linarith)
  have h2 := RankinError.norm_Gamma_le_Gamma_re hs0
  have hG : 0 ≤ Real.Gamma s.re := (Real.Gamma_pos_of_pos hs0).le
  calc (2 * Real.pi) ^ (-s).re * ‖Complex.Gamma s‖ ≤ 1 * Real.Gamma s.re := by gcongr
    _ = _ := one_mul _

lemma norm_G0D_ge {t : ℝ} (ht : 1 ≤ t) :
    (2 * Real.pi) ^ (-(12 : ℝ)) * Real.exp (-(Real.pi * t)) ≤ ‖G0D t‖ := by
  have ht0 : 0 < t := by linarith
  have e1 : dp t 0 = 6 + t * I := by unfold dp; ring
  have hconj : ‖Complex.Gamma (dm t 0)‖ = ‖Complex.Gamma (6 + t * I)‖ := by
    rw [dm_zero, Complex.Gamma_conj, Complex.norm_conj]
  unfold G0D gD
  rw [norm_mul, norm_mul, norm_mul, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by positivity), norm_cpow_eq_rpow_re_of_pos (by positivity), hconj, e1]
  have hre1 : (-(6 + (t : ℂ) * I)).re = -6 := by simp
  have hre2 : (-dm t 0).re = -6 := by simp [dm]
  rw [hre1, hre2]
  have hG := CriticalMeanSquareAsymp.norm_Gamma_six_sq ht0.ne'
  have hPq := CriticalMeanSquareAsymp.Pq_ge t
  have hsinh := CriticalMeanSquareAsymp.sinh_le_half_exp (Real.pi * t)
  have hsp : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hlow : Real.exp (-(Real.pi * t)) ≤ ‖Complex.Gamma (6 + t * I)‖ ^ 2 := by
    rw [hG]
    have ht10 : 1 ≤ t ^ 10 := one_le_pow₀ ht
    have h1 : Real.pi * t / Real.sinh (Real.pi * t) ≥ 2 * Real.pi * t * Real.exp (-(Real.pi * t)) := by
      rw [ge_iff_le, le_div_iff₀ hsp, Real.exp_neg]
      have he := Real.exp_pos (Real.pi * t)
      calc 2 * Real.pi * t * (Real.exp (Real.pi * t))⁻¹ * Real.sinh (Real.pi * t)
          ≤ 2 * Real.pi * t * (Real.exp (Real.pi * t))⁻¹ * (Real.exp (Real.pi * t) / 2) := by gcongr
        _ = Real.pi * t := by field_simp
    have h2 : 2 * Real.pi * t ≥ 1 := by nlinarith [Real.pi_gt_three]
    have hE := Real.exp_pos (-(Real.pi * t))
    calc Real.exp (-(Real.pi * t)) ≤ 1 * (2 * Real.pi * t * Real.exp (-(Real.pi * t))) := by nlinarith
      _ ≤ CriticalMeanSquareAsymp.Pq t * (Real.pi * t / Real.sinh (Real.pi * t)) :=
          mul_le_mul (ht10.trans hPq) h1 (by positivity) (zero_le_one.trans (ht10.trans hPq))
  have h6 : (2 * Real.pi) ^ (-(6 : ℝ)) * (2 * Real.pi) ^ (-(6 : ℝ)) = (2 * Real.pi) ^ (-(12 : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  calc (2 * Real.pi) ^ (-(12 : ℝ)) * Real.exp (-(Real.pi * t))
      ≤ (2 * Real.pi) ^ (-(12 : ℝ)) * ‖Complex.Gamma (6 + t * I)‖ ^ 2 := by gcongr
    _ = _ := by rw [← h6]; ring

theorem gamma_ratio_far_D {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t y : ℝ, 16 ≤ t → t / 4 ≤ |y| →
      ‖RtD t (c + y * I) * cexp (-(2 * ((c : ℂ) + y * I) * (ellT t : ℂ))) - 1‖ ≤
        K * ((1 + |y|) ^ 5 * Real.exp (15 * |y|)) / t ^ 2 := by
  set G : ℝ := Real.Gamma (6 + c) ^ 2 * (2 * Real.pi) ^ (12 : ℝ) with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  refine ⟨16 * (G + 1), by positivity, fun t y ht hy => ?_⟩
  have ht0 : 0 < t := by linarith
  set z : ℂ := (c : ℂ) + y * I with hz
  have hℓ0 : 0 ≤ ellT t := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four])
  have hgp := norm_gD_le (s := dp t z) (by simp [dp, hz]; linarith) (by simp [dp, hz]; linarith)
  have hgm := norm_gD_le (s := dm t z) (by simp [dm, hz]; linarith) (by simp [dm, hz]; linarith)
  have hre_p : (dp t z).re = 6 + c := by simp [dp, hz]
  have hre_m : (dm t z).re = 6 + c := by simp [dm, hz]
  rw [hre_p] at hgp; rw [hre_m] at hgm
  have hG0D := norm_G0D_ge (t := t) (by linarith)
  have hG0Dpos : 0 < (2 * Real.pi) ^ (-(12 : ℝ)) * Real.exp (-(Real.pi * t)) := by positivity
  have hR : ‖RtD t z‖ ≤ G * Real.exp (Real.pi * t) := by
    unfold RtD
    rw [norm_div, norm_mul, div_le_iff₀ (hG0Dpos.trans_le hG0D)]
    have hGam : 0 ≤ Real.Gamma (6 + c) := (Real.Gamma_pos_of_pos (by linarith)).le
    calc ‖gD (dp t z)‖ * ‖gD (dm t z)‖ ≤ Real.Gamma (6 + c) * Real.Gamma (6 + c) := by gcongr
      _ = G * Real.exp (Real.pi * t) * ((2 * Real.pi) ^ (-(12 : ℝ)) * Real.exp (-(Real.pi * t))) := by
          have e1 : Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t)) = 1 := by
            rw [← Real.exp_add]; simp
          have e2 : (2 * Real.pi) ^ (12 : ℝ) * (2 * Real.pi) ^ (-(12 : ℝ)) = 1 := by
            rw [← Real.rpow_add (by positivity)]; simp
          calc Real.Gamma (6 + c) * Real.Gamma (6 + c) = Real.Gamma (6 + c) ^ 2 *
                ((2 * Real.pi) ^ (12 : ℝ) * (2 * Real.pi) ^ (-(12 : ℝ))) *
                (Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t))) := by rw [e1, e2]; ring
            _ = _ := by rw [hG]; ring
      _ ≤ G * Real.exp (Real.pi * t) * ‖G0D t‖ := by gcongr
  have hexpz : ‖cexp (-(2 * z * (ellT t : ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have : (-(2 * z * (ellT t : ℂ))).re = -(2 * c * ellT t) := by simp [hz]
    rw [this, Real.exp_le_one_iff]
    have : 0 ≤ 2 * c * ellT t := by positivity
    linarith
  have hpit : Real.exp (Real.pi * t) ≤ Real.exp (15 * |y|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_lt_d2, Real.pi_pos, mul_le_mul_of_nonneg_left hy Real.pi_pos.le, abs_nonneg y]
  have hy1 : 1 ≤ (1 + |y|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg y])
  have hX : 1 ≤ (1 + |y|) ^ 3 * Real.exp (15 * |y|) := by
    have := Real.one_le_exp (by positivity : (0:ℝ) ≤ 15 * |y|); nlinarith
  have hbig : ‖RtD t z * cexp (-(2 * z * (ellT t : ℂ))) - 1‖ ≤
      (G + 1) * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_one]
    have h0 := norm_nonneg (RtD t z)
    have h1 : ‖RtD t z‖ * ‖cexp (-(2 * z * (ellT t : ℂ)))‖ ≤ ‖RtD t z‖ := by
      nlinarith [norm_nonneg (cexp (-(2 * z * (ellT t : ℂ))))]
    have h2 : ‖RtD t z‖ ≤ G * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) := by
      refine hR.trans ?_
      calc G * Real.exp (Real.pi * t) ≤ G * Real.exp (15 * |y|) := by gcongr
        _ ≤ G * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) := by
            gcongr; nlinarith [Real.exp_pos (15 * |y|)]
    nlinarith
  refine hbig.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have h16 : t ^ 2 ≤ 16 * (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
  have hpos : 0 ≤ (G + 1) * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) := by positivity
  calc (G + 1) * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) * t ^ 2
      ≤ (G + 1) * ((1 + |y|) ^ 3 * Real.exp (15 * |y|)) * (16 * (1 + |y|) ^ 2) := by gcongr
    _ = _ := by ring

/-- `(1+|y|)⁵ e^{15|y|} ≤ 120 e^{129} e^{y²/2}`. -/
lemma poly_exp_le_gauss_D (y : ℝ) :
    (1 + |y|) ^ 5 * Real.exp (15 * |y|) ≤ 120 * Real.exp 129 * Real.exp (y ^ 2 / 2) := by
  have h1 : (1 + |y|) ^ 5 ≤ 120 * Real.exp (1 + |y|) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + |y|) (by positivity) 5
    rw [div_le_iff₀ (by positivity)] at this
    have h5 : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [h5] at this; linarith
  have h2 : Real.exp (1 + |y|) * Real.exp (15 * |y|) ≤ Real.exp 129 * Real.exp (y ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg (|y| - 16)]
  calc (1 + |y|) ^ 5 * Real.exp (15 * |y|) ≤ 120 * Real.exp (1 + |y|) * Real.exp (15 * |y|) := by
        gcongr
    _ = 120 * (Real.exp (1 + |y|) * Real.exp (15 * |y|)) := by ring
    _ ≤ _ := by rw [mul_assoc]; gcongr

/-- **Gamma-ratio for Δ on the line**: `‖R_t(c+iy)(t/2π)^{−2(c+iy)} − 1‖ ≤ K e^{y²/2}/t²`. -/
theorem gamma_ratio_delta {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t y : ℝ, 16 ≤ t →
      ‖RtD t (c + y * I) * cexp (-(2 * ((c : ℂ) + y * I) * (ellT t : ℂ))) - 1‖ ≤
        K * Real.exp (y ^ 2 / 2) / t ^ 2 := by
  obtain ⟨KB, hKB, hfar⟩ := gamma_ratio_far_D hc hc1
  set K₁ : ℝ := 150 * Real.exp 15 + KB with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨K₁ * (120 * Real.exp 129), by positivity, fun t y ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hP := poly_exp_le_gauss_D y
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hmono : (1 + |y|) ^ 3 * Real.exp (15 * |y|) ≤ (1 + |y|) ^ 5 * Real.exp (15 * |y|) := by
    gcongr <;> first | exact hy1 | norm_num
  have hX : 0 ≤ (1 + |y|) ^ 5 * Real.exp (15 * |y|) := by positivity
  rcases le_or_gt |y| (t / 4) with h | h
  · refine (gamma_ratio_near_D ht hc hc1 h).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    calc 150 * Real.exp 15 * ((1 + |y|) ^ 3 * Real.exp (15 * |y|))
        ≤ K₁ * ((1 + |y|) ^ 5 * Real.exp (15 * |y|)) :=
          mul_le_mul (by rw [hK₁]; linarith) hmono (by positivity) hK₁0
      _ ≤ K₁ * (120 * Real.exp 129 * Real.exp (y ^ 2 / 2)) := mul_le_mul_of_nonneg_left hP hK₁0
      _ = _ := by ring
  · refine (hfar t y ht h.le).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    calc KB * ((1 + |y|) ^ 5 * Real.exp (15 * |y|))
        ≤ K₁ * ((1 + |y|) ^ 5 * Real.exp (15 * |y|)) :=
          mul_le_mul_of_nonneg_right (by rw [hK₁]; linarith [Real.exp_pos 15]) hX
      _ ≤ K₁ * (120 * Real.exp 129 * Real.exp (y ^ 2 / 2)) := mul_le_mul_of_nonneg_left hP hK₁0
      _ = _ := by ring

lemma continuousAt_gD {s : ℂ} (hs : 0 < s.re) : ContinuousAt gD s := by
  unfold gD
  refine ContinuousAt.mul ?_ ?_
  · exact (continuousAt_const_cpow (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))).comp
      continuousAt_id.neg
  · exact (Complex.differentiableAt_Gamma _ (not_neg_nat_of_re_pos hs)).continuousAt

lemma continuous_RtD_line (t : ℝ) {c : ℝ} (hc : 0 ≤ c) : Continuous fun y : ℝ => RtD t (c + y * I) := by
  unfold RtD
  refine Continuous.div_const ?_ _
  refine Continuous.mul ?_ ?_
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.comp (g := gD) (continuousAt_gD (by simp [dp]; linarith)) ?_
    unfold dp; fun_prop
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.comp (g := gD) (continuousAt_gD (by simp [dm]; linarith)) ?_
    unfold dm; fun_prop

end RamanujanTau.GoodSecondTerm
