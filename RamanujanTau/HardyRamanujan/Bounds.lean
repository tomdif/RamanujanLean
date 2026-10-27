/-
# Pointwise bounds on the arcs

* `‖F(w) − 1‖ ≤ 2C₀‖w‖` for `‖w‖ ≤ 1/2`, with `C₀ = Σ p(k)2^{−k}`;
* major arc (`|θ| ≤ t`): `‖M(θ)(F(w′) − 1)‖ ≤ e^{2A}·2C₀e^{−2π²/t}`;
* minor arc (`t ≤ |θ| ≤ π`): `‖F(e^{−z})e^{nz}‖ ≤ (1 + C₀)e^{2A}e^{−1/(200t)}`.
-/
import RamanujanTau.HardyRamanujan.Param

set_option autoImplicit false

namespace HardyRamanujan
open Complex Filter Metric
open scoped Real Topology

lemma p_zero : p 0 = 1 := by decide

lemma exp_neg_log_two (k : ℕ) : Real.exp (-(k * Real.log 2)) = (1 / 2 : ℝ) ^ k := by
  rw [show -(k * Real.log 2) = k * Real.log (1 / 2) by rw [one_div, Real.log_inv]; ring, Real.exp_nat_mul,
    Real.exp_log (by norm_num)]

lemma summable_half : Summable fun k : ℕ => (p k : ℝ) * (1 / 2 : ℝ) ^ k :=
  (summable_p_exp (Real.log_pos one_lt_two)).congr fun k => by rw [exp_neg_log_two]

/-- `C₀ = Σ p(k) 2^{−k}`. -/
noncomputable def C0 : ℝ := ∑' k, (p k : ℝ) * (1 / 2 : ℝ) ^ k

lemma C0_nonneg : 0 ≤ C0 := tsum_nonneg fun k => by positivity

lemma F_sub_one {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖F w - 1‖ ≤ 2 * C0 * ‖w‖ := by
  have hb : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
  have h := hasSum_F hb
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, p_zero, Nat.cast_one, pow_zero, mul_one] at h
  have hs : Summable fun k : ℕ => (p (k + 1) : ℝ) * (1 / 2 : ℝ) ^ (k + 1) :=
    summable_half.comp_injective (add_left_injective 1)
  have hT : ∑' k : ℕ, (p (k + 1) : ℝ) * (1 / 2 : ℝ) ^ (k + 1) ≤ C0 := by
    have := summable_half.sum_add_tsum_nat_add 1
    rw [C0, ← this]
    simp [p_zero]
  have hg : HasSum (fun k : ℕ => 2 * ‖w‖ * ((p (k + 1) : ℝ) * (1 / 2 : ℝ) ^ (k + 1)))
      (2 * ‖w‖ * ∑' k : ℕ, (p (k + 1) : ℝ) * (1 / 2 : ℝ) ^ (k + 1)) := hs.hasSum.mul_left _
  refine (h.norm_le_of_bounded hg fun k => ?_).trans ?_
  · rw [norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : ‖w‖ ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (norm_nonneg _) hw k
    have h2 : (0 : ℝ) ≤ p (k + 1) := by positivity
    calc (p (k + 1) : ℝ) * ‖w‖ ^ (k + 1) = (p (k + 1) : ℝ) * ‖w‖ * ‖w‖ ^ k := by ring
      _ ≤ (p (k + 1) : ℝ) * ‖w‖ * (1 / 2) ^ k := by gcongr
      _ = _ := by ring
  · have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * ‖w‖)
    linarith

lemma norm_sq_le_one {z : ℂ} (hz : z ≠ 0) (h : ‖z‖ ≤ 2 * π) : ‖sq z‖ ≤ 1 := by
  rw [sq, norm_exp, Complex.div_ofNat_re, log_re, Real.exp_le_one_iff]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have : ‖z / (2 * π)‖ ≤ 1 := by
    rw [norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg hπ.le],
      div_le_one hπ]; exact h
  have := Real.log_nonpos (norm_nonneg _) this
  linarith

lemma zt_ne_zero {t θ : ℝ} (ht : 0 < t) : zt t θ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [zt] at this; linarith

lemma normSq_zt (t θ : ℝ) : Complex.normSq (zt t θ) = t ^ 2 + θ ^ 2 := by
  simp [zt, Complex.normSq_apply]; ring

lemma re_div_zt (c t θ : ℝ) : ((c : ℂ) / zt t θ).re = c * t / (t ^ 2 + θ ^ 2) := by
  rw [div_re, normSq_zt]; simp [zt]

lemma norm_zt_le {t θ : ℝ} (ht : 0 < t) (hθ : |θ| ≤ π) : ‖zt t θ‖ ≤ t + π := by
  calc ‖zt t θ‖ ≤ ‖(t : ℂ)‖ + ‖(θ : ℂ) * I‖ := norm_add_le _ _
    _ ≤ t + π := by simp [Complex.norm_real, abs_of_pos ht]; linarith

/-- **the major-arc correction**. -/
lemma major_err_bound {n : ℕ} (hn : 1 ≤ n) (ht2 : tn n ≤ 1 / 2) {θ : ℝ} (hθ : |θ| ≤ tn n) :
    ‖Mfun n (tn n) θ * (F (cexp (-(4 * π ^ 2 / zt (tn n) θ))) - 1)‖ ≤
      Real.exp (2 * An n) * (2 * C0 * Real.exp (-(2 * π ^ 2 / tn n))) := by
  set t := tn n with htdef
  have ht := tn_pos hn
  have hz0 := zt_ne_zero (θ := θ) ht
  have hnz : 0 < t ^ 2 + θ ^ 2 := by positivity
  have hθ2 : θ ^ 2 ≤ t ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  -- the pieces
  have hsq : ‖sq (zt t θ)‖ ≤ 1 := norm_sq_le_one hz0 (by
    have := norm_zt_le ht (hθ.trans (by linarith [Real.pi_gt_three]))
    nlinarith [Real.pi_gt_three])
  have hRe1 : (π ^ 2 / (6 * zt t θ) - zt t θ / 24).re ≤ An n := by
    have e : (π : ℂ) ^ 2 / (6 * zt t θ) = (((π ^ 2 / 6 : ℝ)) : ℂ) / zt t θ := by push_cast; field_simp
    rw [sub_re, e, re_div_zt, ← An_eq hn, ← htdef]
    have : (zt t θ / 24).re = t / 24 := by rw [Complex.div_ofNat_re]; simp [zt]
    rw [this]
    have h1 : π ^ 2 / 6 * t / (t ^ 2 + θ ^ 2) ≤ π ^ 2 / (6 * t) := by
      rw [div_le_div_iff₀ hnz (by positivity)]; nlinarith [sq_nonneg θ, Real.pi_pos, sq_nonneg t]
    linarith
  have hRe2 : ((n : ℂ) * zt t θ).re = An n := by simp [zt, An, ← htdef]
  have hw : ‖cexp (-(4 * π ^ 2 / zt t θ))‖ ≤ Real.exp (-(2 * π ^ 2 / t)) := by
    rw [norm_exp, Real.exp_le_exp, neg_re]
    have e : (4 : ℂ) * π ^ 2 / zt t θ = (((4 * π ^ 2 : ℝ)) : ℂ) / zt t θ := by push_cast; ring
    rw [e, re_div_zt, neg_le_neg_iff, div_le_div_iff₀ ht hnz]
    nlinarith [Real.pi_pos, sq_nonneg π]
  have hw2 : Real.exp (-(2 * π ^ 2 / t)) ≤ 1 / 2 := by
    have h1 : 1 ≤ 2 * π ^ 2 / t := by
      rw [le_div_iff₀ ht]; nlinarith [Real.pi_gt_three]
    calc Real.exp (-(2 * π ^ 2 / t)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
  have hF := F_sub_one (hw.trans hw2)
  unfold Mfun
  rw [norm_mul, norm_mul, norm_mul, norm_exp, norm_exp]
  have hE : Real.exp ((π ^ 2 / (6 * zt t θ) - zt t θ / 24).re) * Real.exp (((n : ℂ) * zt t θ).re) ≤
      Real.exp (2 * An n) := by
    rw [← Real.exp_add, Real.exp_le_exp, hRe2]; linarith
  calc ‖sq (zt t θ)‖ * Real.exp ((π ^ 2 / (6 * zt t θ) - zt t θ / 24).re) * Real.exp (((n : ℂ) * zt t θ).re) *
        ‖F (cexp (-(4 * π ^ 2 / zt t θ))) - 1‖
      ≤ 1 * (Real.exp (2 * An n)) * (2 * C0 * Real.exp (-(2 * π ^ 2 / t))) := by
        rw [mul_assoc (‖sq _‖)]
        gcongr
        · exact hF.trans (by gcongr; linarith [C0_nonneg])
    _ = _ := by ring

/-- `‖F(e^{−t})‖ ≤ (1 + C₀)e^A`. -/
lemma F_real_bound {n : ℕ} (hn : 1 ≤ n) (ht2 : tn n ≤ 1 / 2) :
    ‖F (cexp (-((tn n : ℝ) : ℂ)))‖ ≤ (1 + C0) * Real.exp (An n) := by
  set t := tn n with htdef
  have ht := tn_pos hn
  have hz : 0 < ((t : ℂ)).re := by simpa using ht
  rw [F_modular hz, norm_mul, norm_mul, norm_exp]
  have hsq : ‖sq (t : ℂ)‖ ≤ 1 := norm_sq_le_one (by exact_mod_cast ht.ne') (by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le]; nlinarith [Real.pi_gt_three])
  have hRe : (π ^ 2 / (6 * (t : ℂ)) - (t : ℂ) / 24).re ≤ An n := by
    rw [show (π : ℂ) ^ 2 / (6 * (t : ℂ)) - (t : ℂ) / 24 = ((π ^ 2 / (6 * t) - t / 24 : ℝ) : ℂ) by push_cast; ring,
      ofReal_re, An_eq hn]
    linarith
  have hw : ‖cexp (-(4 * π ^ 2 / (t : ℂ)))‖ ≤ 1 / 2 := by
    have e : (-(4 * π ^ 2 / (t : ℂ))).re = -(4 * π ^ 2 / t) := by
      rw [show (4 : ℂ) * π ^ 2 / (t : ℂ) = ((4 * π ^ 2 / t : ℝ) : ℂ) by push_cast; ring, neg_re, ofReal_re]
    rw [norm_exp, e]
    have h1 : 1 ≤ 4 * π ^ 2 / t := by rw [le_div_iff₀ ht]; nlinarith [Real.pi_gt_three]
    calc Real.exp (-(4 * π ^ 2 / t)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
  have hF : ‖F (cexp (-(4 * π ^ 2 / (t : ℂ))))‖ ≤ 1 + C0 := by
    have := F_sub_one hw
    calc ‖F (cexp (-(4 * π ^ 2 / (t : ℂ))))‖ ≤ ‖F (cexp (-(4 * π ^ 2 / (t : ℂ)))) - 1‖ + ‖(1 : ℂ)‖ := by
          have := norm_add_le (F (cexp (-(4 * π ^ 2 / (t : ℂ)))) - 1) 1; simpa using this
      _ ≤ 2 * C0 * (1 / 2) + 1 := by
          rw [norm_one]; gcongr
          exact this.trans (by gcongr; linarith [C0_nonneg])
      _ = 1 + C0 := by ring
  calc ‖sq (t : ℂ)‖ * Real.exp (π ^ 2 / (6 * (t : ℂ)) - (t : ℂ) / 24).re * ‖F (cexp (-(4 * π ^ 2 / (t : ℂ))))‖
      ≤ 1 * Real.exp (An n) * (1 + C0) := by gcongr
    _ = _ := by ring

/-- **the minor-arc integrand**. -/
lemma minor_integrand_bound {n : ℕ} (hn : 1 ≤ n) (ht2 : tn n ≤ 1 / 2) {θ : ℝ} (hθ1 : tn n ≤ |θ|)
    (hθ2 : |θ| ≤ π) :
    ‖F (cexp (-zt (tn n) θ)) * cexp (n * zt (tn n) θ)‖ ≤
      (1 + C0) * Real.exp (2 * An n) * Real.exp (-(1 / (200 * tn n))) := by
  have ht := tn_pos hn
  rw [norm_mul, norm_exp]
  have hm := minor_bound ht ht2 hθ1 hθ2
  have hr := F_real_bound hn ht2
  have hRe : ((n : ℂ) * zt (tn n) θ).re = An n := by simp [zt, An]
  rw [hRe]
  calc ‖F (cexp (-zt (tn n) θ))‖ * Real.exp (An n)
      ≤ ((1 + C0) * Real.exp (An n)) * Real.exp (-(1 / (200 * tn n))) * Real.exp (An n) := by
        gcongr; exact hm.trans (by gcongr)
    _ = _ := by rw [show 2 * An n = An n + An n by ring, Real.exp_add]; ring

end HardyRamanujan
