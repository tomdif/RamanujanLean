/-
# `R_t(z) = (t/2π)^{2z} (1 + O(e^{y²/2}/t²))` for the Δ Gamma factor

`gamma_ratio_delta`: for `0 ≤ c ≤ 1` there is `K` with, for `t ≥ 16` and all real `y`,
`‖R_t(c+iy) e^{−2(c+iy) log(t/2π)} − 1‖ ≤ K e^{y²/2}/t²`.
-/
import RamanujanTau.GoodSecondTerm.Stirling2
import RamanujanTau.ZetaAFE.Ingham

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL RamanujanTau.ZeroCountRvM

/-- `E_t(z) = Σ± [LG(6+z±it) − LG(6±it)] − 2z log t`. -/
noncomputable def EfD (t : ℝ) (z : ℂ) : ℂ :=
  LG (dp t z) - LG (dp t 0) + LG (dm t z) - LG (dm t 0) - 2 * z * (Real.log t : ℂ)

lemma gD_exp {s : ℂ} (hs : 0 < s.re) :
    gD s = cexp (-s * (Real.log (2 * Real.pi) : ℂ) + LG s) := by
  unfold gD
  rw [Gamma_eq_exp_LG hs, Complex.exp_add,
    cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))]
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by positivity)]
  ring_nf

lemma RtD_decomp {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    RtD t z * cexp (-(2 * z * (ellT t : ℂ))) = cexp (EfD t z) := by
  have hp : 0 < (dp t z).re := by simp [dp]; linarith
  have hm : 0 < (dm t z).re := by simp [dm]; linarith
  unfold RtD G0D
  rw [gD_exp hp, gD_exp hm, gD_exp (by simp [dp]), gD_exp (by simp [dm])]
  simp only [← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  unfold EfD ellT dp dm
  rw [Real.log_div ht.ne' (by positivity)]
  push_cast; ring

lemma log_pair_D {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 0 ≤ w.re)
    (hη : ‖(6 + w) ^ 2 / (t : ℂ) ^ 2‖ < 1) :
    log (dp t w) + log (dm t w) = 2 * (Real.log t : ℂ) + log (1 + (6 + w) ^ 2 / (t : ℂ) ^ 2) := by
  have hp : 0 < (dp t w).re := by simp [dp]; linarith
  have hm : 0 < (dm t w).re := by simp [dm]; linarith
  have h1 : log (dp t w * dm t w) = log (dp t w) + log (dm t w) := by
    rw [log_mul_eq_add_log_iff (Complex.ne_zero_of_re_pos hp) (Complex.ne_zero_of_re_pos hm)]
    have a1 := abs_lt.mp (arg_lt_of_re_pos hp)
    have a2 := abs_lt.mp (arg_lt_of_re_pos hm)
    constructor <;> linarith
  have hη0 : 1 + (6 + w) ^ 2 / (t : ℂ) ^ 2 ≠ 0 := by
    intro h
    have : (6 + w) ^ 2 / (t : ℂ) ^ 2 = -1 := by linear_combination h
    rw [this] at hη; simp at hη
  have h2 : dp t w * dm t w = ((t ^ 2 : ℝ) : ℂ) * (1 + (6 + w) ^ 2 / (t : ℂ) ^ 2) := by
    unfold dp dm
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  rw [← h1, h2, log_ofReal_mul (by positivity) hη0, Real.log_pow]
  push_cast; ring

lemma hasDerivAt_dp (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => dp t ((u : ℂ) * z)) z u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).mul_const z
  have h2 := (h1.const_add (6 : ℂ)).add_const ((t : ℂ) * I)
  convert h2 using 1

lemma hasDerivAt_dm (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => dm t ((u : ℂ) * z)) z u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).mul_const z
  have h2 := (h1.const_add (6 : ℂ)).sub_const ((t : ℂ) * I)
  convert h2 using 1

/-- **Second-order Stirling estimate**: `‖E_t(c+iy)‖ ≤ 150(1+|y|)³/t²` for `|y| ≤ t/4`, `t ≥ 16`. -/
theorem norm_EfD_le {t c y : ℝ} (ht : 16 ≤ t) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hy : |y| ≤ t / 4) :
    ‖EfD t ((c : ℂ) + y * I)‖ ≤ 150 * (1 + |y|) ^ 3 / t ^ 2 := by
  set z : ℂ := (c : ℂ) + y * I with hz
  have ht0 : 0 < t := by linarith
  have hzn : ‖z‖ ≤ 1 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    simp [hz, abs_of_nonneg hc]; linarith
  set Lt : ℂ := (Real.log t : ℂ) with hLt
  set f : ℝ → ℂ := fun u => LG (dp t ((u : ℂ) * z)) + LG (dm t ((u : ℂ) * z)) - 2 * ((u : ℂ) * z) * Lt
    with hf
  set f' : ℝ → ℂ := fun u => digamma (dp t ((u : ℂ) * z)) * z +
    digamma (dm t ((u : ℂ) * z)) * z - 2 * z * Lt with hf'
  have hgeo : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ((u : ℂ) * z).re ∧ ((u : ℂ) * z).re ≤ 1 ∧
      |((u : ℂ) * z).im| ≤ |y| ∧ ‖(u : ℂ) * z‖ ≤ 1 + |y| := by
    intro u hu
    have hre : ((u : ℂ) * z).re = u * c := by simp [hz]
    have him : ((u : ℂ) * z).im = u * y := by simp [hz]
    refine ⟨by rw [hre]; exact mul_nonneg hu.1 hc, by rw [hre]; nlinarith [hu.1, hu.2],
      by rw [him, abs_mul, abs_of_nonneg hu.1]; nlinarith [hu.1, hu.2, abs_nonneg y], ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    have := norm_nonneg z
    nlinarith [hu.1, hu.2]
  have hreP : ∀ u ∈ Icc (0 : ℝ) 1, 6 ≤ (dp t ((u : ℂ) * z)).re := by
    intro u hu
    have e : (dp t ((u : ℂ) * z)).re = 6 + ((u : ℂ) * z).re := by simp [dp]
    rw [e]; linarith [(hgeo u hu).1]
  have hreM : ∀ u ∈ Icc (0 : ℝ) 1, 6 ≤ (dm t ((u : ℂ) * z)).re := by
    intro u hu
    have e : (dm t ((u : ℂ) * z)).re = 6 + ((u : ℂ) * z).re := by simp [dm]
    rw [e]; linarith [(hgeo u hu).1]
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' u) (Icc 0 1) u := by
    intro u hu
    have h1 := (hasDerivAt_LG_digamma (by linarith [hreP u hu])).comp u (hasDerivAt_dp t z u)
    have h2 := (hasDerivAt_LG_digamma (by linarith [hreM u hu])).comp u (hasDerivAt_dm t z u)
    have h3 : HasDerivAt (fun u : ℝ => 2 * ((u : ℂ) * z) * Lt) (2 * z * Lt) u := by
      have := ((((hasDerivAt_id u).ofReal_comp).mul_const z).const_mul (2 : ℂ)).mul_const Lt
      simpa using this
    exact ((h1.add h2).sub h3).hasDerivWithinAt
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1, ‖f' u‖ ≤ 150 * (1 + |y|) ^ 3 / t ^ 2 := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hu
    obtain ⟨g1, g2, g3, g4⟩ := hgeo u hu'
    set w : ℂ := (u : ℂ) * z with hw
    have hyw := abs_le.mp g3
    have hyt := abs_le.mp hy
    -- digamma second-order errors
    have him_p : t * (3 / 4) ≤ |(dp t w).im| := by
      have : (dp t w).im = w.im + t := by simp [dp]
      rw [this, abs_of_pos (by linarith)]; linarith
    have him_m : t * (3 / 4) ≤ |(dm t w).im| := by
      have : (dm t w).im = w.im - t := by simp [dm]
      rw [this, abs_of_neg (by linarith)]; linarith
    have hP := norm_digamma_second (hreP u hu')
    have hM := norm_digamma_second (hreM u hu')
    have hPd : 10 / ((dp t w).re + |(dp t w).im|) ^ 2 ≤ 18 / t ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith [hreP u hu']) (by positivity)]
      nlinarith [hreP u hu']
    have hMd : 10 / ((dm t w).re + |(dm t w).im|) ^ 2 ≤ 18 / t ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith [hreM u hu']) (by positivity)]
      nlinarith [hreM u hu']
    -- η
    set η : ℂ := (6 + w) ^ 2 / (t : ℂ) ^ 2 with hη
    have hwn : ‖6 + w‖ ≤ 7 + |y| := by
      refine (norm_add_le _ _).trans ?_; norm_num; linarith
    have hr : (7 + |y|) / t ≤ 11 / 16 := by rw [div_le_iff₀ ht0]; linarith
    have hηn : ‖η‖ ≤ (7 + |y|) ^ 2 / t ^ 2 := by
      rw [hη, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      gcongr
    have hηhalf : ‖η‖ ≤ 1 / 2 := by
      refine hηn.trans ?_
      rw [show (7 + |y|) ^ 2 / t ^ 2 = ((7 + |y|) / t) ^ 2 by ring]
      have h0 : 0 ≤ (7 + |y|) / t := by positivity
      nlinarith
    have hlog := log_pair_D ht0 g1 (by rw [← hη]; linarith)
    rw [← hη] at hlog
    have hlog1 := norm_log_one_add_le hηhalf
    -- the 1/(2a) terms
    have hprod : dp t w * dm t w = ((t ^ 2 : ℝ) : ℂ) * (1 + η) := by
      rw [hη]; unfold dp dm
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      push_cast; field_simp; ring_nf; rw [I_sq]; ring
    have hne_p : dp t w ≠ 0 := Complex.ne_zero_of_re_pos (by linarith [hreP u hu'])
    have hne_m : dm t w ≠ 0 := Complex.ne_zero_of_re_pos (by linarith [hreM u hu'])
    have h1η : ‖1 + η‖ ≥ 1 / 2 := by
      have h := norm_add_le (1 + η) (-η)
      rw [add_neg_cancel_right, norm_neg, norm_one] at h; linarith
    have hinv : ‖1 / (2 * dp t w) + 1 / (2 * dm t w)‖ ≤ 2 * (7 + |y|) / t ^ 2 := by
      have e : 1 / (2 * dp t w) + 1 / (2 * dm t w) = (6 + w) / (((t ^ 2 : ℝ) : ℂ) * (1 + η)) := by
        have e1 : 1 / (2 * dp t w) + 1 / (2 * dm t w) = (dp t w + dm t w) / (2 * (dp t w * dm t w)) := by
          field_simp; ring
        have e2 : dp t w + dm t w = 2 * (6 + w) := by unfold dp dm; ring
        rw [e1, e2, hprod, mul_div_mul_left _ _ two_ne_zero]
      rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_le_div_iff₀ (by have : 0 < ‖1 + η‖ := by linarith
                            positivity) (by positivity)]
      have : 0 ≤ ‖6 + w‖ := norm_nonneg _
      have hA : 0 ≤ 2 * (7 + |y|) * t ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hwn (sq_nonneg t), mul_le_mul_of_nonneg_left h1η hA]
    have hsum : digamma (dp t w) + digamma (dm t w) - 2 * Lt =
        (digamma (dp t w) - log (dp t w) + 1 / (2 * dp t w)) +
        (digamma (dm t w) - log (dm t w) + 1 / (2 * dm t w)) + log (1 + η) -
        (1 / (2 * dp t w) + 1 / (2 * dm t w)) := by
      rw [hLt]; linear_combination hlog
    have hsn : ‖digamma (dp t w) + digamma (dm t w) - 2 * Lt‖ ≤ 148 * (1 + |y|) ^ 2 / t ^ 2 := by
      rw [hsum]
      have n1 := norm_sub_le ((digamma (dp t w) - log (dp t w) + 1 / (2 * dp t w)) +
        (digamma (dm t w) - log (dm t w) + 1 / (2 * dm t w)) + log (1 + η))
        (1 / (2 * dp t w) + 1 / (2 * dm t w))
      have n2 : ‖(digamma (dp t w) - log (dp t w) + 1 / (2 * dp t w)) +
          (digamma (dm t w) - log (dm t w) + 1 / (2 * dm t w)) + log (1 + η)‖ ≤
          ‖digamma (dp t w) - log (dp t w) + 1 / (2 * dp t w)‖ +
          ‖digamma (dm t w) - log (dm t w) + 1 / (2 * dm t w)‖ + ‖log (1 + η)‖ := norm_add₃_le
      have hyy : 0 ≤ |y| := abs_nonneg y
      have h3 : 2 * ‖η‖ ≤ 2 * (7 + |y|) ^ 2 / t ^ 2 := by
        calc 2 * ‖η‖ ≤ 2 * ((7 + |y|) ^ 2 / t ^ 2) := by gcongr
          _ = _ := by ring
      have h4 : (36 + 2 * (7 + |y|) ^ 2 + 2 * (7 + |y|)) / t ^ 2 ≤ 148 * (1 + |y|) ^ 2 / t ^ 2 := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; nlinarith only [hyy, mul_nonneg hyy hyy]
      have h5 : 18 / t ^ 2 + 18 / t ^ 2 + 2 * (7 + |y|) ^ 2 / t ^ 2 + 2 * (7 + |y|) / t ^ 2 =
          (36 + 2 * (7 + |y|) ^ 2 + 2 * (7 + |y|)) / t ^ 2 := by ring
      linarith only [n1, n2, hP, hM, hPd, hMd, hlog1, h3, hinv, h4, h5]
    have hf'eq : f' u = z * (digamma (dp t w) + digamma (dm t w) - 2 * Lt) := by
      simp only [hf', hw]; ring
    rw [hf'eq, norm_mul]
    calc ‖z‖ * ‖digamma (dp t w) + digamma (dm t w) - 2 * Lt‖
        ≤ (1 + |y|) * (148 * (1 + |y|) ^ 2 / t ^ 2) := by gcongr
      _ ≤ 150 * (1 + |y|) ^ 3 / t ^ 2 := by
          rw [show (1 + |y|) * (148 * (1 + |y|) ^ 2 / t ^ 2) = 148 * (1 + |y|) ^ 3 / t ^ 2 by ring]
          gcongr; norm_num
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  have hE : EfD t z = f 1 - f 0 := by
    simp only [hf, EfD]; push_cast; simp
    ring
  rw [hE]
  simpa using hmvt

end RamanujanTau.GoodSecondTerm
