/-
# Stirling input for `R_t(z)`: digamma and the logarithm of `Γ(s₊/2)Γ(s₋/2)`

* `norm_digamma_sub_log_le`: `‖ψ(s) − log s‖ ≤ 40/(Re s + |Im s| − 1)` (Re s > 0).
* `log_pair`: `log a₊ + log a₋ = 2 log(t/2) + log(1+η)`, `a± = (1/2+w±it)/2`, `η = (1/2+w)²/t²`.
* `norm_E_le`: with `E = Σ± [log Γ(a±(z)) − log Γ(a±(0))] − z log(t/2)` (Weierstrass `LG`),
  `‖E‖ ≤ 200(1+|y|)²/t` on `z = c+iy`, `1/2 < c ≤ 1`, `|y| ≤ t/4`, `t ≥ 8`.
-/
import RamanujanTau.ZeroCountRvM.DigammaAsymp
import RamanujanTau.ZetaAFE.Split

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZeroCountRvM

/-- `‖ψ(s) − log s‖ ≤ 40/(Re s + |Im s| − 1)`. -/
theorem norm_digamma_sub_log_le {s : ℂ} (hs : 0 < s.re) (h1 : 1 < s.re + |s.im|) :
    ‖digamma s - log s‖ ≤ 40 / (s.re + |s.im| - 1) := by
  rw [digamma_eq_log_add hs, add_sub_cancel_left]
  set a : ℝ := s.re + |s.im| with ha
  have hb : ∀ j : ℕ, ‖et s j‖ ≤ 40 * (1 / (a + j) ^ 2) := by
    intro j
    refine (norm_et_le hs j).trans ?_
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hn2 : ‖s + j‖ ^ 2 = (s.re + j) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hpos : 0 < ‖s + j‖ := by
      rw [norm_pos_iff]; intro h
      have := congrArg Complex.re h; simp at this; linarith
    rw [norm_div, norm_one, div_pow, one_pow, hn2]
    have hyy : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
    have hkey : (a + j) ^ 2 ≤ 2 * ((s.re + j) ^ 2 + s.im ^ 2) := by
      rw [ha]; nlinarith [sq_nonneg (s.re + j - |s.im|), abs_nonneg s.im]
    have hp1 : 0 < (s.re + (j : ℝ)) ^ 2 + s.im ^ 2 := by positivity
    have hp2 : 0 < (a + j) ^ 2 := by
      have : 0 < a + j := by linarith
      positivity
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ hp1 hp2]
    nlinarith
  obtain ⟨hsum, hle⟩ := tsum_inv_sq_le h1
  have := tsum_of_norm_bounded (hsum.mul_left 40) hb
  calc ‖∑' j, et s j‖ ≤ 40 * ∑' j : ℕ, 1 / (a + j) ^ 2 := this
    _ ≤ 40 * (1 / (a - 1)) := by gcongr
    _ = 40 / (a - 1) := by ring

/-- `a₊(w) = (1/2 + w + it)/2`. -/
noncomputable def aP (t : ℝ) (w : ℂ) : ℂ := sp t w / 2
/-- `a₋(w) = (1/2 + w − it)/2`. -/
noncomputable def aM (t : ℝ) (w : ℂ) : ℂ := sm t w / 2

lemma re_aP (t : ℝ) (w : ℂ) : (aP t w).re = (1 / 2 + w.re) / 2 := by simp [aP, sp]
lemma re_aM (t : ℝ) (w : ℂ) : (aM t w).re = (1 / 2 + w.re) / 2 := by simp [aM, sm]
lemma im_aP (t : ℝ) (w : ℂ) : (aP t w).im = (w.im + t) / 2 := by simp [aP, sp]
lemma im_aM (t : ℝ) (w : ℂ) : (aM t w).im = (w.im - t) / 2 := by simp [aM, sm]

lemma arg_lt_of_re_pos {a : ℂ} (h : 0 < a.re) : |arg a| < Real.pi / 2 :=
  abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)

lemma ne_zero_of_re_pos {a : ℂ} (h : 0 < a.re) : a ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

/-- `log a₊ + log a₋ = 2 log(t/2) + log(1 + η)`. -/
lemma log_pair {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 0 ≤ w.re)
    (hη : ‖(1 / 2 + w) ^ 2 / (t : ℂ) ^ 2‖ < 1) :
    log (aP t w) + log (aM t w) =
      2 * (Real.log (t / 2) : ℂ) + log (1 + (1 / 2 + w) ^ 2 / (t : ℂ) ^ 2) := by
  have hp : 0 < (aP t w).re := by rw [re_aP]; linarith
  have hm : 0 < (aM t w).re := by rw [re_aM]; linarith
  have h1 : log (aP t w * aM t w) = log (aP t w) + log (aM t w) := by
    rw [log_mul_eq_add_log_iff (ne_zero_of_re_pos hp) (ne_zero_of_re_pos hm)]
    have a1 := abs_lt.mp (arg_lt_of_re_pos hp)
    have a2 := abs_lt.mp (arg_lt_of_re_pos hm)
    constructor <;> linarith
  have hη0 : 1 + (1 / 2 + w) ^ 2 / (t : ℂ) ^ 2 ≠ 0 := by
    intro h
    have : (1 / 2 + w) ^ 2 / (t : ℂ) ^ 2 = -1 := by linear_combination h
    rw [this] at hη; simp at hη
  have h2 : aP t w * aM t w = (((t / 2) ^ 2 : ℝ) : ℂ) * (1 + (1 / 2 + w) ^ 2 / (t : ℂ) ^ 2) := by
    unfold aP aM sp sm
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
    ring_nf
    rw [I_sq]; ring
  rw [← h1, h2, log_ofReal_mul (by positivity) hη0, Real.log_pow]
  push_cast; ring

/-- `‖log(1+η)‖ ≤ 2‖η‖` for `‖η‖ ≤ 1/2`. -/
lemma norm_log_one_add_le {η : ℂ} (h : ‖η‖ ≤ 1 / 2) : ‖log (1 + η)‖ ≤ 2 * ‖η‖ := by
  have h1 := norm_log_one_add_sub_self_le (z := η) (by linarith)
  have h2 : ‖η‖ ^ 2 * (1 - ‖η‖)⁻¹ / 2 ≤ ‖η‖ := by
    have hn := norm_nonneg η
    have h3 : (1 - ‖η‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖η‖ ^ 2 * (1 - ‖η‖)⁻¹ / 2 ≤ ‖η‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖η‖ * ‖η‖ := by ring
      _ ≤ ‖η‖ * 1 := by gcongr; linarith
      _ = ‖η‖ := by ring
  have := norm_sub_norm_le (log (1 + η)) η
  linarith

lemma hasDerivAt_LG_digamma {s : ℂ} (hs : 0 < s.re) : HasDerivAt LG (digamma s) s := by
  rw [digamma_eq_series hs]; exact hasDerivAt_LG hs

/-- `E_t(z) = LG(a₊(z)) − LG(a₊(0)) + LG(a₋(z)) − LG(a₋(0)) − z log(t/2)`. -/
noncomputable def Efun (t : ℝ) (z : ℂ) : ℂ :=
  LG (aP t z) - LG (aP t 0) + LG (aM t z) - LG (aM t 0) - z * (Real.log (t / 2) : ℂ)

lemma hasDerivAt_aP (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => aP t ((u : ℂ) * z)) (z / 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).mul_const z
  have h2 := ((h1.const_add (1 / 2 : ℂ)).add_const ((t : ℂ) * I)).div_const 2
  convert h2 using 1

lemma hasDerivAt_aM (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => aM t ((u : ℂ) * z)) (z / 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).mul_const z
  have h2 := ((h1.const_add (1 / 2 : ℂ)).sub_const ((t : ℂ) * I)).div_const 2
  convert h2 using 1

/-- The key Stirling estimate: `‖E_t(c+iy)‖ ≤ 200(1+|y|)²/t` for `|y| ≤ t/4`, `t ≥ 8`. -/
theorem norm_E_le {t c y : ℝ} (ht : 8 ≤ t) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hy : |y| ≤ t / 4) :
    ‖Efun t ((c : ℂ) + y * I)‖ ≤ 200 * (1 + |y|) ^ 2 / t := by
  set z : ℂ := (c : ℂ) + y * I with hz
  have ht0 : 0 < t := by linarith
  have hzn : ‖z‖ ≤ 1 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    simp [hz, abs_of_nonneg hc]; linarith
  set L₂ : ℂ := (Real.log (t / 2) : ℂ) with hL₂
  set f : ℝ → ℂ := fun u => LG (aP t ((u : ℂ) * z)) + LG (aM t ((u : ℂ) * z)) - (u : ℂ) * z * L₂
    with hf
  set f' : ℝ → ℂ := fun u => digamma (aP t ((u : ℂ) * z)) * (z / 2) +
    digamma (aM t ((u : ℂ) * z)) * (z / 2) - z * L₂ with hf'
  -- geometry along the segment
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
  have hreP : ∀ u ∈ Icc (0 : ℝ) 1, 0 < (aP t ((u : ℂ) * z)).re := by
    intro u hu; rw [re_aP]; linarith [(hgeo u hu).1]
  have hreM : ∀ u ∈ Icc (0 : ℝ) 1, 0 < (aM t ((u : ℂ) * z)).re := by
    intro u hu; rw [re_aM]; linarith [(hgeo u hu).1]
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' u) (Icc 0 1) u := by
    intro u hu
    have h1 := (hasDerivAt_LG_digamma (hreP u hu)).comp u (hasDerivAt_aP t z u)
    have h2 := (hasDerivAt_LG_digamma (hreM u hu)).comp u (hasDerivAt_aM t z u)
    have h3 : HasDerivAt (fun u : ℝ => (u : ℂ) * z * L₂) (z * L₂) u := by
      simpa using (((hasDerivAt_id u).ofReal_comp).mul_const z).mul_const L₂
    exact ((h1.add h2).sub h3).hasDerivWithinAt
  -- the derivative bound
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1, ‖f' u‖ ≤ 200 * (1 + |y|) ^ 2 / t := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hu
    obtain ⟨g1, g2, g3, g4⟩ := hgeo u hu'
    set w : ℂ := (u : ℂ) * z with hw
    have hP := norm_digamma_sub_log_le (s := aP t w) (hreP u hu') (by
      rw [re_aP, im_aP]
      have : t * (3 / 8) ≤ |(w.im + t) / 2| := by
        rw [abs_div, abs_two, le_div_iff₀ (by norm_num)]
        have := abs_le.mp g3; have := abs_le.mp hy
        rw [abs_of_pos (by linarith)]; linarith
      linarith)
    have hM := norm_digamma_sub_log_le (s := aM t w) (hreM u hu') (by
      rw [re_aM, im_aM]
      have : t * (3 / 8) ≤ |(w.im - t) / 2| := by
        rw [abs_div, abs_two, le_div_iff₀ (by norm_num)]
        have := abs_le.mp g3; have := abs_le.mp hy
        rw [abs_of_neg (by linarith)]; linarith
      linarith)
    have hPd : 40 / ((aP t w).re + |(aP t w).im| - 1) ≤ 160 / t := by
      rw [re_aP, im_aP]
      have : t * (3 / 8) ≤ |(w.im + t) / 2| := by
        rw [abs_div, abs_two, le_div_iff₀ (by norm_num)]
        have := abs_le.mp g3; have := abs_le.mp hy
        rw [abs_of_pos (by linarith)]; linarith
      rw [div_le_div_iff₀ (by linarith) ht0]; nlinarith
    have hMd : 40 / ((aM t w).re + |(aM t w).im| - 1) ≤ 160 / t := by
      rw [re_aM, im_aM]
      have : t * (3 / 8) ≤ |(w.im - t) / 2| := by
        rw [abs_div, abs_two, le_div_iff₀ (by norm_num)]
        have := abs_le.mp g3; have := abs_le.mp hy
        rw [abs_of_neg (by linarith)]; linarith
      rw [div_le_div_iff₀ (by linarith) ht0]; nlinarith
    -- η
    set η : ℂ := (1 / 2 + w) ^ 2 / (t : ℂ) ^ 2 with hη
    have hwn : ‖1 / 2 + w‖ ≤ 3 / 2 + |y| := by
      refine (norm_add_le _ _).trans ?_; norm_num; linarith
    have hηn : ‖η‖ ≤ (3 / 2 + |y|) ^ 2 / t ^ 2 := by
      rw [hη, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      gcongr
    have hr : (3 / 2 + |y|) / t ≤ 7 / 16 := by
      rw [div_le_iff₀ ht0]; linarith
    have hηn' : ‖η‖ ≤ 7 / 16 * ((3 / 2 + |y|) / t) := by
      refine hηn.trans (le_of_eq_of_le (by ring : (3 / 2 + |y|) ^ 2 / t ^ 2 =
        ((3 / 2 + |y|) / t) * ((3 / 2 + |y|) / t)) ?_)
      gcongr
    have hηhalf : ‖η‖ ≤ 1 / 2 := by
      have : 7 / 16 * ((3 / 2 + |y|) / t) ≤ 7 / 16 * (7 / 16) := by gcongr
      linarith
    have hlog := log_pair ht0 g1 (by rw [← hη]; linarith)
    rw [← hη] at hlog
    have hlog1 := norm_log_one_add_le hηhalf
    -- assemble
    have hsum : digamma (aP t w) + digamma (aM t w) - 2 * L₂ =
        (digamma (aP t w) - log (aP t w)) + (digamma (aM t w) - log (aM t w)) + log (1 + η) := by
      rw [hL₂]; linear_combination hlog
    have hsn : ‖digamma (aP t w) + digamma (aM t w) - 2 * L₂‖ ≤ 400 * (1 + |y|) / t := by
      rw [hsum]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      have : 2 * ‖η‖ ≤ 2 * (3 / 2 + |y|) / t := by
        have := hηn'
        have h0 : 0 ≤ (3 / 2 + |y|) / t := by positivity
        rw [mul_div_assoc]; nlinarith
      calc ‖digamma (aP t w) - log (aP t w)‖ + ‖digamma (aM t w) - log (aM t w)‖ + ‖log (1 + η)‖
          ≤ 160 / t + 160 / t + 2 * (3 / 2 + |y|) / t := by linarith
        _ = (323 + 2 * |y|) / t := by ring
        _ ≤ 400 * (1 + |y|) / t := by
            rw [div_le_div_iff_of_pos_right ht0]
            nlinarith [abs_nonneg y]
    have hf'eq : f' u = z / 2 * (digamma (aP t w) + digamma (aM t w) - 2 * L₂) := by
      simp only [hf', hw]; ring
    rw [hf'eq, norm_mul, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    calc ‖z‖ / 2 * ‖digamma (aP t w) + digamma (aM t w) - 2 * L₂‖
        ≤ (1 + |y|) / 2 * (400 * (1 + |y|) / t) := by gcongr
      _ = 200 * (1 + |y|) ^ 2 / t := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  have hE : Efun t z = f 1 - f 0 := by
    simp only [hf, Efun]; push_cast; simp
    ring
  rw [hE]
  simpa using hmvt

end RamanujanTau.ZetaAFE
