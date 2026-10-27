/-
# The Bessel line integral

For `c > 0`, `y ≥ 0`:

  `∫_ℝ (c+it)^{−5/2} e^{(c+it) + y/(c+it)} dt = 2π Σ_m y^m/(m! Γ(m+5/2))`.

Let `g(x) = Σ_m y^m x^{m+3/2} e^{−cx}/(m! Γ(m+5/2))` for `x > 0` (and `0` for `x ≤ 0`). Its Fourier transform is
`Σ_m y^m s^{−m−5/2}/m! = s^{−5/2} e^{y/s}` with `s = c + 2πiξ` (`lap_eq`, termwise). Fourier inversion at
`x = 1` gives the identity.
-/
import RamanujanTau.Rademacher.Laplace

set_option autoImplicit false

namespace Rademacher
open Complex MeasureTheory Set Filter
open scoped Real Topology Nat FourierTransform

noncomputable section

/-- `y^m/(m! Γ(m+5/2))`. -/
def bco (y : ℝ) (m : ℕ) : ℝ := y ^ m / (m ! * Real.Gamma (m + 5 / 2))

lemma Gamma_pos (m : ℕ) : 0 < Real.Gamma (m + 5 / 2) := Real.Gamma_pos_of_pos (by positivity)

lemma bco_nonneg {y : ℝ} (hy : 0 ≤ y) (m : ℕ) : 0 ≤ bco y m := by
  unfold bco; have := Gamma_pos m; positivity

/-- the `m`-th term on `x > 0`. -/
def gterm (y c : ℝ) (m : ℕ) (x : ℝ) : ℂ := (bco y m : ℂ) * lapI (m + 5 / 2) c x

/-- `g`. -/
def gfun (y c : ℝ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator fun x => ∑' m, gterm y c m x

lemma beta_pos (m : ℕ) : (0 : ℝ) < m + 5 / 2 := by positivity

lemma integral_norm_lapI {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), ‖lapI β c x‖ = c ^ (-β) * Real.Gamma β := by
  have h := lap_real hβ hc
  have e : ∫ x in Ioi (0 : ℝ), ‖lapI β c x‖ = ∫ x in Ioi (0 : ℝ), x ^ (β - 1) * Real.exp (-(c * x)) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [norm_lapI hx]; simp
  rw [e]
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hc
  rw [h2, one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]

lemma bco_mul_Gamma (y : ℝ) (m : ℕ) : bco y m * Real.Gamma (m + 5 / 2) = y ^ m / m ! := by
  unfold bco; have := (Gamma_pos m).ne'; field_simp

lemma summable_bco_norm {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) :
    Summable fun m : ℕ => bco y m * (c ^ (-((m : ℝ) + 5 / 2)) * Real.Gamma (m + 5 / 2)) := by
  have h := (Real.summable_pow_div_factorial (y / c)).mul_left (c ^ (-(5 / 2 : ℝ)))
  refine h.congr fun m => ?_
  rw [show bco y m * (c ^ (-((m : ℝ) + 5 / 2)) * Real.Gamma (m + 5 / 2)) =
      (bco y m * Real.Gamma (m + 5 / 2)) * c ^ (-((m : ℝ) + 5 / 2)) by ring, bco_mul_Gamma,
    neg_add, Real.rpow_add hc, Real.rpow_neg hc.le (m : ℝ), Real.rpow_natCast, div_pow]
  field_simp

/-- `s^{−(m+5/2)} = s^{−5/2} (1/s)^m`. -/
lemma cpow_shift {s : ℂ} (hs : s ≠ 0) (m : ℕ) :
    s ^ (-(((m : ℝ) + 5 / 2 : ℝ) : ℂ)) = s ^ (-(5 / 2 : ℂ)) * (1 / s) ^ m := by
  rw [show (-(((m : ℝ) + 5 / 2 : ℝ) : ℂ)) = (-(5 / 2 : ℂ)) + (-(m : ℂ)) by push_cast; ring, cpow_add _ _ hs,
    cpow_neg s (m : ℂ), cpow_natCast, one_div, inv_pow]

/-- **the Fourier transform of `g`**. -/
lemma fourier_gfun {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) (ξ : ℝ) :
    𝓕 (gfun y c) ξ = ((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) * cexp (y / ((c : ℂ) + 2 * π * ξ * I)) := by
  set s : ℂ := (c : ℂ) + 2 * π * ξ * I with hsdef
  have hsre : s.re = c := by simp [hsdef]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, gfun]
  have hind : ∀ v : ℝ, cexp (↑(-2 * π * v * ξ) * I) * (Ioi (0 : ℝ)).indicator (fun x => ∑' m, gterm y c m x) v =
      (Ioi (0 : ℝ)).indicator (fun x => ∑' m, (bco y m : ℂ) * lapI (m + 5 / 2) s x) v := by
    intro v
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, ← tsum_mul_left]
      congr 1; funext m
      simp only [gterm, lapI]
      rw [mul_left_comm]
      congr 1
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      rw [hsdef]; push_cast; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
  simp only [hind]
  rw [integral_indicator measurableSet_Ioi]
  have hint : ∀ m : ℕ, Integrable (fun x => (bco y m : ℂ) * lapI (m + 5 / 2) s x) (volume.restrict (Ioi 0)) :=
    fun m => (integrable_lapI (beta_pos m) (by rw [hsre]; exact hc)).const_mul _
  have hnorm : ∀ m : ℕ, ∫ x in Ioi (0 : ℝ), ‖(bco y m : ℂ) * lapI (m + 5 / 2) s x‖ =
      bco y m * (c ^ (-((m : ℝ) + 5 / 2)) * Real.Gamma (m + 5 / 2)) := by
    intro m
    have e : ∀ x ∈ Ioi (0 : ℝ), ‖(bco y m : ℂ) * lapI (m + 5 / 2) s x‖ = bco y m * ‖lapI (m + 5 / 2) c x‖ := by
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bco_nonneg hy m), norm_lapI hx, norm_lapI hx, hsre]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, integral_norm_lapI (beta_pos m) hc]
  have hsum := integral_tsum_of_summable_integral_norm hint
    ((summable_bco_norm hy hc).congr fun m => (hnorm m).symm)
  rw [← hsum]
  -- each integral
  have hk : ∀ m : ℕ, ∫ x in Ioi (0 : ℝ), (bco y m : ℂ) * lapI (m + 5 / 2) s x =
      s ^ (-(5 / 2 : ℂ)) * ((y / s) ^ m / m !) := by
    intro m
    rw [integral_const_mul]
    have hl := lap_eq (beta_pos m) (by rw [hsre]; exact hc : 0 < s.re)
    rw [lap] at hl
    rw [hl, cpow_shift hs0 m, Complex.Gamma_ofReal]
    have hb : (bco y m : ℂ) * (Real.Gamma (m + 5 / 2) : ℂ) = (y : ℂ) ^ m / m ! := by
      have := bco_mul_Gamma y m; exact_mod_cast this
    rw [show (bco y m : ℂ) * (s ^ (-(5 / 2 : ℂ)) * (1 / s) ^ m * (Real.Gamma ((m : ℝ) + 5 / 2) : ℂ)) =
      s ^ (-(5 / 2 : ℂ)) * (1 / s) ^ m * ((bco y m : ℂ) * (Real.Gamma (m + 5 / 2) : ℂ)) by push_cast; ring, hb]
    rw [div_pow, one_pow, div_pow]
    field_simp
  simp only [hk]
  rw [tsum_mul_left]
  congr 1
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp (y / s)).tsum_eq

/-! ### integrability, continuity, inversion -/

lemma integrable_tsum_of {μ : Measure ℝ} {F : ℕ → ℝ → ℂ}
    (hmeas : AEStronglyMeasurable (fun a => ∑' i, F i a) μ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ := lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum fun i => (hF i).1.enorm
    _ = ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF i)]
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hs]
        exact ENNReal.ofReal_lt_top

lemma one_le_Gamma (m : ℕ) : 1 ≤ Real.Gamma (m + 5 / 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h := Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ∈ Ici 2 from Set.left_mem_Ici)
    (show (m : ℝ) + 5 / 2 ∈ Ici 2 by rw [Set.mem_Ici]; linarith) (by linarith)
  rwa [Real.Gamma_two] at h

lemma bco_le {y : ℝ} (hy : 0 ≤ y) (m : ℕ) : bco y m ≤ y ^ m / m ! := by
  unfold bco
  have h1 := one_le_Gamma m
  have h2 : (0 : ℝ) < m ! := by positivity
  rw [div_le_div_iff₀ (by positivity) h2]
  have hp := pow_nonneg hy m
  have : y ^ m * (m ! : ℝ) * 1 ≤ y ^ m * (m ! : ℝ) * Real.Gamma (m + 5 / 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

lemma norm_gterm_le {y c R : ℝ} (hy : 0 ≤ y) (hc : 0 < c) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) R) :
    ‖gterm y c m x‖ ≤ y ^ m / m ! * R ^ ((m : ℝ) + 3 / 2) := by
  rw [gterm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bco_nonneg hy m), norm_lapI hx.1]
  have he : Real.exp (-(c * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
  have hp : x ^ ((m : ℝ) + 5 / 2 - 1) ≤ R ^ ((m : ℝ) + 3 / 2) := by
    rw [show (m : ℝ) + 5 / 2 - 1 = m + 3 / 2 by ring]
    exact Real.rpow_le_rpow hx.1.le hx.2.le (by positivity)
  calc bco y m * (x ^ ((m : ℝ) + 5 / 2 - 1) * Real.exp (-(c * x)))
      ≤ y ^ m / m ! * (R ^ ((m : ℝ) + 3 / 2) * 1) := by
        have h0 : 0 ≤ x ^ ((m : ℝ) + 5 / 2 - 1) * Real.exp (-(c * x)) :=
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le
        have hR : 0 ≤ R := by linarith [hx.1, hx.2]
        calc bco y m * (x ^ ((m : ℝ) + 5 / 2 - 1) * Real.exp (-(c * x)))
            ≤ y ^ m / m ! * (x ^ ((m : ℝ) + 5 / 2 - 1) * Real.exp (-(c * x))) :=
              mul_le_mul_of_nonneg_right (bco_le hy m) h0
          _ ≤ y ^ m / m ! * (R ^ ((m : ℝ) + 3 / 2) * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg hR _))
                (by positivity)
    _ = _ := by ring

lemma summable_bound (y : ℝ) {R : ℝ} (hR : 0 < R) : Summable fun m : ℕ => y ^ m / m ! * R ^ ((m : ℝ) + 3 / 2) := by
  have h := (Real.summable_pow_div_factorial (R * y)).mul_left (R ^ (3 / 2 : ℝ))
  refine h.congr fun m => ?_
  rw [Real.rpow_add hR, Real.rpow_natCast, mul_pow]; ring

lemma continuousOn_gsum_R {y c R : ℝ} (hy : 0 ≤ y) (hc : 0 < c) (hR : 0 < R) :
    ContinuousOn (fun x => ∑' m, gterm y c m x) (Ioo 0 R) := by
  refine continuousOn_tsum (fun m => ?_) (summable_bound y hR) (fun m x hx => norm_gterm_le hy hc m hx)
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold gterm lapI
  exact continuousAt_const.mul ((continuousAt_ofReal_cpow_const _ _ (Or.inr hx.1.ne')).mul (by fun_prop))

lemma continuousOn_gsum {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) :
    ContinuousOn (fun x => ∑' m, gterm y c m x) (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have h := continuousOn_gsum_R hy hc (R := x + 1) (by linarith)
  exact (h.continuousAt (Ioo_mem_nhds hx' (by linarith))).continuousWithinAt

lemma integrable_gfun {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) : Integrable (gfun y c) := by
  rw [gfun, integrable_indicator_iff measurableSet_Ioi]
  have hint : ∀ m : ℕ, Integrable (gterm y c m) (volume.restrict (Ioi 0)) :=
    fun m => (integrable_lapI (beta_pos m) (by simpa using hc)).const_mul _
  refine integrable_tsum_of ((continuousOn_gsum hy hc).aestronglyMeasurable measurableSet_Ioi) hint ?_
  refine (summable_bco_norm hy hc).congr fun m => ?_
  have e : ∀ x ∈ Ioi (0 : ℝ), ‖gterm y c m x‖ = bco y m * ‖lapI (m + 5 / 2) c x‖ := by
    intro x hx
    rw [gterm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bco_nonneg hy m)]
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, integral_norm_lapI (beta_pos m) hc]

lemma gfun_one (y c : ℝ) : gfun y c 1 = cexp (-(c : ℂ)) * ∑' m, (bco y m : ℂ) := by
  rw [gfun, Set.indicator_of_mem (Set.mem_Ioi.mpr (one_pos : (0 : ℝ) < 1)), ← tsum_mul_left]
  congr 1; funext m
  simp [gterm, lapI]; ring

lemma continuousAt_gfun {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) : ContinuousAt (gfun y c) 1 := by
  have h := (continuousOn_gsum hy hc).continuousAt (Ioi_mem_nhds one_pos)
  refine h.congr ?_
  filter_upwards [Ioi_mem_nhds one_pos] with x hx
  rw [gfun, Set.indicator_of_mem hx]

/-- the Fourier transform is `O((1+|ξ|)^{−5/2})`. -/
lemma integrable_fourier_gfun {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) : Integrable (𝓕 (gfun y c)) := by
  have hf : 𝓕 (gfun y c) = fun ξ : ℝ =>
      ((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) * cexp (y / ((c : ℂ) + 2 * π * ξ * I)) :=
    funext (fourier_gfun hy hc)
  rw [hf]
  set κ : ℝ := min c 1 with hκ
  have hκ0 : 0 < κ := lt_min hc one_pos
  have hbound : ∀ ξ : ℝ, ‖((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) * cexp (y / ((c : ℂ) + 2 * π * ξ * I))‖ ≤
      (κ / 2) ^ (-(5 / 2 : ℝ)) * Real.exp (y / c) * (1 + ‖ξ‖) ^ (-(5 / 2 : ℝ)) := by
    intro ξ
    set s : ℂ := (c : ℂ) + 2 * π * ξ * I with hs
    have hsre : s.re = c := by simp [hs]
    have hsim : s.im = 2 * π * ξ := by simp [hs]
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
    have hn2 : ‖s‖ ^ 2 = c ^ 2 + (2 * π * ξ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]; ring
    have hns : κ / 2 * (1 + ‖ξ‖) ≤ ‖s‖ := by
      have hπ := Real.pi_gt_three
      have h1 : κ ≤ c := min_le_left _ _
      have h2 : κ ≤ 1 := min_le_right _ _
      have hξ : ‖ξ‖ = |ξ| := Real.norm_eq_abs ξ
      have hsq : (κ / 2 * (1 + ‖ξ‖)) ^ 2 ≤ ‖s‖ ^ 2 := by
        rw [hn2, hξ]
        have habs : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
        have a1 : (1 + |ξ|) ^ 2 ≤ 2 * (1 + ξ ^ 2) := by nlinarith [sq_nonneg (|ξ| - 1)]
        have a2 : κ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hκ0.le h1 2
        have a3 : κ ^ 2 ≤ 1 := by nlinarith
        have a4 : κ ^ 2 * ξ ^ 2 ≤ (2 * π * ξ) ^ 2 := by
          have : (2 * π * ξ) ^ 2 = (4 * π ^ 2) * ξ ^ 2 := by ring
          rw [this]
          have h4 : κ ^ 2 ≤ 4 * π ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right h4 (sq_nonneg ξ)
        have a5 : (κ / 2 * (1 + |ξ|)) ^ 2 = κ ^ 2 / 4 * (1 + |ξ|) ^ 2 := by ring
        rw [a5]
        have a6 : κ ^ 2 / 4 * (1 + |ξ|) ^ 2 ≤ κ ^ 2 / 4 * (2 * (1 + ξ ^ 2)) :=
          mul_le_mul_of_nonneg_left a1 (by positivity)
        nlinarith [sq_nonneg (2 * π * ξ)]
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq
    rw [norm_mul, norm_cpow_of_ne_zero hs0, norm_exp]
    have hre : (y / s).re ≤ y / c := by
      rw [div_re, show ((y : ℂ)).re = y by simp, show ((y : ℂ)).im = 0 by simp, zero_mul, zero_div, add_zero,
        Complex.normSq_eq_norm_sq, hsre]
      have : c ^ 2 ≤ ‖s‖ ^ 2 := by rw [hn2]; nlinarith [sq_nonneg (2 * π * ξ)]
      rw [div_le_div_iff₀ (by positivity) hc]
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hy hc.le)]
    simp only [neg_re, neg_im, div_ofNat_re, div_ofNat_im, re_ofNat, im_ofNat, zero_div, neg_zero, mul_zero,
      Real.exp_zero, div_one]
    have hp : ‖s‖ ^ (-(5 / 2 : ℝ)) ≤ (κ / 2 * (1 + ‖ξ‖)) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hns (by norm_num)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hp
    calc ‖s‖ ^ (-(5 / 2 : ℝ)) * Real.exp (y / s).re ≤ ((κ / 2) ^ (-(5 / 2 : ℝ)) * (1 + ‖ξ‖) ^ (-(5 / 2 : ℝ))) *
          Real.exp (y / c) := by gcongr
      _ = _ := by ring
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (r := 5 / 2) (by simp; norm_num)).const_mul
    ((κ / 2) ^ (-(5 / 2 : ℝ)) * Real.exp (y / c))) ?_ (Eventually.of_forall hbound)
  refine Continuous.aestronglyMeasurable ?_
  have hne : ∀ ξ : ℝ, (c : ℂ) + 2 * π * ξ * I ≠ 0 := fun ξ h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hslit : ∀ ξ : ℝ, (c : ℂ) + 2 * π * ξ * I ∈ slitPlane := fun ξ => mem_slitPlane_iff.mpr (Or.inl (by simpa))
  refine Continuous.mul ?_ ?_
  · exact continuous_iff_continuousAt.mpr fun ξ =>
      ContinuousAt.cpow (by fun_prop) continuousAt_const (hslit ξ)
  · exact (continuous_const.div (by fun_prop) hne).cexp

/-- **the Bessel line integral**. -/
theorem bessel_line {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) :
    ∫ t : ℝ, ((c : ℂ) + t * I) ^ (-(5 / 2 : ℂ)) * cexp (((c : ℂ) + t * I) + y / ((c : ℂ) + t * I)) =
      2 * π * ∑' m, (bco y m : ℂ) := by
  have hinv := (integrable_gfun hy hc).fourierInv_fourier_eq (integrable_fourier_gfun hy hc) (continuousAt_gfun hy hc)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, gfun_one] at hinv
  simp only [smul_eq_mul, fourier_gfun hy hc] at hinv
  -- `∫ e^{2πiξ} s^{−5/2} e^{y/s} dξ = e^{−c} Σ`
  have hξ : ∫ ξ : ℝ, ((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) *
      cexp (((c : ℂ) + 2 * π * ξ * I) + y / ((c : ℂ) + 2 * π * ξ * I)) = ∑' m, (bco y m : ℂ) := by
    have e : ∀ ξ : ℝ, ((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) *
        cexp (((c : ℂ) + 2 * π * ξ * I) + y / ((c : ℂ) + 2 * π * ξ * I)) =
        cexp (c : ℂ) * (cexp (↑(-2 * π * ξ * -1) * I) * (((c : ℂ) + 2 * π * ξ * I) ^ (-(5 / 2 : ℂ)) *
          cexp (y / ((c : ℂ) + 2 * π * ξ * I)))) := by
      intro ξ
      rw [Complex.exp_add, Complex.exp_add]
      push_cast
      ring_nf
    simp only [e]
    rw [integral_const_mul, hinv, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hcv := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => ((c : ℂ) + t * I) ^ (-(5 / 2 : ℂ)) * cexp (((c : ℂ) + t * I) + y / ((c : ℂ) + t * I))) (2 * π)
  simp only at hcv
  have e2 : ∀ ξ : ℝ, ((c : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) = (c : ℂ) + 2 * π * ξ * I := fun ξ => by push_cast; ring
  simp only [e2, hξ] at hcv
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), Complex.real_smul] at hcv
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [hcv, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ hπ, one_mul]

end

end Rademacher
