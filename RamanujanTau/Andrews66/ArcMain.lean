/-
# Andrews 1966, M-a (second half): the main term on the arc at `h/K`, for every `K`

On the arc at `h/K` of the line `Im τ = y`, write `τ = h/K + φ + iy`, `z = K(y − iφ)` (so
`q = e^{2πiτ} = e^{2πi(h+iz)/K}`). After the transformation of `b`, the main integrand is

  `m(φ) = z^{−1/2} e^{π(1/z − z)/(12K)} e^{2πnz/K}`       (`mI`).

* `mI_eq`: with `ζ = β/z`, `β = π/(12K)`: `m(φ) dφ = (√β/(iK)) · h(ζ) dζ`, `h(ζ) = ζ^{−3/2} e^{ζ + Y/ζ}`,
  `Y = π²(24n−1)/(144K²)`.
* `core_chord`: the symmetric segment `|φ| ≤ θ₀` becomes an arc of `|ζ − A/2| = A/2` (`A = β/(Ky)`) from `c − is`
  to `c + is`; a primitive on the disc `|ζ − A| < A − c/4` (inside `Re ζ > 0`) replaces it by its chord.
* `tail_bound'`: completing the chord `Re ζ = c, |v| ≤ s` to the full line costs `≤ 4e^{c + Yc/(c²+s²)}/√s`.
* `core_eval`: `‖∫_{−θ₀}^{θ₀} m − M_K(n)‖ ≤ (√β/K)·4e^{c + Yc/(c²+s²)}/√s`, where
  `M_K(n) = √48/(√K √(24n−1)) · sinh(π√(24n−1)/(6K))` (`MK`) is the full-line (Bessel) value; for `K = 2k`
  this is Andrews' `π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k`.
-/
import RamanujanTau.Andrews66.Main

set_option autoImplicit false

namespace Andrews66
open Complex Filter Metric MeasureTheory Set intervalIntegral
open scoped Real Topology

noncomputable section

/-- `z(φ) = K(y − iφ)`. -/
def zK (K : ℕ) (y φ : ℝ) : ℂ := (K : ℂ) * ((y : ℂ) - φ * I)

lemma zK_re (K : ℕ) (y φ : ℝ) : (zK K y φ).re = K * y := by simp [zK]

lemma zK_im (K : ℕ) (y φ : ℝ) : (zK K y φ).im = -(K * φ) := by simp [zK]

lemma normSq_zK (K : ℕ) (y φ : ℝ) : normSq (zK K y φ) = (K : ℝ) ^ 2 * (y ^ 2 + φ ^ 2) := by
  rw [normSq_apply, zK_re, zK_im]; ring

lemma zK_re_pos {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (φ : ℝ) : 0 < (zK K y φ).re := by
  rw [zK_re]; have : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

lemma zK_ne {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (φ : ℝ) : zK K y φ ≠ 0 := fun h => by
  have := zK_re_pos hK hy φ; rw [h] at this; simp at this

lemma hasDerivAt_zK (K : ℕ) (y φ : ℝ) : HasDerivAt (zK K y) (-(K : ℂ) * I) φ := by
  have h1 : HasDerivAt (fun φ : ℝ => (φ : ℂ) * I) I φ := by
    simpa using ((hasDerivAt_id (φ : ℂ)).comp_ofReal).mul_const I
  have := (h1.const_sub (y : ℂ)).const_mul (K : ℂ)
  convert this using 1
  ring

/-- `β = π/(12K)`. -/
def βK (K : ℕ) : ℝ := π / (12 * K)

/-- `Y = π²(24n − 1)/(144K²)`. -/
def YK (K n : ℕ) : ℝ := π ^ 2 * (24 * n - 1) / (144 * K ^ 2)

lemma βK_pos {K : ℕ} (hK : 0 < K) : 0 < βK K := by
  unfold βK; have : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

lemma YK_pos {K n : ℕ} (hK : 0 < K) (hn : 1 ≤ n) : 0 < YK K n := by
  unfold YK
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < 24 * n - 1 := by linarith
  positivity

/-- **the main integrand** on the arc. -/
def mI (K n : ℕ) (y φ : ℝ) : ℂ :=
  1 / Complex.sqrt (zK K y φ) * cexp (π * (1 / zK K y φ - zK K y φ) / (12 * K)) *
    cexp (2 * π * n * zK K y φ / K)

/-- `ζ(φ) = β/z(φ)`. -/
def zetaK (K : ℕ) (y φ : ℝ) : ℂ := (βK K : ℂ) / zK K y φ

lemma hasDerivAt_zetaK {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (φ : ℝ) :
    HasDerivAt (zetaK K y) ((βK K : ℂ) * ((K : ℂ) * I) / zK K y φ ^ 2) φ := by
  have h3 := (hasDerivAt_inv (zK_ne hK hy φ)).comp φ (hasDerivAt_zK K y φ)
  have h4 := h3.const_mul (βK K : ℂ)
  convert h4 using 1
  try ring

/-- **the substitution `ζ = β/z`**. -/
lemma mI_eq {K : ℕ} (hK : 0 < K) (n : ℕ) {y : ℝ} (hy : 0 < y) (φ : ℝ) :
    mI K n y φ = ((√(βK K) : ℝ) : ℂ) / (I * K) *
      (hfun (YK K n) (zetaK K y φ) * ((βK K : ℂ) * ((K : ℂ) * I) / zK K y φ ^ 2)) := by
  set z := zK K y φ with hzdef
  have hz0 : z ≠ 0 := zK_ne hK hy φ
  have hzre : 0 < z.re := zK_re_pos hK hy φ
  have hb := βK_pos hK
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hLz : z = cexp (log z) := (exp_log hz0).symm
  have hLb : ((βK K : ℝ) : ℂ) = cexp (Real.log (βK K)) := by rw [← ofReal_exp, Real.exp_log hb]
  have hlogζ : log ((βK K : ℂ) / z) = Real.log (βK K) - log z := by
    rw [div_eq_mul_inv, log_ofReal_mul hb (inv_ne_zero hz0), log_inv _ (arg_ne_pi_of_re_pos hzre)]
    ring
  have hζ0 : (βK K : ℂ) / z ≠ 0 := div_ne_zero (by exact_mod_cast hb.ne') hz0
  have hsq : ((√(βK K) : ℝ) : ℂ) = cexp (Real.log (βK K) / 2) := by rw [sqrt_cexp hb]
  have hsz : Complex.sqrt z = cexp (log z / 2) := sqrt_eq_exp hz0
  have hE : π * (1 / z - z) / (12 * K) + 2 * π * n * z / K =
      (βK K : ℂ) / z + (YK K n : ℂ) / ((βK K : ℂ) / z) := by
    unfold βK YK; push_cast; field_simp; ring
  unfold mI hfun zetaK
  rw [← hzdef, mul_assoc (1 / Complex.sqrt z), ← Complex.exp_add, hE, cpow_def_of_ne_zero hζ0, hlogζ, hsq, hsz]
  set E : ℂ := (βK K : ℂ) / z + (YK K n : ℂ) / ((βK K : ℂ) / z)
  set Lb : ℂ := (Real.log (βK K) : ℂ)
  set Lz : ℂ := log z
  have hz2 : z ^ 2 = cexp (2 * Lz) := by
    rw [show (2 : ℂ) * Lz = Lz + Lz by ring, Complex.exp_add, ← hLz]; ring
  rw [hLb, hz2]
  clear_value E Lb Lz
  have e1 : cexp (Lb / 2) / (I * K) * (cexp ((Lb - Lz) * -(3 / 2)) * cexp E * (cexp Lb * (K * I) / cexp (2 * Lz)))
      = cexp (Lb / 2 + (Lb - Lz) * -(3 / 2) + E + Lb - 2 * Lz) := by
    have hIK : (I * K : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hK0
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_add]
    field_simp
    try ring
  rw [e1, one_div, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-! ### arc → chord -/

/-- the chord abscissa `c = βy/(K(y²+θ₀²))`. -/
def cK (K : ℕ) (y θ₀ : ℝ) : ℝ := βK K * y / (K * (y ^ 2 + θ₀ ^ 2))
/-- the chord half-height `s = βθ₀/(K(y²+θ₀²))`. -/
def sK (K : ℕ) (y θ₀ : ℝ) : ℝ := βK K * θ₀ / (K * (y ^ 2 + θ₀ ^ 2))
/-- the diameter `A = β/(Ky)` of the circle. -/
def AK (K : ℕ) (y : ℝ) : ℝ := βK K / (K * y)

lemma zetaK_re (K : ℕ) (y φ : ℝ) : (zetaK K y φ).re = βK K * y / (K * (y ^ 2 + φ ^ 2)) := by
  unfold zetaK; rw [div_re, normSq_zK]; simp [zK]; try field_simp

lemma zetaK_im (K : ℕ) (y φ : ℝ) : (zetaK K y φ).im = βK K * φ / (K * (y ^ 2 + φ ^ 2)) := by
  unfold zetaK; rw [div_im, normSq_zK]; simp [zK]; try field_simp

lemma normSq_zetaK {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (φ : ℝ) :
    normSq (zetaK K y φ) = AK K y * (zetaK K y φ).re := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  rw [normSq_apply, zetaK_re, zetaK_im, AK]
  have : 0 < y ^ 2 + φ ^ 2 := by positivity
  field_simp

/-- membership in the disc `|ζ − A| < A − c/4`. -/
lemma mem_discA {A c : ℝ} (hc : 0 < c) (hcA : c ≤ A) {ζ : ℂ} (hre : c ≤ ζ.re) (hn : normSq ζ ≤ A * ζ.re) :
    ζ ∈ ball ((A : ℝ) : ℂ) (A - c / 4) := by
  rw [mem_ball, dist_eq_norm]
  have hr : 0 < A - c / 4 := by linarith
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  rw [normSq_apply] at hn
  nlinarith

lemma re_pos_of_discA {A c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ ∈ ball ((A : ℝ) : ℂ) (A - c / 4)) : 0 < ζ.re := by
  rw [mem_ball, dist_eq_norm] at hζ
  have h := Complex.abs_re_le_norm (ζ - (A : ℂ))
  rw [sub_re, ofReal_re] at h
  have := neg_abs_le (ζ.re - A)
  linarith

lemma cK_pos {K : ℕ} (hK : 0 < K) {y θ₀ : ℝ} (hy : 0 < y) : 0 < cK K y θ₀ := by
  unfold cK; have := βK_pos hK; have : (0 : ℝ) < K := by exact_mod_cast hK
  have : 0 < y ^ 2 + θ₀ ^ 2 := by positivity
  positivity

lemma sK_pos {K : ℕ} (hK : 0 < K) {y θ₀ : ℝ} (hy : 0 < y) (hθ : 0 < θ₀) : 0 < sK K y θ₀ := by
  unfold sK; have := βK_pos hK; have : (0 : ℝ) < K := by exact_mod_cast hK
  have : 0 < y ^ 2 + θ₀ ^ 2 := by positivity
  positivity

lemma cK_le_AK {K : ℕ} (hK : 0 < K) {y θ₀ : ℝ} (hy : 0 < y) : cK K y θ₀ ≤ AK K y := by
  unfold cK AK
  have := βK_pos hK; have : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ βK K * y * K * θ₀ ^ 2 := by positivity
  nlinarith

lemma cs_sq {K : ℕ} (hK : 0 < K) {y θ₀ : ℝ} (hy : 0 < y) :
    cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2 = AK K y * cK K y θ₀ := by
  unfold cK sK AK
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have : 0 < y ^ 2 + θ₀ ^ 2 := by positivity
  field_simp

lemma zetaK_pm {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (θ₀ : ℝ) :
    zetaK K y θ₀ = (cK K y θ₀ : ℂ) + (sK K y θ₀ : ℂ) * I ∧
    zetaK K y (-θ₀) = (cK K y θ₀ : ℂ) + ((-sK K y θ₀ : ℝ) : ℂ) * I := by
  constructor <;> apply Complex.ext <;>
    simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      zero_add, add_zero, zetaK_re, zetaK_im, cK, sK] <;> ring

/-- **arc → chord**: `∫_{−θ₀}^{θ₀} m(φ) dφ = (√β/K) ∫_{−s}^{s} h(c + iv) dv`. -/
theorem core_chord {K : ℕ} (hK : 0 < K) (n : ℕ) {y θ₀ : ℝ} (hy : 0 < y) (hθ : 0 < θ₀) :
    ∫ φ in (-θ₀)..θ₀, mI K n y φ =
      ((√(βK K) : ℝ) : ℂ) / K * ∫ v in (-sK K y θ₀)..sK K y θ₀,
        hfun (YK K n) ((cK K y θ₀ : ℂ) + v * I) := by
  set c := cK K y θ₀ with hcdef
  set s := sK K y θ₀ with hsdef
  set A := AK K y with hAdef
  have hc0 : 0 < c := cK_pos hK hy
  have hs0 : 0 < s := sK_pos hK hy hθ
  have hcA : c ≤ A := cK_le_AK hK hy
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  set U := ball ((A : ℝ) : ℂ) (A - c / 4)
  have hdiff : DifferentiableOn ℂ (hfun (YK K n)) U := fun ζ hζ =>
    (differentiableAt_hfun _ (re_pos_of_discA hc0 hζ)).differentiableWithinAt
  obtain ⟨P, hP⟩ := hdiff.isExactOn_ball
  -- the arc
  have harc_mem : ∀ φ ∈ Icc (-θ₀) θ₀, zetaK K y φ ∈ U := by
    intro φ hφ
    have hφ2 : φ ^ 2 ≤ θ₀ ^ 2 := by nlinarith [hφ.1, hφ.2]
    refine mem_discA hc0 hcA ?_ (le_of_eq (normSq_zetaK hK hy φ))
    rw [zetaK_re, hcdef, cK]
    have := βK_pos hK
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hcont : ContinuousOn (fun φ => hfun (YK K n) (zetaK K y φ) * ((βK K : ℂ) * ((K : ℂ) * I) / zK K y φ ^ 2))
      (Icc (-θ₀) θ₀) := by
    refine ContinuousOn.mul ?_ ?_
    · intro φ hφ
      exact ((differentiableAt_hfun _ (re_pos_of_discA hc0 (harc_mem φ hφ))).continuousAt.comp
        (hasDerivAt_zetaK hK hy φ).continuousAt).continuousWithinAt
    · intro φ _
      refine (continuousAt_const.div ((hasDerivAt_zK K y φ).continuousAt.pow 2)
        (pow_ne_zero _ (zK_ne hK hy φ))).continuousWithinAt
  have h1 := Rademacher.integral_eq_of_primitive hP (by linarith) (hasDerivAt_zetaK hK hy) harc_mem hcont
  -- the chord
  have hγ : ∀ v : ℝ, HasDerivAt (fun v : ℝ => ((c : ℝ) : ℂ) + v * I) I v := by
    intro v
    have := ((hasDerivAt_id (v : ℂ)).comp_ofReal).mul_const I
    simpa using this.const_add ((c : ℝ) : ℂ)
  have hchord_mem : ∀ v ∈ Icc (-s) s, ((c : ℝ) : ℂ) + v * I ∈ U := by
    intro v hv
    have hv2 : v ^ 2 ≤ s ^ 2 := by nlinarith [hv.1, hv.2]
    refine mem_discA hc0 hcA (by simp) ?_
    rw [normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    have := cs_sq (θ₀ := θ₀) hK hy
    rw [← hcdef, ← hsdef, ← hAdef] at this
    nlinarith
  have h2 : ∫ v in (-s)..s, hfun (YK K n) (((c : ℝ) : ℂ) + v * I) * I =
      P ((c : ℂ) + (s : ℂ) * I) - P ((c : ℂ) + ((-s : ℝ) : ℂ) * I) := by
    refine Rademacher.integral_eq_of_primitive (γ := fun v : ℝ => ((c : ℝ) : ℂ) + v * I) hP (by linarith) hγ
      hchord_mem ?_
    refine ContinuousOn.mul (fun v _ => ?_) continuousOn_const
    refine ((differentiableAt_hfun _ ?_).continuousAt.comp (by fun_prop : Continuous fun v : ℝ =>
      ((c : ℝ) : ℂ) + v * I).continuousAt).continuousWithinAt
    simpa using hc0
  obtain ⟨hz1, hz2⟩ := zetaK_pm hK hy θ₀
  have hM : ∫ φ in (-θ₀)..θ₀, mI K n y φ = ((√(βK K) : ℝ) : ℂ) / (I * K) *
      ∫ φ in (-θ₀)..θ₀, hfun (YK K n) (zetaK K y φ) * ((βK K : ℂ) * ((K : ℂ) * I) / zK K y φ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun φ _ => mI_eq hK n hy φ
  rw [hM, h1, hz1, hz2, ← hcdef, ← hsdef, ← h2, intervalIntegral.integral_mul_const]
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

/-! ### the tails of the chord -/

lemma tail_Ioi' {s E : ℝ} (hs : 0 < s) (g : ℝ → ℂ) (hg : ∀ v : ℝ, s < v → ‖g v‖ ≤ v ^ (-(3 / 2 : ℝ)) * E) :
    ‖∫ v in Ioi s, g v‖ ≤ 2 * E / √s := by
  have hI := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) hs
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi s)) (hI.mul_const E)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => hg v hv))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_mul_const, integral_Ioi_rpow_of_lt (by norm_num) hs]
  rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
  field_simp

lemma tail_pointwise' {Y c s v : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) (hs : 0 < s) (hv : s ≤ |v|) :
    ‖hfun Y ((c : ℂ) + v * I)‖ ≤ |v| ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y * c / (c ^ 2 + s ^ 2)) := by
  rw [norm_hfun_line hc]
  have h1 : ‖(c : ℂ) + v * I‖ ^ (-(3 / 2 : ℝ)) ≤ |v| ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) norm_line_ge (by norm_num)
  have hv2 : s ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ hs.le hv 2
  have h2 : Real.exp (c + Y * c / (c ^ 2 + v ^ 2)) ≤ Real.exp (c + Y * c / (c ^ 2 + s ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : Y * c / (c ^ 2 + v ^ 2) ≤ Y * c / (c ^ 2 + s ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- **the tails**: `‖∫_ℝ h(c+iv) dv − ∫_{−s}^{s} h(c+iv) dv‖ ≤ 4e^{c + Yc/(c²+s²)}/√s`. -/
theorem tail_bound' {Y c s : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) (hs : 0 < s) :
    ‖(∫ v : ℝ, hfun Y ((c : ℂ) + v * I)) - ∫ v in (-s)..s, hfun Y ((c : ℂ) + v * I)‖ ≤
      4 * Real.exp (c + Y * c / (c ^ 2 + s ^ 2)) / √s := by
  set g := fun v : ℝ => hfun Y ((c : ℂ) + v * I)
  set E := Real.exp (c + Y * c / (c ^ 2 + s ^ 2))
  have hint := integrable_hfun_line hY hc
  have e1 := intervalIntegral.integral_Iic_add_Ioi (f := g) (b := -s) hint.integrableOn hint.integrableOn
  have e2 := intervalIntegral.integral_interval_add_Ioi (f := g) (a := -s) (b := s) hint.integrableOn
    hint.integrableOn
  have e3 := integral_comp_neg_Ioi s g
  have hdiff : (∫ v : ℝ, g v) - ∫ v in (-s)..s, g v = (∫ v in Ioi s, g (-v)) + ∫ v in Ioi s, g v := by
    rw [e3, ← e1, ← e2]; ring
  change ‖(∫ v : ℝ, g v) - ∫ v in (-s)..s, g v‖ ≤ _
  rw [hdiff]
  have b1 := tail_Ioi' hs (fun v => g (-v)) (E := E) fun v hv => by
    have := tail_pointwise' (v := -v) hY hc hs (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    rwa [abs_neg, abs_of_pos (by linarith)] at this
  have b2 := tail_Ioi' hs g (E := E) fun v hv => by
    have := tail_pointwise' (v := v) hY hc hs (by rw [abs_of_pos (by linarith)]; linarith)
    rwa [abs_of_pos (by linarith)] at this
  calc _ ≤ ‖∫ v in Ioi s, g (-v)‖ + ‖∫ v in Ioi s, g v‖ := norm_add_le _ _
    _ ≤ _ := by
        have : 4 * E / √s = 2 * E / √s + 2 * E / √s := by ring
        linarith

/-! ### the exact value -/

/-- **Andrews' main term at the cusps of denominator `K`**:
`M_K(n) = √48/(√K √(24n−1)) · sinh(π√(24n−1)/(6K))`. -/
def MK (K n : ℕ) : ℝ := √48 / (√K * √(24 * (n : ℝ) - 1)) * Real.sinh (π * √(24 * (n : ℝ) - 1) / (6 * K))

lemma sqrt_YK {K n : ℕ} (hK : 0 < K) (hn : 1 ≤ n) : √(YK K n) = π * √(24 * (n : ℝ) - 1) / (12 * K) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h0 : 0 ≤ 24 * (n : ℝ) - 1 := by linarith
  rw [show YK K n = (π * √(24 * (n : ℝ) - 1) / (12 * K)) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt h0]; unfold YK; ring]
  exact Real.sqrt_sq (by positivity)

lemma MK_const {K n : ℕ} (hK : 0 < K) (hn : 1 ≤ n) :
    √(βK K) / K * (2 * π * (2 * Real.sinh (2 * √(YK K n)) / (√π * (2 * √(YK K n))))) = MK K n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h0 : 0 < 24 * (n : ℝ) - 1 := by linarith
  have hs : 0 < √(24 * (n : ℝ) - 1) := Real.sqrt_pos.mpr h0
  have hβ : √(βK K) = √π / (√12 * √K) := by
    rw [βK, Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num)]
  rw [sqrt_YK hK hn, hβ]
  unfold MK
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hK' : 0 < √(K : ℝ) := Real.sqrt_pos.mpr hk
  have h12 : √(12 : ℝ) ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have h48 : √(48 : ℝ) = 2 * √12 := by
    rw [show (48 : ℝ) = 2 ^ 2 * 12 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hKs : √(K : ℝ) ^ 2 = K := Real.sq_sqrt hk.le
  have hπs : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  rw [show 2 * (π * √(24 * (n : ℝ) - 1) / (12 * K)) = π * √(24 * (n : ℝ) - 1) / (6 * K) by ring, h48]
  field_simp
  rw [h12]
  norm_num

/-- **the exact evaluation of the core**: `‖∫_{−θ₀}^{θ₀} m − M_K(n)‖ ≤ (√β/K)·4e^{c + Yc/(c²+s²)}/√s`. -/
theorem core_eval {K : ℕ} (hK : 0 < K) {n : ℕ} (hn : 1 ≤ n) {y θ₀ : ℝ} (hy : 0 < y) (hθ : 0 < θ₀) :
    ‖(∫ φ in (-θ₀)..θ₀, mI K n y φ) - MK K n‖ ≤
      √(βK K) / K * (4 * Real.exp (cK K y θ₀ + YK K n * cK K y θ₀ / (cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2)) /
        √(sK K y θ₀)) := by
  have hY := YK_pos hK hn
  have hc0 := cK_pos (θ₀ := θ₀) hK hy
  have hs0 := sK_pos hK hy hθ
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hB := bessel_line hY.le hc0
  rw [← Complex.ofReal_tsum, tsum_bco hY] at hB
  have hT := tail_bound' hY.le hc0 hs0
  rw [core_chord hK n hy hθ, ← MK_const hK hn]
  set L := ∫ v : ℝ, hfun (YK K n) ((cK K y θ₀ : ℂ) + v * I)
  set S := ∫ v in (-sK K y θ₀)..sK K y θ₀, hfun (YK K n) ((cK K y θ₀ : ℂ) + v * I)
  have hB' : L = ((2 * π * (2 * Real.sinh (2 * √(YK K n)) / (√π * (2 * √(YK K n)))) : ℝ) : ℂ) := by
    rw [show L = ∫ t : ℝ, ((cK K y θ₀ : ℂ) + t * I) ^ (-(3 / 2 : ℂ)) *
      cexp (((cK K y θ₀ : ℂ) + t * I) + (YK K n : ℂ) / ((cK K y θ₀ : ℂ) + t * I)) from rfl, hB]
    push_cast; ring
  have e : ((√(βK K) : ℝ) : ℂ) / K * S -
      ((√(βK K) / K * (2 * π * (2 * Real.sinh (2 * √(YK K n)) / (√π * (2 * √(YK K n))))) : ℝ) : ℂ) =
      -(((√(βK K) / K : ℝ) : ℂ) * (L - S)) := by
    rw [hB']; push_cast; ring
  rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr

end

end Andrews66
