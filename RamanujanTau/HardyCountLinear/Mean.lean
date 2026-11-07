/-
# A weighted mean-square bound for Fourier integrals (Schur test)

Let `g : ℝ → ℂ` be continuous with `‖g ξ‖ ≤ S · triHat R ξ`, and put
`I(t₀) = ∫ g(ξ) e^{-2πiξt₀} dξ`.  Then for every `L ≥ 0` and centre `c`,

    ∫ tri_L(t₀ − c) |I(t₀)|² dt₀ ≤ 2 S² R³ L.

Proof: expand `|I|² = I · conj I`, use Fubini twice to get
`∫ ḡ(η) ∫ g(ξ) Ŵ(ξ − η) dξ dη` with `Ŵ` the Fourier transform of the weight, `|Ŵ| = triHat_L`,
then `‖g‖ ≤ 2SR²` and `∫ triHat_L = L`, `∫ triHat_R = R`.  This replaces Plancherel (which in
Mathlib is not linked to the integral Fourier transform) and is the mean-square input of the
Hardy–Littlewood method.
-/
import RamanujanTau.HardyCount.Triangle

set_option autoImplicit false

namespace RamanujanTau.HardyCountLinear

open Complex MeasureTheory Set Filter Function
open RamanujanTau.HardyCount
open scoped Real FourierTransform

/-- The phase `e^{-2πiξt}`. -/
noncomputable def ph (ξ t : ℝ) : ℂ := cexp (-(↑(2 * π * ξ * t) * I))

lemma norm_ph (ξ t : ℝ) : ‖ph ξ t‖ = 1 := by
  rw [ph, Complex.norm_exp]; simp

lemma continuous_ph : Continuous fun p : ℝ × ℝ => ph p.1 p.2 := by
  unfold ph; fun_prop

lemma conj_ph (ξ t : ℝ) : (starRingEnd ℂ) (ph ξ t) = ph (-ξ) t := by
  rw [ph, ph, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma ph_mul (ξ η t : ℝ) : ph ξ t * ph η t = ph (ξ + η) t := by
  rw [ph, ph, ph, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The Fourier integral `I(t₀) = ∫ g(ξ) e^{-2πiξt₀} dξ`. -/
noncomputable def fI (g : ℝ → ℂ) (t₀ : ℝ) : ℂ := ∫ ξ, g ξ * ph ξ t₀

lemma continuous_triHat {R : ℝ} (hR : 0 ≤ R) : Continuous fun ξ => triHat R ξ := by
  have : (fun ξ => triHat R ξ) = fun ξ => (𝓕 (triC R) ξ).re := by
    funext ξ; rw [fourier_triC hR]; simp
  rw [this]
  exact Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ (integrable_triC R))

section
variable {g : ℝ → ℂ} {S R : ℝ}

lemma integrable_of_bound (hg : Continuous g) (hR : 0 ≤ R)
    (hb : ∀ ξ, ‖g ξ‖ ≤ S * triHat R ξ) : Integrable g := by
  refine ((integrable_triHat hR).const_mul S).mono' hg.aestronglyMeasurable
    (Eventually.of_forall hb)

lemma norm_fI_le (t₀ : ℝ) : ‖fI g t₀‖ ≤ ∫ ξ, ‖g ξ‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext ξ; rw [norm_mul, norm_ph, mul_one]

lemma continuous_fI (hg : Continuous g) (hR : 0 ≤ R) (hb : ∀ ξ, ‖g ξ‖ ≤ S * triHat R ξ) :
    Continuous (fI g) := by
  have hgi := integrable_of_bound hg hR hb
  refine continuous_of_dominated (bound := fun ξ => ‖g ξ‖)
    (fun t₀ => (hg.mul (continuous_ph.comp (Continuous.prodMk continuous_id
      continuous_const))).aestronglyMeasurable)
    (fun t₀ => Eventually.of_forall fun ξ => by rw [norm_mul, norm_ph, mul_one])
    hgi.norm (Eventually.of_forall fun ξ => ?_)
  exact continuous_const.mul (continuous_ph.comp (Continuous.prodMk continuous_const
    continuous_id))

/-- The Fourier transform of the shifted triangle has modulus `triHat`. -/
lemma norm_integral_tri_ph_le {L : ℝ} (hL : 0 ≤ L) (c ζ : ℝ) :
    ‖∫ t, (tri L (t - c) : ℂ) * ph ζ t‖ ≤ triHat L ζ := by
  have e1 : (∫ t, (tri L (t - c) : ℂ) * ph ζ t) = ∫ u, (tri L u : ℂ) * ph ζ (u + c) := by
    have := integral_sub_right_eq_self (μ := volume)
      (fun t => (tri L t : ℂ) * ph ζ (t + c)) c
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [sub_add_cancel]
  have e2 : ∀ u, (tri L u : ℂ) * ph ζ (u + c) = ph ζ c * (cexp (↑(-2 * π * u * ζ) * I) • triC L u) := by
    intro u
    rw [ph, ph, smul_eq_mul, triC]
    rw [show (tri L u : ℂ) * cexp (-(↑(2 * π * ζ * (u + c)) * I)) =
      (tri L u : ℂ) * (cexp (-(↑(2 * π * ζ * c) * I)) * cexp (↑(-2 * π * u * ζ) * I)) by
        rw [← Complex.exp_add]; congr 2; push_cast; ring]
    ring
  rw [e1, integral_congr_ae (Eventually.of_forall e2), integral_const_mul,
    ← Real.fourier_real_eq_integral_exp_smul, fourier_triC hL, norm_mul, norm_ph, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triHat_nonneg hL)]

/-- **The weighted mean-square bound.** -/
theorem integral_tri_norm_fI_sq_le (hg : Continuous g) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hb : ∀ ξ, ‖g ξ‖ ≤ S * triHat R ξ) {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    ∫ t₀, tri L (t₀ - c) * ‖fI g t₀‖ ^ 2 ≤ 2 * S ^ 2 * R ^ 3 * L := by
  have hgi := integrable_of_bound hg hR hb
  set B : ℝ := ∫ ξ, ‖g ξ‖ with hB
  have hIc := continuous_fI hg hR hb
  have hIb := norm_fI_le (g := g)
  have hWc : Continuous fun t₀ => (tri L (t₀ - c) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_tri L).comp (by fun_prop))
  have hWi : Integrable fun t₀ => tri L (t₀ - c) := (integrable_tri L).comp_sub_right c
  have hWi' : Integrable fun t₀ => (tri L (t₀ - c) : ℂ) := hWi.ofReal
  -- `conj I`
  have hconj : ∀ t₀, (starRingEnd ℂ) (fI g t₀) = ∫ η, (starRingEnd ℂ) (g η) * ph (-η) t₀ := by
    intro t₀
    rw [fI, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [map_mul, conj_ph]
  -- step 1: as a complex integral
  have hstep1 : ((∫ t₀, tri L (t₀ - c) * ‖fI g t₀‖ ^ 2 : ℝ) : ℂ) =
      ∫ t₀, ∫ η, (tri L (t₀ - c) : ℂ) * fI g t₀ * ((starRingEnd ℂ) (g η) * ph (-η) t₀) := by
    refine (integral_ofReal).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun t₀ => ?_)
    simp only
    rw [integral_const_mul, ← hconj, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  -- step 2: swap
  set F : ℝ → ℝ → ℂ := fun t₀ η =>
    (tri L (t₀ - c) : ℂ) * fI g t₀ * ((starRingEnd ℂ) (g η) * ph (-η) t₀) with hF
  have hFc : Continuous (uncurry F) := by
    simp only [hF]
    refine ((hWc.comp continuous_fst).mul (hIc.comp continuous_fst)).mul
      ((Complex.continuous_conj.comp (hg.comp continuous_snd)).mul ?_)
    exact continuous_ph.comp (Continuous.prodMk (continuous_neg.comp continuous_snd) continuous_fst)
  have hFi : Integrable (uncurry F) (volume.prod volume) := by
    refine ((hWi.mul_const B).mul_prod hgi.norm).mono' hFc.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tri_nonneg _ _), Complex.norm_conj, norm_ph, mul_one]
    have := hIb p.1
    have h0 := tri_nonneg L (p.1 - c)
    have h1 := norm_nonneg (g p.2)
    calc tri L (p.1 - c) * ‖fI g p.1‖ * ‖g p.2‖ ≤ tri L (p.1 - c) * B * ‖g p.2‖ := by gcongr
      _ = _ := rfl
  rw [integral_integral_swap hFi] at hstep1
  -- step 3: the inner integral
  have hinner : ∀ η, (∫ t₀, F t₀ η) = (starRingEnd ℂ) (g η) *
      ∫ ξ, g ξ * ∫ t₀, (tri L (t₀ - c) : ℂ) * ph (ξ - η) t₀ := by
    intro η
    set G : ℝ → ℝ → ℂ := fun t₀ ξ => (tri L (t₀ - c) : ℂ) * (g ξ * ph ξ t₀) * ph (-η) t₀
      with hG
    have hGc : Continuous (uncurry G) := by
      simp only [hG, uncurry]
      refine ((hWc.comp continuous_fst).mul ((hg.comp continuous_snd).mul
        (continuous_ph.comp (Continuous.prodMk continuous_snd continuous_fst)))).mul ?_
      exact continuous_ph.comp (Continuous.prodMk continuous_const continuous_fst)
    have hGi : Integrable (uncurry G) (volume.prod volume) := by
      refine (hWi.mul_prod hgi.norm).mono' hGc.aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      simp only [uncurry, hG, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tri_nonneg _ _), norm_ph, mul_one]
      rfl
    have e1 : (∫ t₀, F t₀ η) = (starRingEnd ℂ) (g η) * ∫ t₀, ∫ ξ, G t₀ ξ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t₀ => ?_)
      simp only [hF, hG, fI]
      rw [integral_mul_const, show (∫ a, (tri L (t₀ - c) : ℂ) * (g a * ph a t₀)) =
        (tri L (t₀ - c) : ℂ) * ∫ a, g a * ph a t₀ from integral_const_mul _ _]
      ring
    rw [e1, integral_integral_swap hGi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hG]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t₀ => ?_)
    simp only
    rw [show ph (ξ - η) t₀ = ph ξ t₀ * ph (-η) t₀ by rw [ph_mul]; ring_nf]
    ring
  rw [integral_congr_ae (Eventually.of_forall hinner)] at hstep1
  -- step 4: bounds
  have hgle : ∀ ξ, ‖g ξ‖ ≤ S * (2 * R ^ 2) := fun ξ =>
    (hb ξ).trans (mul_le_mul_of_nonneg_left (triHat_le_const hR) hS)
  have hinb : ∀ η, ‖∫ ξ, g ξ * ∫ t₀, (tri L (t₀ - c) : ℂ) * ph (ξ - η) t₀‖ ≤
      S * (2 * R ^ 2) * L := by
    intro η
    have hk : Integrable fun ξ => triHat L (ξ - η) := (integrable_triHat hL).comp_sub_right η
    refine (norm_integral_le_of_norm_le (hk.const_mul (S * (2 * R ^ 2)))
      (Eventually.of_forall fun ξ => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul]
      exact mul_le_mul (hgle ξ) (norm_integral_tri_ph_le hL c _) (norm_nonneg _)
        (by positivity)
    · rw [integral_const_mul, integral_sub_right_eq_self (fun ξ => triHat L ξ) η,
        integral_triHat hL]
  have hout : ‖∫ η, (starRingEnd ℂ) (g η) *
      ∫ ξ, g ξ * ∫ t₀, (tri L (t₀ - c) : ℂ) * ph (ξ - η) t₀‖ ≤ 2 * S ^ 2 * R ^ 3 * L := by
    refine (norm_integral_le_of_norm_le
      (((integrable_triHat hR).const_mul S).mul_const (S * (2 * R ^ 2) * L))
      (Eventually.of_forall fun η => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hb η) (hinb η) (norm_nonneg _)
        (mul_nonneg hS (triHat_nonneg hR))
    · rw [integral_mul_const, integral_const_mul, integral_triHat hR]; ring
  have hre := Complex.re_le_norm
    (((∫ t₀, tri L (t₀ - c) * ‖fI g t₀‖ ^ 2 : ℝ) : ℂ))
  rw [Complex.ofReal_re] at hre
  rw [hstep1] at hre
  exact hre.trans hout

end

end RamanujanTau.HardyCountLinear
