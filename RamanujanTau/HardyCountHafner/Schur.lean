/-
# A general weighted mean-square bound for Fourier integrals (Schur test)

Generalises `HardyCountLinear.integral_tri_norm_fI_sq_le`: if `g` is continuous with
`‖g ξ‖ ≤ k ξ`, `k` integrable and `k ≤ K`, then for `I(t₀) = ∫ g(ξ) e^{-2πiξt₀} dξ`

    ∫ tri_L(t₀ − c) |I(t₀)|² dt₀ ≤ K · (∫ k) · L.

Same proof (expand, Fubini twice, `|Ŵ| = triHat_L`, `∫ triHat_L = L`).
-/
import RamanujanTau.HardyCountLinear.Mean

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open Complex MeasureTheory Set Filter Function
open RamanujanTau.HardyCount RamanujanTau.HardyCountLinear
open scoped Real FourierTransform

section
variable {g : ℝ → ℂ} {k : ℝ → ℝ} {K : ℝ}

lemma continuous_fI_gen (hg : Continuous g) (hgi : Integrable g) : Continuous (fI g) := by
  refine continuous_of_dominated (bound := fun ξ => ‖g ξ‖)
    (fun t₀ => (hg.mul (continuous_ph.comp (Continuous.prodMk continuous_id
      continuous_const))).aestronglyMeasurable)
    (fun t₀ => Eventually.of_forall fun ξ => by rw [norm_mul, norm_ph, mul_one])
    hgi.norm (Eventually.of_forall fun ξ => ?_)
  exact continuous_const.mul (continuous_ph.comp (Continuous.prodMk continuous_const
    continuous_id))

/-- **The weighted mean-square bound** (general majorant). -/
theorem integral_tri_norm_fI_sq_le_gen (hg : Continuous g) (hk : Integrable k)
    (hb : ∀ ξ, ‖g ξ‖ ≤ k ξ) (hK : ∀ ξ, k ξ ≤ K) {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    ∫ t₀, tri L (t₀ - c) * ‖fI g t₀‖ ^ 2 ≤ K * (∫ ξ, k ξ) * L := by
  have hgi : Integrable g := hk.mono' hg.aestronglyMeasurable (Eventually.of_forall hb)
  set B : ℝ := ∫ ξ, ‖g ξ‖ with hB
  have hIc := continuous_fI_gen hg hgi
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
      simp only [hG]
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
  have hk0 : ∀ ξ, 0 ≤ k ξ := fun ξ => (norm_nonneg _).trans (hb ξ)
  have hK0 : 0 ≤ K := (hk0 0).trans (hK 0)
  have hgle : ∀ ξ, ‖g ξ‖ ≤ K := fun ξ => (hb ξ).trans (hK ξ)
  have hinb : ∀ η, ‖∫ ξ, g ξ * ∫ t₀, (tri L (t₀ - c) : ℂ) * ph (ξ - η) t₀‖ ≤ K * L := by
    intro η
    have hk' : Integrable fun ξ => triHat L (ξ - η) := (integrable_triHat hL).comp_sub_right η
    refine (norm_integral_le_of_norm_le (hk'.const_mul K)
      (Eventually.of_forall fun ξ => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul]
      exact mul_le_mul (hgle ξ) (norm_integral_tri_ph_le hL c _) (norm_nonneg _) hK0
    · rw [integral_const_mul, integral_sub_right_eq_self (fun ξ => triHat L ξ) η,
        integral_triHat hL]
  have hout : ‖∫ η, (starRingEnd ℂ) (g η) *
      ∫ ξ, g ξ * ∫ t₀, (tri L (t₀ - c) : ℂ) * ph (ξ - η) t₀‖ ≤ K * (∫ ξ, k ξ) * L := by
    refine (norm_integral_le_of_norm_le (hk.mul_const (K * L))
      (Eventually.of_forall fun η => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hb η) (hinb η) (norm_nonneg _) (hk0 η)
    · rw [integral_mul_const]; ring
  have hre := Complex.re_le_norm
    (((∫ t₀, tri L (t₀ - c) * ‖fI g t₀‖ ^ 2 : ℝ) : ℂ))
  rw [Complex.ofReal_re] at hre
  rw [hstep1] at hre
  exact hre.trans hout

end

end RamanujanTau.HardyCountHafner
