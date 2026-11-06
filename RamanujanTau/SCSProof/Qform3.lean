/-
# The pairing `Q` as an integral of horocycle coefficients (part 3)

`Q_eq`: `∫ Ψ conj ft = ∫_ζ 1_B(ζ) ∫_y 1_I(y) y⁻² cf(y,ζ)`.
-/
import RamanujanTau.SCSProof.Qform2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- The `y`-integrand. -/
noncomputable def Ky (ζ : ℍ) (y : ℝ) : ℂ :=
  (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * cf P y ζ) y

lemma integral_Hf_x (ζ : ℍ) (y : ℝ) : ∫ x, Hf P ζ (x, y) = Ky P ζ y := by
  unfold Ky
  by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
  · have hy0 : 0 < y := P.hY.trans_le hy.1
    rw [indicator_of_mem hy]
    have e : ∀ x : ℝ, Hf P ζ (x, y) = (Ico (0 : ℝ) 1).indicator (fun x => ((1 / y ^ 2 : ℝ) : ℂ) *
        (Psi (hp hy0 x) (aff hy0 x ζ) * cexp (-2 * π * I * P.h * x))) x := by
      intro x
      unfold Hf
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · rw [indicator_of_mem (show (x, y) ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε)) from
          ⟨hx, hy⟩), indicator_of_mem hx, aff_eq_affGL hy0, toH_hp hy0]
        ring
      · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]
    simp_rw [e]
    rw [integral_indicator measurableSet_Ico, integral_const_mul]
    unfold cf
    rw [← coeff_Psi P.h hy0 ζ]
    congr 1
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  · rw [indicator_of_notMem hy]
    have : ∀ x : ℝ, Hf P ζ (x, y) = 0 := fun x => by
      unfold Hf; exact indicator_of_notMem (fun h => hy h.2) _
    simp [this]

lemma integral_Az (ζ : ℍ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ∫ z, Az P ζ z = ∫ y, Ky P ζ y := by
  rw [integral_Az_eq_Hf, Measure.volume_eq_prod,
    integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact integrable_Hf P hM0 hM ζ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => integral_Hf_x P ζ y)

lemma g_skew (p : ℍ × ℍ) :
    (fun p : ℍ × ℍ => Psi p.1 p.2 * conj (ft P p)) (skew p) =
      ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) * Az P p.2 p.1 := by
  simp only
  rw [ft_skew]
  unfold Az skew
  simp only [map_mul]
  have h1 : conj (strip.indicator (1 : ℍ → ℂ) p.1) = strip.indicator 1 p.1 := by
    unfold indicator; split_ifs <;> simp
  have h2 : conj ({u : ℍ | inI P u.im}.indicator (1 : ℍ → ℂ) p.1) =
      {u : ℍ | inI P u.im}.indicator 1 p.1 := by
    unfold indicator; split_ifs <;> simp
  have h3 : conj ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) =
      {ζ : ℂ | inB P ζ}.indicator 1 (p.2 : ℂ) := by
    unfold indicator; split_ifs <;> simp
  have h4 : conj (cexp (2 * π * I * P.h * p.1.re)) = cexp (-2 * π * I * P.h * p.1.re) := by
    rw [← Complex.exp_conj]; congr 1; apply Complex.ext <;> simp
  have h5 : (strip ∩ {u : ℍ | inI P u.im}).indicator (1 : ℍ → ℂ) p.1 =
      strip.indicator 1 p.1 * {u : ℍ | inI P u.im}.indicator 1 p.1 := by
    by_cases ha : p.1 ∈ strip <;> by_cases hb : p.1 ∈ {u : ℍ | inI P u.im} <;>
      simp [indicator, ha, hb]
  rw [h1, h2, h3, h4, h5]
  ring

/-- **The pairing in coordinates.** -/
theorem Q_eq {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ∫ p, Psi p.1 p.2 * conj (ft P p) =
      ∫ ζ : ℍ, ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ)) * ∫ y, Ky P ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_g P hM0 hM
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hgi.aestronglyMeasurable)]
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      Az P p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact g_skew P p
  simp_rw [g_skew]
  rw [Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_Az P ζ hM0 hM]

end RamanujanTau.SCSProof
