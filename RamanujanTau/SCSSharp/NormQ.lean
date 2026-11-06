/-
# Cauchy–Schwarz with the sharp ball bound

`norm_Q_le'`: `‖∫ Ψ conj ft‖ ≤ ½ · √(M² R¹² · 8R) · √(2 ‖Σ_γ I(γ)‖)` (was `8R⁴` in `SCSProof.norm_Q_le`).
-/
import RamanujanTau.SCSSharp.Ball

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.SCSProof
open RamanujanTau.EisensteinReal.Horo (Uset)
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

theorem norm_Q_le' {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ ≤
      (1 / 2) * Real.sqrt ((M * Rθ P ^ 6) ^ 2 * (8 * Rθ P)) *
        Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) := by
  have h2Q := two_Q_eq P hM0 hM
  set R := Rθ P
  have hR := one_le_Rθ P
  set c := M * R ^ 6
  have hc0 : 0 ≤ c := by positivity
  set F : ℍ × ℍ → ℝ≥0∞ := fun p => indU p * ENNReal.ofReal c *
    {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p
  set G : ℍ × ℍ → ℝ≥0∞ := fun p => indU p * ‖Pt P p‖ₑ
  have hmD : Measurable fun q : ℍ × ℍ => Dh q.1 q.2 := by
    unfold Dh
    refine Measurable.div ?_ ((measurable_im_H.comp measurable_fst).mul
      (measurable_im_H.comp measurable_snd))
    exact Complex.continuous_normSq.measurable.comp
      ((UpperHalfPlane.measurable_coe.comp measurable_fst).sub
        (Complex.continuous_conj.measurable.comp (UpperHalfPlane.measurable_coe.comp measurable_snd)))
  have hmS : MeasurableSet {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} := measurableSet_le hmD measurable_const
  have hFm : Measurable F := (measurable_indU.mul measurable_const).mul
    (measurable_one.indicator hmS)
  have hGm : Measurable G := measurable_indU.mul (measurable_Pt P).enorm
  -- pointwise domination
  have hpt : ∀ p, ‖indUC p * (Psi p.1 p.2 * conj (Pt P p))‖ₑ ≤ (F * G) p := by
    intro p
    rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
    simp only [Pi.mul_apply, F, G]
    by_cases hP : Pt P p = 0
    · simp [hP]
    have hD := Dh_le_of_Pt P p hP
    have hD0 : 0 ≤ Dh p.1 p.2 := by
      unfold Dh; exact div_nonneg (Complex.normSq_nonneg _) (mul_pos p.1.im_pos p.2.im_pos).le
    have hPsi : ‖Psi p.1 p.2‖ₑ ≤ ENNReal.ofReal c := by
      rw [← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ((norm_Psi_le_Dh hM p.1 p.2).trans ?_)
      show M * Dh p.1 p.2 ^ 6 ≤ M * R ^ 6
      gcongr
    rw [indicator_of_mem (show p ∈ {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} from hD)]
    have hU : ‖indUC p‖ₑ = indU p := by
      unfold indUC indU; by_cases h : p.1 ∈ Uset
      · rw [indicator_of_mem h, indicator_of_mem h]; simp
      · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
    rw [hU]
    have hUU : indU p = indU p * indU p := by
      unfold indU; by_cases h : p.1 ∈ Uset
      · rw [indicator_of_mem h]; simp
      · rw [indicator_of_notMem h]; simp
    calc indU p * (‖Psi p.1 p.2‖ₑ * ‖Pt P p‖ₑ) ≤ indU p * (ENNReal.ofReal c * ‖Pt P p‖ₑ) := by
          gcongr
      _ = indU p * ENNReal.ofReal c * 1 * (indU p * ‖Pt P p‖ₑ) := by
          conv_lhs => rw [hUU]
          ring
      _ = _ := by simp
  -- Hölder
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hFm.aemeasurable hGm.aemeasurable
  have hF2 : ∫⁻ p, F p ^ (2 : ℝ) ≤ ENNReal.ofReal (c ^ 2 * (8 * R)) := by
    have e : ∀ p, F p ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) *
        (indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p) := by
      intro p
      simp only [F]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        indU_sq]
      have hI : ({q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator (1 : ℍ × ℍ → ℝ≥0∞) p) ^ (2 : ℝ) =
          {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p := by
        unfold indicator; split_ifs <;> simp
      rw [hI, ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num)]
      norm_num
      ring
    simp_rw [e]
    rw [lintegral_const_mul _ (measurable_indU.mul (measurable_one.indicator hmS))]
    calc ENNReal.ofReal (c ^ 2) * ∫⁻ p, indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p
        ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (8 * R) := by
          gcongr; exact lintegral_U_ball' R hR
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hG2 : ∫⁻ p, G p ^ (2 : ℝ) = ∫⁻ p, indU p * ‖Pt P p‖ₑ ^ 2 := by
    refine lintegral_congr fun p => ?_
    simp only [G]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), indU_sq]
    norm_cast
  have hGfin := lintegral_Pt_sq_ne_top P
  have hFfin : ∫⁻ p, F p ^ (2 : ℝ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF2
  -- assemble
  have hnorm : ‖(2 : ℂ) * ∫ p, Psi p.1 p.2 * conj (ft P p)‖ ≤
      (∫⁻ p, ‖indUC p * (Psi p.1 p.2 * conj (Pt P p))‖ₑ).toReal := by
    rw [← h2Q]; exact norm_integral_le_toReal _
  have hle1 : (∫⁻ p, ‖indUC p * (Psi p.1 p.2 * conj (Pt P p))‖ₑ).toReal ≤
      ((∫⁻ p, F p ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ p, G p ^ (2 : ℝ)) ^ (1 / (2 : ℝ))).toReal := by
    refine ENNReal.toReal_mono ?_ ((lintegral_mono hpt).trans hH)
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFfin)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by rw [hG2]; exact hGfin))
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, hG2] at hle1
  have hA : ((∫⁻ p, F p ^ (2 : ℝ)).toReal) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt (c ^ 2 * (8 * R)) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_sqrt ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hF2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hB : ((∫⁻ p, indU p * ‖Pt P p‖ₑ ^ 2).toReal) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (lintegral_Pt_sq_le P)
  rw [norm_mul] at hnorm
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at hnorm
  have hfinal : 2 * ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ ≤
      Real.sqrt (c ^ 2 * (8 * R)) * Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) := by
    refine hnorm.trans (hle1.trans ?_)
    exact mul_le_mul hA hB (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.sqrt_nonneg _)
  linarith

end RamanujanTau.SCSSharp
