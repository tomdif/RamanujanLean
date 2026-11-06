/-
# Sharp measure bound for hyperbolic balls: `μ{w : Dh(z,w) ≤ R} ≤ 4R`

`SCSProof.lintegral_ball_le` bounds the ball `{w : Dh(z,w) ≤ R}` (with `Dh = |z − w̄|²/(Im z Im w)
= 4cosh²(d/2)`) by the box `[−R,R]×[1/R,R]`, i.e. by `4R⁴`.  The true area is `2π(cosh d − 1) ≈ πR`;
here we prove `≤ 4R` by integrating the exact horizontal widths `2√(R y)` against `dy/y²`:
`∫_{1/R}^∞ 2√(R y) y^{−2} dy = 4R`.
-/
import RamanujanTau.SCSProof.Point4

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.SCSProof
open RamanujanTau.EisensteinReal.Horo (Uset)
open scoped ENNReal Real ComplexConjugate

/-- The planar region `{(x,y) : y ≥ 1/R, |x| ≤ √(R y)}`. -/
def Sb (R : ℝ) : Set (ℝ × ℝ) := {p | 1 / R ≤ p.2 ∧ |p.1| ≤ Real.sqrt (R * p.2)}

lemma measurableSet_Sb (R : ℝ) : MeasurableSet (Sb R) := by
  refine (measurableSet_le measurable_const measurable_snd).inter ?_
  exact measurableSet_le (continuous_abs.comp continuous_fst).measurable
    (Real.continuous_sqrt.comp (continuous_const.mul continuous_snd)).measurable

/-- The planar weight. -/
noncomputable def gB (R : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  (Sb R).indicator (fun q : ℝ × ℝ => ENNReal.ofReal (1 / q.2 ^ 2)) p

lemma measurable_gB (R : ℝ) : Measurable (gB R) := by
  refine Measurable.indicator ?_ (measurableSet_Sb R)
  exact ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_snd.pow_const 2))

lemma gB_slice (R : ℝ) (hR : 0 < R) (y : ℝ) :
    ∫⁻ x, gB R (x, y) = (Ici (1 / R)).indicator
      (fun y => ENNReal.ofReal (2 * Real.sqrt R * y ^ (-(3 / 2 : ℝ)))) y := by
  by_cases hy : 1 / R ≤ y
  · rw [indicator_of_mem (show y ∈ Ici (1 / R) from hy)]
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
    have e : (fun x => gB R (x, y)) = (Icc (-Real.sqrt (R * y)) (Real.sqrt (R * y))).indicator
        (fun _ => ENNReal.ofReal (1 / y ^ 2)) := by
      funext x
      unfold gB Sb
      by_cases hx : |x| ≤ Real.sqrt (R * y)
      · rw [indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 1 / R ≤ p.2 ∧ |p.1| ≤ Real.sqrt (R * p.2)}
          from ⟨hy, hx⟩), indicator_of_mem (show x ∈ Icc (-Real.sqrt (R * y)) (Real.sqrt (R * y))
          from abs_le.1 hx)]
      · rw [indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 1 / R ≤ p.2 ∧ |p.1| ≤ Real.sqrt (R * p.2)}
          from fun h => hx h.2), indicator_of_notMem (show x ∉ Icc (-Real.sqrt (R * y))
          (Real.sqrt (R * y)) from fun h => hx (abs_le.2 h))]
    rw [e, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hs : Real.sqrt (R * y) = Real.sqrt R * y ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul hR.le, Real.sqrt_eq_rpow y]
    rw [hs]
    have e2 : y ^ (-(3 / 2 : ℝ)) = y ^ (1 / 2 : ℝ) / y ^ 2 := by
      rw [eq_div_iff (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num
    rw [e2]; ring
  · rw [indicator_of_notMem (show y ∉ Ici (1 / R) from hy)]
    have : (fun x => gB R (x, y)) = fun _ => 0 := by
      funext x; unfold gB Sb
      exact indicator_of_notMem (fun h => hy h.1) _
    rw [this, lintegral_zero]

lemma lintegral_gB (R : ℝ) (hR : 0 < R) : ∫⁻ p, gB R p = ENNReal.ofReal (4 * R) := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ (measurable_gB R).aemeasurable]
  simp_rw [gB_slice R hR]
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hc : (0 : ℝ) < 1 / R := by positivity
  have hint : IntegrableOn (fun y : ℝ => 2 * Real.sqrt R * y ^ (-(3 / 2 : ℝ))) (Ioi (1 / R)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
    have e : (1 / R) ^ (-(3 / 2 : ℝ) + 1) = Real.sqrt R := by
      rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2) by norm_num, Real.rpow_neg hc.le, one_div,
        Real.inv_rpow hR.le, inv_inv, Real.sqrt_eq_rpow]
    rw [e]
    have := Real.mul_self_sqrt hR.le
    norm_num
    nlinarith
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have : 0 < y := lt_trans hc hy
    positivity

/-- **Sharp ball bound**: `∫⁻ 1[Dh(z,·) ≤ R] ≤ 4R`. -/
theorem lintegral_ball_le' (z : ℍ) {R : ℝ} (hR : 1 ≤ R) :
    ∫⁻ w, {w : ℍ | Dh z w ≤ R}.indicator 1 w ≤ ENNReal.ofReal (4 * R) := by
  have hR0 : 0 < R := by linarith
  rw [lintegral_affGL z]
  set φ : ℍ → ℝ≥0∞ := fun ζ => {w : ℍ | Dh z w ≤ R}.indicator (1 : ℍ → ℝ≥0∞)
      (affGL z.re z.im z.im_pos • ζ) with hφ
  have hm : Measurable φ := by
    refine (measurable_one.indicator ?_).comp (measurePreserving_affGL _ _ _).measurable
    refine measurableSet_le ?_ measurable_const
    unfold Dh
    refine Measurable.div ?_ (measurable_const.mul measurable_im_H)
    exact Complex.continuous_normSq.measurable.comp (measurable_const.sub
      (Complex.continuous_conj.measurable.comp UpperHalfPlane.measurable_coe))
  rw [lintegral_H φ hm]
  refine le_trans ?_ ((setLIntegral_le_lintegral {p : ℝ × ℝ | 0 < p.2} (gB R)).trans
    (le_of_eq (lintegral_gB R hR0)))
  refine setLIntegral_mono' (measurableSet_lt measurable_const measurable_snd) fun p hp => ?_
  have hp' : 0 < p.2 := hp
  by_cases h0 : φ (toH p) = 0
  · rw [h0, zero_mul]; exact bot_le
  have hmem : Dh z (affGL z.re z.im z.im_pos • toH p) ≤ R := by
    by_contra h
    exact h0 (indicator_of_notMem (show affGL z.re z.im z.im_pos • toH p ∉
      {w : ℍ | Dh z w ≤ R} from h) _)
  rw [Dh_eq_rel, rel_affGL] at hmem
  have hre : ((toH p : ℂ)).re = p.1 := toH_re hp'
  have him : ((toH p : ℂ)).im = p.2 := toH_im hp'
  rw [hre, him, div_le_iff₀ hp'] at hmem
  have h1 : (1 + p.2) ^ 2 ≤ R * p.2 := by nlinarith [sq_nonneg p.1]
  have h2 : p.1 ^ 2 ≤ R * p.2 := by nlinarith [sq_nonneg (1 + p.2)]
  have hS : p ∈ Sb R := by
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hR0]; nlinarith
    · rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h2
  have hφ1 : φ (toH p) ≤ 1 := by
    simp only [hφ]; unfold indicator; split_ifs <;> simp
  unfold gB
  rw [indicator_of_mem hS]
  calc φ (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) ≤ 1 * ENNReal.ofReal (1 / p.2 ^ 2) := by gcongr
    _ = _ := one_mul _

/-- `∫⁻_{U×ℍ} 1[Dh ≤ R] ≤ 8R`. -/
lemma lintegral_U_ball' (R : ℝ) (hR : 1 ≤ R) :
    ∫⁻ p : ℍ × ℍ, indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p ≤
      ENNReal.ofReal (8 * R) := by
  have hmD : Measurable fun q : ℍ × ℍ => Dh q.1 q.2 := by
    unfold Dh
    refine Measurable.div ?_ ((measurable_im_H.comp measurable_fst).mul
      (measurable_im_H.comp measurable_snd))
    exact Complex.continuous_normSq.measurable.comp
      ((UpperHalfPlane.measurable_coe.comp measurable_fst).sub
        (Complex.continuous_conj.measurable.comp (UpperHalfPlane.measurable_coe.comp measurable_snd)))
  have hmS : MeasurableSet {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} := measurableSet_le hmD measurable_const
  rw [Measure.volume_eq_prod, lintegral_prod _ ((measurable_indU.mul
    (measurable_one.indicator hmS)).aemeasurable)]
  calc ∫⁻ z, ∫⁻ w, indU (z, w) * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 (z, w)
      ≤ ∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z * ENNReal.ofReal (4 * R) := by
        refine lintegral_mono fun z => ?_
        simp only [indU]
        have hmw : Measurable fun w : ℍ => {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator
            (1 : ℍ × ℍ → ℝ≥0∞) (z, w) :=
          (measurable_one.indicator hmS).comp measurable_prodMk_left
        rw [lintegral_const_mul _ hmw]
        gcongr
        refine le_trans (le_of_eq ?_) (lintegral_ball_le' z hR)
        congr 1
    _ = (∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z) * ENNReal.ofReal (4 * R) :=
        lintegral_mul_const _ (measurable_one.indicator measurableSet_Uset)
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (4 * R) := by gcongr; exact lintegral_U_le
    _ = ENNReal.ofReal (8 * R) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf

end RamanujanTau.SCSSharp
