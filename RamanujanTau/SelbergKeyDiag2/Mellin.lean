/-
# M3 step 4: the Mellin integral `∫₁^∞ x^{iv−1} W(a,b; αx²) dx`

On the line `Re z = 2`, `∫₁^∞ x^{iv−1}(αx²)^{−z} dx = α^{−z}/(2z − iv)`, so (`mellin_line2`)

    ∫₁^∞ x^{iv−1} W(a,b; αx²) dx = (2π)⁻¹ ∫_{(2)} Γ(a+z)Γ(b+z) α^{−z} e^{z²} / (z (2z − iv)) dy.

Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Residue
import RamanujanTau.SelbergKey.ShiftAFE

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
open scoped Real

lemma cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (Real.log x * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

lemma key_pow {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (v : ℝ) (z : ℂ) :
    (x : ℂ) ^ ((v : ℂ) * I - 1) * ((α * x ^ 2 : ℝ) : ℂ) ^ (-z) =
      (α : ℂ) ^ (-z) * (x : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z) := by
  rw [cpow_eq_exp hx, cpow_eq_exp (by positivity), cpow_eq_exp hα, cpow_eq_exp hx,
    Real.log_mul hα.ne' (by positivity), Real.log_pow, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The `x`-integral on `Re z = 2`. -/
lemma integral_Ioi_one_cpow (v : ℝ) {z : ℂ} (hz : z.re = 2) :
    ∫ x in Ioi (1:ℝ), (x : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z) = 1 / (2 * z - v * I) := by
  have hre : ((v : ℂ) * I - 1 - 2 * z).re < -1 := by norm_num [hz]
  rw [integral_Ioi_cpow_of_lt hre one_pos]
  simp only [ofReal_one, one_cpow]
  have : (v : ℂ) * I - 1 - 2 * z + 1 = -(2 * z - v * I) := by ring
  rw [this, neg_div_neg_eq]

/-- `Γ(a+z)Γ(b+z)e^{z²}/z` on the line `Re z = 2`. -/
noncomputable def gl (a b : ℂ) (y : ℝ) : ℂ :=
  Gamma (a + (((2:ℝ) : ℂ) + y * I)) * Gamma (b + (((2:ℝ) : ℂ) + y * I)) *
    cexp ((((2:ℝ) : ℂ) + y * I) ^ 2) / (((2:ℝ) : ℂ) + y * I)

lemma norm_gl_le {a b : ℂ} (ha : 0 < a.re + 2) (hb : 0 < b.re + 2) (y : ℝ) :
    ‖gl a b y‖ ≤ Real.Gamma (a.re + 2) * Real.Gamma (b.re + 2) * (Real.exp (2 ^ 2) * 2⁻¹) *
      Real.exp (-1 * y ^ 2) := by
  have h := norm_W2sh_integrand_le (c := 2) (ξ := 1) (by norm_num) ha hb one_pos y
  simp only [ofReal_one, one_cpow, mul_one, Real.one_rpow] at h
  exact h

lemma continuous_gl {a b : ℂ} (ha : 0 < a.re + 2) (hb : 0 < b.re + 2) : Continuous (gl a b) := by
  unfold gl
  exact Continuous.div (((continuous_Gamma_line ha).mul (continuous_Gamma_line hb)).mul (by fun_prop))
    (continuous_line 2) (line_ne_zero (by norm_num))

/-- **Mellin evaluation on the line `Re z = 2`.** -/
theorem mellin_line2 {a b : ℂ} (ha : 0 < a.re + 2) (hb : 0 < b.re + 2) {α : ℝ} (hα : 0 < α)
    (v : ℝ) :
    ∫ x in Ioi (1:ℝ), (x : ℂ) ^ ((v : ℂ) * I - 1) * W2sh a b (α * x ^ 2) 2 =
      (2 * π : ℂ)⁻¹ * vline (fun z => Gamma (a + z) * Gamma (b + z) * (α : ℂ) ^ (-z) *
        cexp (z ^ 2) / z / (2 * z - v * I)) 2 := by
  set z : ℝ → ℂ := fun y => ((2:ℝ) : ℂ) + y * I with hzdef
  have hzre : ∀ y, (z y).re = 2 := fun y => by simp [hzdef]
  set F : ℝ → ℝ → ℂ := fun x y =>
    (α : ℂ) ^ (-z y) * (x : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z y) * gl a b y with hF
  -- pointwise rewriting of the integrand
  have hpt : ∀ x ∈ Ioi (1:ℝ), (x : ℂ) ^ ((v : ℂ) * I - 1) * W2sh a b (α * x ^ 2) 2 =
      (2 * π : ℂ)⁻¹ * ∫ y, F x y := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    unfold W2sh vline
    rw [← mul_assoc, mul_comm _ ((2 * π : ℂ)⁻¹), mul_assoc, ← integral_const_mul]
    congr 1; congr 1; ext y
    have e := key_pow hα hx0 v (z y)
    simp only [hF, gl]
    rw [show (x : ℂ) ^ ((v : ℂ) * I - 1) * (Gamma (a + z y) * Gamma (b + z y) *
        (((α * x ^ 2 : ℝ)) : ℂ) ^ (-z y) * cexp (z y ^ 2) / z y) =
        ((x : ℂ) ^ ((v : ℂ) * I - 1) * (((α * x ^ 2 : ℝ)) : ℂ) ^ (-z y)) *
          (Gamma (a + z y) * Gamma (b + z y) * cexp (z y ^ 2) / z y) by ring, e]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  congr 1
  -- integrability on the product
  set C : ℝ := Real.Gamma (a.re + 2) * Real.Gamma (b.re + 2) * (Real.exp (2 ^ 2) * 2⁻¹)
  have hC : 0 ≤ C := by
    have := Real.Gamma_pos_of_pos ha; have := Real.Gamma_pos_of_pos hb; positivity
  have hnF : ∀ x ∈ Ioi (1:ℝ), ∀ y, ‖F x y‖ ≤ α ^ (-(2:ℝ)) * C * (x ^ (-(5:ℝ)) * Real.exp (-1 * y ^ 2)) := by
    intro x hx y
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only [hF]
    rw [norm_mul, norm_mul, norm_ofReal_cpow hα, norm_ofReal_cpow hx0]
    have r1 : (-z y).re = -2 := by simp [hzre]
    have r2 : ((v : ℂ) * I - 1 - 2 * z y).re = -5 := by simp [hzre]; norm_num
    rw [r1, r2]
    have := norm_gl_le ha hb y
    calc α ^ (-2:ℝ) * x ^ (-5:ℝ) * ‖gl a b y‖ ≤ α ^ (-2:ℝ) * x ^ (-5:ℝ) * (C * Real.exp (-1 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hmeasF : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun q : ℝ × ℝ => (α : ℂ) ^ (-z q.2) :=
      (Continuous.const_cpow (f := fun y : ℝ => -z y) (by fun_prop)
        (Or.inl (by exact_mod_cast hα.ne'))).measurable.comp measurable_snd
    have h2 : Measurable fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z q.2) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow
        ((by fun_prop : Continuous fun y : ℝ => (v : ℂ) * I - 1 - 2 * z y).measurable.comp measurable_snd)
    have h3 : Measurable fun q : ℝ × ℝ => gl a b q.2 := (continuous_gl ha hb).measurable.comp measurable_snd
    exact (h1.mul h2).mul h3
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioi (1:ℝ))).prod volume) := by
    have hdom : Integrable (fun q : ℝ × ℝ => (α ^ (-(2:ℝ)) * C * q.1 ^ (-(5:ℝ))) * Real.exp (-1 * q.2 ^ 2))
        ((volume.restrict (Ioi (1:ℝ))).prod volume) := by
      refine Integrable.mul_prod (f := fun x : ℝ => α ^ (-(2:ℝ)) * C * x ^ (-(5:ℝ)))
        (g := fun y : ℝ => Real.exp (-1 * y ^ 2)) ?_ (integrable_exp_neg_mul_sq one_pos)
      exact (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine hdom.mono' hmeasF.aestronglyMeasurable ?_
    have hm : (volume.restrict (Ioi (1:ℝ))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioi 1 ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hm]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).2
      (Eventually.of_forall fun q hq => ?_)
    have := hnF q.1 hq.1 q.2
    show ‖F q.1 q.2‖ ≤ _
    rw [show α ^ (-(2:ℝ)) * C * q.1 ^ (-(5:ℝ)) * Real.exp (-1 * q.2 ^ 2) =
      α ^ (-(2:ℝ)) * C * (q.1 ^ (-(5:ℝ)) * Real.exp (-1 * q.2 ^ 2)) by ring]
    exact this
  rw [integral_integral_swap hint]
  congr 1; ext y
  simp only [hF]
  have e : ∫ x in Ioi (1:ℝ), (α : ℂ) ^ (-z y) * (x : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z y) * gl a b y =
      (α : ℂ) ^ (-z y) * gl a b y * ∫ x in Ioi (1:ℝ), (x : ℂ) ^ ((v : ℂ) * I - 1 - 2 * z y) := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [e, integral_Ioi_one_cpow v (hzre y)]
  simp only [gl, hzdef]
  field_simp

end RamanujanTau.SelbergKeyDiag2
