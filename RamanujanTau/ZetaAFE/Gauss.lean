/-
# The Gaussian Mellin kernel

For `c > 0` and real `L`,

    ∫_ℝ e^{(c+iy)² − (c+iy)L} / (c+iy) dy = π · V(L),     V(L) = ∫_{u>L} e^{−u²/4}/√π du.

Proof: `e^{−zL}/z = ∫_{u>L} e^{−zu} du` (`Re z = c > 0`), Fubini, and the Gaussian integral
`∫_ℝ e^{(c+iy)² − (c+iy)u} dy = √π e^{−u²/4}` (`integral_cexp_quadratic`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

/-- The Gaussian density `g(u) = e^{−u²/4}/√π` (total mass `2`). -/
noncomputable def gk (u : ℝ) : ℝ := Real.exp (-(u ^ 2) / 4) / Real.sqrt Real.pi

/-- `V(L) = ∫_{u>L} g`. -/
noncomputable def V (L : ℝ) : ℝ := ∫ u in Ioi L, gk u

lemma gk_pos (u : ℝ) : 0 < gk u := by unfold gk; positivity

lemma continuous_gk : Continuous gk := by
  unfold gk; fun_prop

lemma gk_eq (u : ℝ) : gk u = 1 / Real.sqrt Real.pi * Real.exp (-(1 / 4) * u ^ 2) := by
  unfold gk; rw [div_eq_mul_inv, mul_comm, one_div]; congr 2; ring

lemma integrable_gk : Integrable gk := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul (1 / Real.sqrt Real.pi)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [gk_eq]

lemma integral_gk : ∫ u, gk u = 2 := by
  simp_rw [gk_eq]
  rw [integral_const_mul, integral_gaussian]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [show Real.pi / (1 / 4) = 4 * Real.pi by ring, Real.sqrt_mul (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  field_simp

lemma V_nonneg (L : ℝ) : 0 ≤ V L :=
  setIntegral_nonneg measurableSet_Ioi fun u _ => (gk_pos u).le

lemma V_le_two (L : ℝ) : V L ≤ 2 := by
  rw [← integral_gk]
  exact setIntegral_le_integral integrable_gk (Eventually.of_forall fun u => (gk_pos u).le)

lemma gk_le (u : ℝ) : gk u ≤ Real.exp (1 - u) / Real.sqrt Real.pi := by
  unfold gk
  gcongr
  nlinarith [sq_nonneg (u / 2 - 1)]

/-- `V(L) ≤ e^{1−L}/√π ≤ 2 e^{−L}`. -/
lemma V_le_exp (L : ℝ) : V L ≤ 2 * Real.exp (-L) := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (1 - u) / Real.sqrt Real.pi) (Ioi L) := by
    have h : IntegrableOn (fun u : ℝ => Real.exp 1 / Real.sqrt Real.pi * Real.exp (-1 * u)) (Ioi L) :=
      Integrable.const_mul (exp_neg_integrableOn_Ioi L (b := 1) one_pos) _
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [sub_eq_add_neg, Real.exp_add]; ring_nf
  have h1 : V L ≤ ∫ u in Ioi L, Real.exp (1 - u) / Real.sqrt Real.pi :=
    setIntegral_mono_on integrable_gk.integrableOn hint measurableSet_Ioi fun u _ => gk_le u
  have h2 : ∫ u in Ioi L, Real.exp (1 - u) / Real.sqrt Real.pi =
      Real.exp 1 / Real.sqrt Real.pi * Real.exp (-L) := by
    rw [← integral_exp_neg_Ioi L, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [sub_eq_add_neg, Real.exp_add]; ring
  rw [h2] at h1
  refine h1.trans ?_
  gcongr
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs : (1.7 : ℝ) < Real.sqrt Real.pi := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `V(a) = ∫_a^b g + V(b)`. -/
lemma V_eq_add {a b : ℝ} (hab : a ≤ b) : V a = (∫ u in a..b, gk u) + V b := by
  unfold V
  rw [intervalIntegral.integral_of_le hab, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi integrable_gk.integrableOn integrable_gk.integrableOn, Ioc_union_Ioi_eq_Ioi hab]

lemma V_eq_sub (L : ℝ) : V L = V 0 - ∫ u in (0:ℝ)..L, gk u := by
  rcases le_total 0 L with h | h
  · rw [V_eq_add h]; ring
  · rw [V_eq_add h, intervalIntegral.integral_symm]; ring

lemma hasDerivAt_V (L : ℝ) : HasDerivAt V (-gk L) L := by
  have h := (continuous_gk.integral_hasStrictDerivAt 0 L).hasDerivAt
  have : V = fun x => V 0 - ∫ u in (0:ℝ)..x, gk u := funext V_eq_sub
  rw [this]
  exact h.const_sub _

lemma antitone_V : Antitone V := by
  intro a b hab
  rw [V_eq_add hab]
  have : 0 ≤ ∫ u in a..b, gk u :=
    intervalIntegral.integral_nonneg hab fun u _ => (gk_pos u).le
  linarith

lemma continuous_V : Continuous V :=
  continuous_iff_continuousAt.mpr fun L => (hasDerivAt_V L).continuousAt

/-! ## The Gaussian line integral -/

lemma norm_cexp_line (c y u : ℝ) :
    ‖cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * u)‖ =
      Real.exp (c ^ 2 - y ^ 2 - c * u) := by
  rw [Complex.norm_exp]; congr 1
  simp [sq]

/-- `∫_ℝ e^{(c+iy)² − (c+iy)u} dy = √π e^{−u²/4}`. -/
lemma integral_quad (c u : ℝ) :
    ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * u) =
      ((Real.sqrt Real.pi * Real.exp (-(u ^ 2) / 4) : ℝ) : ℂ) := by
  have h : ∀ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * u) =
      cexp ((-1 : ℂ) * (y : ℂ) ^ 2 + (I * (2 * c - u)) * y + ((c : ℂ) ^ 2 - c * u)) := by
    intro y; congr 1; ring_nf; rw [I_sq]; ring
  simp_rw [h]
  rw [integral_cexp_quadratic (by simp)]
  have h1 : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast; rfl
  rw [h1]
  push_cast
  congr 2
  ring_nf; rw [I_sq]; ring

/-- `e^{−zL}/z = ∫_{u>L} e^{−zu}` for `Re z > 0`. -/
lemma exp_div_eq_integral {z : ℂ} (hz : 0 < z.re) (L : ℝ) :
    cexp (-z * L) / z = ∫ u in Ioi L, cexp (-z * u) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hz)]
  have : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  field_simp

lemma integrable_prod_line {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable (Function.uncurry fun (y u : ℝ) =>
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * u))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi L))) := by
  have hf : Integrable (fun y : ℝ => Real.exp (-1 * y ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have hg : Integrable (fun u : ℝ => Real.exp (c ^ 2) * Real.exp (-c * u)) (volume.restrict (Ioi L)) :=
    (exp_neg_integrableOn_Ioi L hc).const_mul _
  have hprod := hf.mul_prod hg
  refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [Function.uncurry_apply_pair, norm_cexp_line]
    rw [← Real.exp_add, ← Real.exp_add]
    apply le_of_eq; congr 1; ring

/-- **The Gaussian line integral**: `∫_ℝ e^{z²−zL}/z dy = π V(L)` on `z = c + iy`, `c > 0`. -/
theorem line_gauss {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * L) / ((c : ℂ) + y * I) =
      (Real.pi : ℂ) * (V L : ℂ) := by
  have h1 : ∀ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * L) / ((c : ℂ) + y * I) =
      ∫ u in Ioi L, cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * u) := by
    intro y
    have hre : 0 < ((c : ℂ) + y * I).re := by simpa using hc
    rw [sub_eq_add_neg, Complex.exp_add, mul_div_assoc, neg_mul_eq_neg_mul,
      exp_div_eq_integral hre L, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [h1]
  rw [integral_integral_swap (integrable_prod_line hc L)]
  simp_rw [integral_quad]
  have hpi : Real.pi = Real.sqrt Real.pi * Real.sqrt Real.pi :=
    (Real.mul_self_sqrt Real.pi_pos.le).symm
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hx : ∀ x : ℝ, Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4) = Real.pi * gk x := by
    intro x; unfold gk; rw [mul_div_assoc', eq_div_iff hs, mul_comm, ← mul_assoc, ← hpi]
  simp_rw [hx]
  rw [integral_complex_ofReal, integral_const_mul]
  unfold V
  push_cast; rfl

/-- `∫_ℝ e^{z²}/z dy = π` on `Re z = c > 0`. -/
theorem line_gauss_zero {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) = (Real.pi : ℂ) := by
  have h := line_gauss hc 0
  have hV : V 0 = 1 := by
    have h2 : ∫ x, gk |x| = 2 * ∫ x in Ioi (0 : ℝ), gk x := integral_comp_abs
    have h3 : (fun x => gk |x|) = gk := by funext x; simp [gk, sq_abs]
    rw [h3, integral_gk] at h2
    unfold V; linarith
  rw [hV] at h
  simpa using h

end RamanujanTau.ZetaAFE
