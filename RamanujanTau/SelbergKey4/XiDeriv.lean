/-
# M2.3: the `ξ`-derivative of the lag weight

On a line `Re z = x`, `∂_ξ [ξ^{−z} e^{z²}/z] = −ξ^{−1} ξ^{−z} e^{z²}`: the factor `1/z` disappears.
So `ξ ∂_ξ W̃_{u,u+v}(ξ) = −Vl x v ξ u`, `Vl x = ∫ R(u)R(−(u+v)) (2π)^{−1} ξ^{−z} e^{z²} dy`, on
**both** lines `x = A+1` and `x = −1` (`W̃ = Wl (A+1) = 1 + Wl (−1)`), and

    |Vl x v ξ u| ≤ K (T(u)T(u+v)/ξ)^x                         (`norm_Vl_le`).

* **`Wxi_bound`**: `ξ ↦ W̃_{u,u+v}(ξ)` is differentiable on `ξ > 0` and
  `|ξ ∂_ξ W̃_{u,u+v}(ξ)| ≤ C (1 + ξ/(T(u)T(u+v)))^{−A}`, uniformly in `u, v`.
Level 1.
-/
import RamanujanTau.SelbergKey4.FarTerm

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Complex MeasureTheory Set Metric Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
  RamanujanTau.HeckeAFE3 RamanujanTau.SelbergKey RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey3
open scoped Real

/-- `(2π)^{−1} ξ^{−z} e^{z²}`, `z = x + iy` (the kernel `Kf` without `1/z`). -/
noncomputable def Kz (x ξ y : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ((ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2))

/-- `Vl x v ξ u = ∫ Pf · Kz`. -/
noncomputable def Vl (x v ξ u : ℝ) : ℂ := ∫ y : ℝ, Pf x v u y * Kz x ξ y

lemma norm_Kz (x y : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖Kz x ξ y‖ = (2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) := by
  unfold Kz
  rw [norm_mul, norm_two_pi_inv, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
  have hr : (-((x : ℂ) + y * I)).re = -x := by simp
  rw [hr, show x ^ 2 - y ^ 2 = x ^ 2 + -1 * y ^ 2 by ring, Real.exp_add]
  ring

lemma continuous_Kz (x : ℝ) {ξ : ℝ} (hξ : 0 < ξ) : Continuous (Kz x ξ) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  unfold Kz
  refine continuous_const.mul (Continuous.mul ?_ (by fun_prop))
  exact continuous_iff_continuousAt.2 fun y =>
    ((continuousAt_const_cpow hξ0).comp (by fun_prop : Continuous fun y : ℝ =>
      -((x : ℂ) + y * I)).continuousAt)

lemma hasDerivAt_Kf_xi {x : ℝ} (hx0 : x ≠ 0) (y : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun ξ => Kf x ξ y) (-(Kz x ξ y / ξ)) ξ := by
  set z : ℂ := (x : ℂ) + y * I
  have hz : z ≠ 0 := line_ne_zero hx0 y
  have hmz : -z ≠ 0 := neg_ne_zero.2 hz
  have h := ((hasDerivAt_ofReal_cpow_const hξ.ne' hmz).mul_const (cexp (z ^ 2) / z)).const_mul
    (2 * π : ℂ)⁻¹
  have e : (fun ξ => Kf x ξ y) = fun ξ : ℝ => (2 * π : ℂ)⁻¹ * ((ξ : ℂ) ^ (-z) * (cexp (z ^ 2) / z)) := by
    funext w; unfold Kf; simp only [z]; ring
  rw [e]
  convert h using 1
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  unfold Kz
  rw [Complex.cpow_sub _ _ hξc, Complex.cpow_one]
  have hz' : ((x : ℂ) + y * I) ≠ 0 := hz
  simp only [z]
  field_simp


/-- `‖Pf‖ ≤ C² (T(u)T(u+v))^x (1+|y|)^{11+2x} e^{π|y|}`. -/
lemma norm_Pf_le {x : ℝ} (hx : -1 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v u y : ℝ, ‖Pf x v u y‖ ≤
      C * C * (Tq u * Tq (u + v)) ^ x * ((1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line (x := x) (by linarith)
  refine ⟨C, hC0, fun v u y => ?_⟩
  have hGp : ∀ t : ℝ, 0 < ‖Gamma (6 + t * I)‖ := fun t => norm_pos_iff.2 (Gamma_line_ne t)
  have hR : ∀ t : ℝ, ‖Rf x t y‖ ≤
      C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) := by
    intro t; unfold Rf; rw [norm_div, div_le_iff₀ (hGp t)]; exact hC t y
  have hR2 := hR (-(u + v))
  rw [Tq_neg] at hR2
  have hy1 : 0 < 1 + |y| := by positivity
  unfold Pf
  rw [norm_mul]
  calc ‖Rf x u y‖ * ‖Rf x (-(u + v)) y‖
      ≤ (C * Tq u ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2))) *
        (C * Tq (u + v) ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2))) :=
        mul_le_mul (hR u) hR2 (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Tq_pos u).le _)) (by positivity))
    _ = C * C * (Tq u ^ x * Tq (u + v) ^ x) *
        (((1 + |y|) ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x)) *
          (Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2))) := by ring
    _ = _ := by
        rw [← Real.mul_rpow (Tq_pos u).le (Tq_pos (u + v)).le, ← Real.rpow_add hy1, ← Real.exp_add]
        congr 3 <;> ring

/-- `‖Pf · Kz‖ ≤ P e^{−y²/2}` with the explicit `P`. -/
lemma norm_PfKz_le {x : ℝ} (hx : -1 ≤ x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v u ξ y : ℝ, 0 < ξ →
      ‖Pf x v u y * Kz x ξ y‖ ≤ K * (Tq u * Tq (u + v)) ^ x * ξ ^ (-x) *
        Real.exp (-(1 / 2) * y ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_Pf_le hx
  have hq : 0 ≤ 2 * (11 / 2 + x) := by linarith
  set E : ℝ := Real.exp ((2 * (11 / 2 + x) + π) ^ 2 / 2)
  refine ⟨C * C * E * ((2 * π)⁻¹ * Real.exp (x ^ 2)),
    mul_nonneg (mul_nonneg (mul_self_nonneg C) (Real.exp_pos _).le) (by positivity),
    fun v u ξ y hξ => ?_⟩
  rw [norm_mul, norm_Kz x y hξ]
  have hpe := poly_exp_bound2 hq y
  have hTT : 0 ≤ (Tq u * Tq (u + v)) ^ x :=
    Real.rpow_nonneg (mul_nonneg (Tq_pos u).le (Tq_pos (u + v)).le) _
  have hξx : 0 ≤ ξ ^ (-x) := Real.rpow_nonneg hξ.le _
  calc ‖Pf x v u y‖ * ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)))
      ≤ (C * C * (Tq u * Tq (u + v)) ^ x * ((1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|))) *
        ((2 * π)⁻¹ * (ξ ^ (-x) * Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2))) :=
        mul_le_mul_of_nonneg_right (hC v u y) (by positivity)
    _ = C * C * (Tq u * Tq (u + v)) ^ x * ((2 * π)⁻¹ * Real.exp (x ^ 2)) * ξ ^ (-x) *
        ((1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2)) := by ring
    _ ≤ C * C * (Tq u * Tq (u + v)) ^ x * ((2 * π)⁻¹ * Real.exp (x ^ 2)) * ξ ^ (-x) *
        (E * Real.exp (-(1 / 2) * y ^ 2)) := by gcongr
    _ = _ := by ring

lemma continuous_Pf_y {x : ℝ} (hx : -1 ≤ x) (v u : ℝ) : Continuous (fun y => Pf x v u y) := by
  have := continuous_Pd_y hx v 0 u
  simpa [Pd_zero] using this

lemma integrable_PfKz {x : ℝ} (hx : -1 ≤ x) (v u : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun y => Pf x v u y * Kz x ξ y) := by
  obtain ⟨K, -, hK⟩ := norm_PfKz_le hx
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul _)
    ((continuous_Pf_y hx v u).mul (continuous_Kz x hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y => hK v u ξ y hξ)

lemma Kf_eq_Kz_div (x ξ y : ℝ) : Kf x ξ y = Kz x ξ y / ((x : ℂ) + y * I) := by
  unfold Kf Kz; ring

lemma integrable_PfKf {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (v u : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun y => Pf x v u y * Kf x ξ y) := by
  obtain ⟨K, -, hK⟩ := norm_PfKz_le hx
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul
    (K * (Tq u * Tq (u + v)) ^ x * ξ ^ (-x) * |x|⁻¹))
    ((continuous_Pf_y hx v u).mul (continuous_Kf hx0 hξ)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hb := hK v u ξ y hξ
  have hz : |x| ≤ ‖(x : ℂ) + y * I‖ := norm_line_ge y
  have hx' : 0 < |x| := abs_pos.2 hx0
  rw [Kf_eq_Kz_div, mul_div_assoc', norm_div]
  calc ‖Pf x v u y * Kz x ξ y‖ / ‖(x : ℂ) + y * I‖
      ≤ ‖Pf x v u y * Kz x ξ y‖ / |x| := div_le_div_of_nonneg_left (norm_nonneg _) hx' hz
    _ ≤ K * (Tq u * Tq (u + v)) ^ x * ξ ^ (-x) * Real.exp (-(1 / 2) * y ^ 2) / |x| := by gcongr
    _ = _ := by ring

/-- **The bound on one line.** -/
theorem norm_Vl_le {x : ℝ} (hx : -1 ≤ x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v u ξ : ℝ, 0 < ξ →
      ‖Vl x v ξ u‖ ≤ K * (Tq u * Tq (u + v) / ξ) ^ x := by
  obtain ⟨K, hK0, hK⟩ := norm_PfKz_le hx
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨K * J, by positivity, fun v u ξ hξ => ?_⟩
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul
    (K * (Tq u * Tq (u + v)) ^ x * ξ ^ (-x))
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => hK v u ξ y hξ)
  rw [integral_const_mul] at hI
  unfold Vl
  refine hI.trans (le_of_eq ?_)
  rw [Real.div_rpow (mul_nonneg (Tq_pos u).le (Tq_pos (u + v)).le) hξ.le, Real.rpow_neg hξ.le]
  simp only [J]
  ring

/-- **Differentiation in `ξ` under the integral.** -/
theorem hasDerivAt_Wl_xi {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (v u : ℝ) {ξ₀ : ℝ} (hξ₀ : 0 < ξ₀) :
    HasDerivAt (fun ξ => Wl x v ξ u) (-(Vl x v ξ₀ u / ξ₀)) ξ₀ := by
  obtain ⟨K, hK0, hK⟩ := norm_PfKz_le hx
  set r : ℝ := ξ₀ / 2
  have hr : 0 < r := by positivity
  set Mξ : ℝ := (ξ₀ / 2) ^ (-x) + (3 * ξ₀ / 2) ^ (-x)
  set M : ℝ := K * (Tq u * Tq (u + v)) ^ x * Mξ * (2 / ξ₀)
  have hball : ∀ ξ ∈ ball ξ₀ r, ξ₀ / 2 < ξ ∧ ξ < 3 * ξ₀ / 2 := by
    intro ξ hξ
    rw [mem_ball, Real.dist_eq, abs_lt] at hξ
    simp only [r] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  have hpow : ∀ ξ ∈ ball ξ₀ r, ξ ^ (-x) ≤ Mξ := by
    intro ξ hξ
    obtain ⟨h1, h2⟩ := hball ξ hξ
    have hξp : 0 < ξ := by linarith
    rcases le_total 0 x with h | h
    · have : ξ ^ (-x) ≤ (ξ₀ / 2) ^ (-x) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1.le (by linarith)
      have : 0 ≤ (3 * ξ₀ / 2) ^ (-x) := by positivity
      linarith
    · have : ξ ^ (-x) ≤ (3 * ξ₀ / 2) ^ (-x) :=
        Real.rpow_le_rpow hξp.le h2.le (by linarith)
      have : 0 ≤ (ξ₀ / 2) ^ (-x) := by positivity
      linarith
  have hbound : ∀ᵐ y : ℝ, ∀ ξ ∈ ball ξ₀ r,
      ‖Pf x v u y * -(Kz x ξ y / ξ)‖ ≤ M * Real.exp (-(1 / 2) * y ^ 2) := by
    refine Eventually.of_forall fun y ξ hξ => ?_
    obtain ⟨h1, -⟩ := hball ξ hξ
    have hξp : 0 < ξ := by linarith
    have hinv : ξ⁻¹ ≤ 2 / ξ₀ := by
      rw [inv_le_comm₀ hξp (by positivity), inv_div]; linarith
    rw [norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξp,
      ← mul_div_assoc, div_eq_mul_inv]
    have hb := hK v u ξ y hξp
    rw [norm_mul] at hb
    have hTT : 0 ≤ (Tq u * Tq (u + v)) ^ x :=
      Real.rpow_nonneg (mul_nonneg (Tq_pos u).le (Tq_pos (u + v)).le) _
    calc ‖Pf x v u y‖ * ‖Kz x ξ y‖ * ξ⁻¹
        ≤ K * (Tq u * Tq (u + v)) ^ x * ξ ^ (-x) * Real.exp (-(1 / 2) * y ^ 2) * (2 / ξ₀) :=
          mul_le_mul hb hinv (by positivity) (by positivity)
      _ ≤ K * (Tq u * Tq (u + v)) ^ x * Mξ * Real.exp (-(1 / 2) * y ^ 2) * (2 / ξ₀) := by
          gcongr; exact hpow ξ hξ
      _ = M * Real.exp (-(1 / 2) * y ^ 2) := by simp only [M]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := ξ₀)
    (F := fun ξ y => Pf x v u y * Kf x ξ y) (F' := fun ξ y => Pf x v u y * -(Kz x ξ y / ξ))
    (bound := fun y => M * Real.exp (-(1 / 2) * y ^ 2)) (ball_mem_nhds ξ₀ hr)
    (by
      filter_upwards [ball_mem_nhds ξ₀ hr] with ξ hξ
      have hξp : 0 < ξ := by linarith [(hball ξ hξ).1]
      exact ((continuous_Pf_y hx v u).mul (continuous_Kf hx0 hξp)).aestronglyMeasurable)
    (integrable_PfKf hx hx0 v u hξ₀)
    ((continuous_Pf_y hx v u).mul ((continuous_Kz x hξ₀).div_const _).neg).aestronglyMeasurable
    hbound
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    (Eventually.of_forall fun y ξ hξ => by
      have hξp : 0 < ξ := by linarith [(hball ξ hξ).1]
      exact (hasDerivAt_Kf_xi hx0 y hξp).const_mul (Pf x v u y))
  have e : (∫ y : ℝ, Pf x v u y * -(Kz x ξ₀ y / ξ₀)) = -(Vl x v ξ₀ u / ξ₀) := by
    unfold Vl
    rw [← integral_div, ← integral_neg]
    congr 1; funext y; ring
  rw [← e]
  exact h.2

lemma hasDerivAt_Wsh_xi_line {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (u v : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (hW : ∀ ξ' : ℝ, 0 < ξ' → Wsh u (u + v) ξ' = Wl x v ξ' u + (if x < 0 then 1 else 0)) :
    HasDerivAt (fun ξ' => Wsh u (u + v) ξ') (-(Vl x v ξ u / ξ)) ξ := by
  have h := (hasDerivAt_Wl_xi hx hx0 v u hξ).add_const (if x < 0 then (1 : ℂ) else 0)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hξ] with ξ' hξ'
  exact hW ξ' hξ'

/-- **M2.3: `|ξ ∂_ξ W̃_{u,u+v}(ξ)| ≤ C (1 + ξ/(T(u)T(u+v)))^{−A}`**, uniformly in `u, v`. -/
theorem Wxi_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ' => Wsh u (u + v) ξ') (-(Vl (A + 1) v ξ u / ξ)) ξ ∧
      ‖(ξ : ℂ) * -(Vl (A + 1) v ξ u / ξ)‖ ≤ C * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_Vl_le (x := A + 1) (by linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_Vl_le (x := -1) le_rfl
  refine ⟨2 ^ (A + 1) * (K₁ + K₂), by positivity, fun u v ξ hξ => ?_⟩
  have hx1 : (0:ℝ) < A + 1 := by linarith
  have hd1 := hasDerivAt_Wsh_xi_line (x := A + 1) (by linarith) hx1.ne' u v hξ (fun ξ' hξ' => by
    rw [if_neg (by linarith), add_zero]; exact Wsh_eq_Wl_pos hx1 hξ' u v)
  have hd2 := hasDerivAt_Wsh_xi_line (x := -1) le_rfl (by norm_num) u v hξ (fun ξ' hξ' => by
    rw [if_pos (by norm_num), Wsh_eq_one_add_Wl hξ' u v, add_comm])
  refine ⟨hd1, ?_⟩
  have huniq := hd1.unique hd2
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have e1 : (ξ : ℂ) * -(Vl (A + 1) v ξ u / ξ) = -Vl (A + 1) v ξ u := by field_simp
  have e2 : (ξ : ℂ) * -(Vl (A + 1) v ξ u / ξ) = -Vl (-1) v ξ u := by rw [huniq]; field_simp
  have hTT : 0 < Tq u * Tq (u + v) := mul_pos (Tq_pos u) (Tq_pos (u + v))
  set r : ℝ := ξ / (Tq u * Tq (u + v))
  have hr : 0 < r := div_pos hξ hTT
  have hinv : Tq u * Tq (u + v) / ξ = r⁻¹ := by simp only [r]; rw [inv_div]
  set f : ℝ := ‖(ξ : ℂ) * -(Vl (A + 1) v ξ u / ξ)‖
  have hf1 : f ≤ K₁ * r ^ (-(A + 1)) := by
    simp only [f]; rw [e1, norm_neg]
    refine (hK₁ v u ξ hξ).trans (le_of_eq ?_)
    rw [hinv, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
  have hf2 : f ≤ K₂ * r := by
    simp only [f]; rw [e2, norm_neg]
    refine (hK₂ v u ξ hξ).trans (le_of_eq ?_)
    rw [hinv, Real.inv_rpow hr.le, Real.rpow_neg_one, inv_inv]
  exact combine_r hA hK₁0 hK₂0 hr hf1 hf2

end RamanujanTau.SelbergKey4
