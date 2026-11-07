/-
# M3 step 3a: the test function `f(t) = t^{iv} W̃_{u,u+v}(αt²)` and its derivative

* `Wd u v ξ = ∂_ξ W̃_{u,u+v}(ξ)`; `hasDerivAt_Wd`; `norm_xi_Wd_small`: `|ξ W̃'(ξ)| ≤ C (ξ/T(u)T(u+v))^{1/20}`;
  `norm_xi_Wd_decay`: `|ξ W̃'(ξ)| ≤ C (1 + ξ/T(u)T(u+v))^{−A}`;
* `ft`, `ft'`, `hasDerivAt_ft` (for `t > 0`), and the bounds `norm_ft_le`, `norm_ft'_le`.
Level 1.
-/
import RamanujanTau.SelbergKey4.XiDeriv
import RamanujanTau.SelbergKeyDiag2.Mellin

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey3 RamanujanTau.SelbergKey4
open scoped Real

/-- `TT = T(u)T(u+v)`. -/
noncomputable def TT (u v : ℝ) : ℝ := Tq u * Tq (u + v)

lemma TT_pos (u v : ℝ) : 0 < TT u v := mul_pos (Tq_pos u) (Tq_pos (u + v))

/-- `W̃'(ξ)`. -/
noncomputable def Wd (u v ξ : ℝ) : ℂ := deriv (fun ξ' => Wsh u (u + v) ξ') ξ

lemma hasDerivAt_Wd (u v : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun ξ' => Wsh u (u + v) ξ') (Wd u v ξ) ξ := by
  obtain ⟨C, -, hC⟩ := Wxi_bound (A := 0) le_rfl
  have h := (hC u v ξ hξ).1
  rw [Wd, h.deriv]; exact h

theorem norm_xi_Wd_decay {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v ξ : ℝ, 0 < ξ → ‖(ξ : ℂ) * Wd u v ξ‖ ≤ C * (1 + ξ / TT u v) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := Wxi_bound hA
  refine ⟨C, hC0, fun u v ξ hξ => ?_⟩
  obtain ⟨h1, h2⟩ := hC u v ξ hξ
  rw [Wd, h1.deriv]; exact h2

theorem norm_xi_Wd_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v ξ : ℝ, 0 < ξ → ‖(ξ : ℂ) * Wd u v ξ‖ ≤ C * (ξ / TT u v) ^ (1 / 20 : ℝ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_xi_Wd_decay (A := 0) le_rfl
  obtain ⟨K, hK0, hK⟩ := norm_Vl_le (x := -1) le_rfl
  refine ⟨C₁ + K, by positivity, fun u v ξ hξ => ?_⟩
  set r := ξ / TT u v with hr
  have hr0 : 0 < r := div_pos hξ (TT_pos u v)
  rcases le_total r 1 with h | h
  · have hd := hasDerivAt_Wsh_xi_line (x := -1) le_rfl (by norm_num) u v hξ (fun ξ' hξ' => by
      rw [if_pos (by norm_num), Wsh_eq_one_add_Wl hξ' u v, add_comm])
    have e : Wd u v ξ = -(Vl (-1) v ξ u / ξ) := by rw [Wd, hd.deriv]
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    rw [e, show (ξ : ℂ) * -(Vl (-1) v ξ u / ξ) = -Vl (-1) v ξ u by field_simp, norm_neg]
    refine (hK v u ξ hξ).trans ?_
    have e2 : (Tq u * Tq (u + v) / ξ) ^ (-1:ℝ) = r := by
      rw [Real.rpow_neg_one, inv_div]; rfl
    rw [e2]
    have : r ≤ r ^ (1 / 20 : ℝ) := by
      calc r = r ^ (1:ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (1 / 20 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr0 h (by norm_num)
    nlinarith [Real.rpow_nonneg hr0.le (1 / 20 : ℝ)]
  · have h1 := hC₁ u v ξ hξ
    rw [neg_zero, Real.rpow_zero, mul_one] at h1
    have : 1 ≤ r ^ (1 / 20 : ℝ) := Real.one_le_rpow h (by norm_num)
    nlinarith

/-- `f(t) = t^{iv} W̃(αt²)`. -/
noncomputable def ft (u v α t : ℝ) : ℂ := (t : ℂ) ^ ((v : ℂ) * I) * Wsh u (u + v) (α * t ^ 2)

/-- `f'(t) = iv t^{iv−1} W̃(αt²) + t^{iv}·2αt·W̃'(αt²)`. -/
noncomputable def ft' (u v α t : ℝ) : ℂ :=
  (v : ℂ) * I * (t : ℂ) ^ ((v : ℂ) * I - 1) * Wsh u (u + v) (α * t ^ 2) +
    (t : ℂ) ^ ((v : ℂ) * I) * ((2 * α * t : ℝ) : ℂ) * Wd u v (α * t ^ 2)

lemma hasDerivAt_ofReal_cpow' {t : ℝ} (ht : 0 < t) (w : ℂ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) t :=
  (Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.2 ht)).hasDerivAt.comp_ofReal

theorem hasDerivAt_ft (u v : ℝ) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    HasDerivAt (ft u v α) (ft' u v α t) t := by
  have h1 := hasDerivAt_ofReal_cpow' ht ((v : ℂ) * I)
  have hin : HasDerivAt (fun s : ℝ => α * s ^ 2) (2 * α * t) t := by
    have := (hasDerivAt_pow 2 t).const_mul α
    convert this using 1; push_cast; ring
  have h2 := (hasDerivAt_Wd u v (show 0 < α * t ^ 2 by positivity)).scomp t hin
  have h3 := h1.mul h2
  unfold ft ft'
  convert h3 using 1
  simp only [Function.comp_def, real_smul]
  ring

lemma norm_cpow_I {t : ℝ} (ht : 0 < t) (v : ℝ) : ‖(t : ℂ) ^ ((v : ℂ) * I)‖ = 1 := by
  rw [norm_ofReal_cpow ht]; simp

lemma norm_cpow_I_sub_one {t : ℝ} (ht : 0 < t) (v : ℝ) :
    ‖(t : ℂ) ^ ((v : ℂ) * I - 1)‖ = t⁻¹ := by
  rw [norm_ofReal_cpow ht]; simp [Real.rpow_neg_one]

lemma norm_ft_eq (u v : ℝ) {α t : ℝ} (ht : 0 < t) : ‖ft u v α t‖ = ‖Wsh u (u + v) (α * t ^ 2)‖ := by
  unfold ft; rw [norm_mul, norm_cpow_I ht, one_mul]

/-- `|f'(t)| ≤ |v| t⁻¹ |W̃(αt²)| + 2 t⁻¹ |ξ W̃'(ξ)|`, `ξ = αt²`. -/
lemma norm_ft'_le (u v : ℝ) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ‖ft' u v α t‖ ≤ |v| * t⁻¹ * ‖Wsh u (u + v) (α * t ^ 2)‖ +
      2 * t⁻¹ * ‖((α * t ^ 2 : ℝ) : ℂ) * Wd u v (α * t ^ 2)‖ := by
  unfold ft'
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  have hn1 : ‖(v : ℂ) * I * (t : ℂ) ^ ((v : ℂ) * I - 1) * Wsh u (u + v) (α * t ^ 2)‖ =
      |v| * t⁻¹ * ‖Wsh u (u + v) (α * t ^ 2)‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_cpow_I_sub_one ht, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one]
  have hn2 : ‖(t : ℂ) ^ ((v : ℂ) * I) * ((2 * α * t : ℝ) : ℂ) * Wd u v (α * t ^ 2)‖ =
      2 * t⁻¹ * ‖((α * t ^ 2 : ℝ) : ℂ) * Wd u v (α * t ^ 2)‖ := by
    rw [norm_mul, norm_mul, norm_cpow_I ht, one_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    field_simp
  rw [hn1, hn2]

end RamanujanTau.SelbergKeyDiag2
