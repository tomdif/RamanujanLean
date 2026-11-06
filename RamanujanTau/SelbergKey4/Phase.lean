/-
# M2.0: the phase `U(u, u+v)` of the lag expansion and its `u`-derivatives

`Ush u (u+v) = (2π)^{iv} e(u) conj(e(u+v))`, `e(u) = Γ(6+iu)/|Γ(6+iu)|` (`Ush_eq`).

* `hasDerivAt_eG`: `e'(u) = i Re ψ(6+iu) e(u)`;
* `hasDerivAt_Ulag`: `∂_u U(u,u+v) = i δ(u) U`, `δ(u) = Re ψ(6+iu) − Re ψ(6+i(u+v))`;
* `hasDerivAt_Ulag1`: `∂_u (iδU) = (iδ' − δ²) U`, `δ'(u) = Re(iψ'(6+iu)) − Re(iψ'(6+i(u+v)))`;
* `norm_Ulag_le`: for `|v| ≤ 1`: `|U| = 1`, `|U'| ≤ C/(1+|u|)`, `|U''| ≤ C/(1+|u|)²`.
Level 1.
-/
import RamanujanTau.SelbergKey3.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
  RamanujanTau.HeckeAFE3 RamanujanTau.SelbergKey
open scoped Real ComplexConjugate

/-- `Γ(6+iu)`. -/
noncomputable def Gl (u : ℝ) : ℂ := Gamma (6 + u * I)

/-- The unimodular phase `e(u) = Γ(6+iu)/|Γ(6+iu)|`. -/
noncomputable def eG (u : ℝ) : ℂ := Gl u / ((‖Gl u‖ : ℝ) : ℂ)

/-- `Re ψ(6+iu)`. -/
noncomputable def psR (u : ℝ) : ℝ := (digamma (6 + u * I)).re

/-- `Re (i ψ'(6+iu))`, the derivative of `psR`. -/
noncomputable def psR1 (u : ℝ) : ℝ := (I * deriv digamma (6 + u * I)).re

lemma Gl_ne (u : ℝ) : Gl u ≠ 0 := Gamma_line_ne u

lemma normGl_pos (u : ℝ) : 0 < ‖Gl u‖ := norm_pos_iff.2 (Gl_ne u)

lemma norm_eG (u : ℝ) : ‖eG u‖ = 1 := by
  unfold eG
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (normGl_pos u),
    div_self (normGl_pos u).ne']

lemma hasDerivAt_Gl (u : ℝ) : HasDerivAt Gl (I * digamma (6 + u * I) * Gl u) u := by
  have := hasDerivAt_Gamma_line (x := 0) (by norm_num) 0 u
  simp only [ofReal_zero, zero_mul, add_zero] at this
  rw [deriv_Gamma_eq (by simp : (0:ℝ) < (6 + u * I).re)] at this
  unfold Gl
  convert this using 1; ring

lemma hasDerivAt_normGl (u : ℝ) :
    HasDerivAt (fun w => ‖Gl w‖) (-(‖Gl u‖ * (digamma (6 + u * I)).im)) u := by
  have h1 := (hasDerivAt_Gl u).norm_sq
  have hpos := normGl_pos u
  have h2 := h1.sqrt (by positivity)
  have e : (fun w => Real.sqrt (‖Gl w‖ ^ 2)) = fun w => ‖Gl w‖ := by
    funext w; exact Real.sqrt_sq (norm_nonneg _)
  rw [e] at h2
  convert h2 using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  have hin : (inner ℝ (Gl u) (I * digamma (6 + u * I) * Gl u) : ℝ) =
      -(‖Gl u‖ ^ 2 * (digamma (6 + u * I)).im) := by
    rw [Complex.inner]
    rw [mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_mul_ofReal]
    simp; ring
  rw [hin]
  field_simp

theorem hasDerivAt_eG (u : ℝ) : HasDerivAt eG (I * (psR u : ℂ) * eG u) u := by
  have hN := (hasDerivAt_normGl u).ofReal_comp
  have h := (hasDerivAt_Gl u).div hN (by exact_mod_cast (normGl_pos u).ne')
  unfold eG
  convert h using 1
  have hN0 : ((‖Gl u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normGl_pos u).ne'
  unfold psR
  set ψ := digamma (6 + u * I)
  have hψ : ψ = (ψ.re : ℂ) + (ψ.im : ℂ) * I := (Complex.re_add_im ψ).symm
  field_simp
  push_cast
  rw [hψ]
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasDerivAt_conj_eG (u : ℝ) :
    HasDerivAt (fun w => conj (eG w)) (conj (I * (psR u : ℂ) * eG u)) u :=
  (hasDerivAt_eG u).star

/-- **The phase as a product of unimodular factors.** -/
theorem Ush_eq (u v : ℝ) :
    Ush u (u + v) = (2 * π : ℂ) ^ ((v : ℂ) * I) * (eG u * conj (eG (u + v))) := by
  unfold Ush eG Gl
  have h1 : Gamma (6 - ((u + v : ℝ) : ℂ) * I) = conj (Gamma (6 + ((u + v : ℝ) : ℂ) * I)) := by
    rw [← Complex.Gamma_conj]; congr 1; apply Complex.ext <;> simp
  rw [h1, map_div₀, Complex.conj_ofReal]
  rw [show (((u + v - u : ℝ)) : ℂ) = (v : ℂ) by push_cast; ring]
  push_cast
  have ha : ((‖Gamma (6 + ↑u * I)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normGl_pos u).ne'
  have hb : ((‖Gamma (6 + (↑u + ↑v) * I)‖ : ℝ) : ℂ) ≠ 0 := by
    have := normGl_pos (u + v); unfold Gl at this; push_cast at this; exact_mod_cast this.ne'
  field_simp

/-- `U(u) = U(u, u+v)`. -/
noncomputable def Ulag (v u : ℝ) : ℂ := Ush u (u + v)

/-- `δ(u) = Re ψ(6+iu) − Re ψ(6+i(u+v))`. -/
noncomputable def dlt (v u : ℝ) : ℝ := psR u - psR (u + v)

/-- `δ'(u)`. -/
noncomputable def dlt1 (v u : ℝ) : ℝ := psR1 u - psR1 (u + v)

theorem hasDerivAt_Ulag (v u : ℝ) :
    HasDerivAt (Ulag v) (I * (dlt v u : ℂ) * Ulag v u) u := by
  have h1 := hasDerivAt_eG u
  have h2 := (hasDerivAt_conj_eG (u + v)).comp_add_const u v
  have h := (h1.mul h2).const_mul ((2 * π : ℂ) ^ ((v : ℂ) * I))
  have e : Ulag v = fun w => (2 * π : ℂ) ^ ((v : ℂ) * I) * (eG w * conj (eG (w + v))) := by
    funext w; exact Ush_eq w v
  rw [e]
  convert h using 1
  unfold dlt
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma differentiable_digamma_line (u : ℝ) :
    HasDerivAt (fun w : ℝ => digamma (6 + w * I)) (I * deriv digamma (6 + u * I)) u := by
  have hmem : (6 + (u : ℂ) * I) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp
  have hd : DifferentiableAt ℂ digamma (6 + (u : ℂ) * I) :=
    (analyticOnNhd_digamma _ hmem).differentiableAt
  have hin : HasDerivAt (fun w : ℝ => 6 + (w : ℂ) * I) I u := by
    have := (((hasDerivAt_id u).ofReal_comp).mul_const I).const_add 6
    simpa using this
  have := hd.hasDerivAt.comp u hin
  convert this using 1; ring

lemma hasDerivAt_psR (u : ℝ) : HasDerivAt psR (psR1 u) u := by
  have h := (differentiable_digamma_line u)
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  unfold psR psR1
  simpa using this

theorem hasDerivAt_dlt (v u : ℝ) : HasDerivAt (dlt v) (dlt1 v u) u := by
  have h1 := hasDerivAt_psR u
  have h2 := (hasDerivAt_psR (u + v)).comp_add_const u v
  unfold dlt dlt1
  exact h1.sub h2

/-- `U'' = (iδ' − δ²) U`. -/
theorem hasDerivAt_Ulag1 (v u : ℝ) :
    HasDerivAt (fun w => I * (dlt v w : ℂ) * Ulag v w)
      ((I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u) u := by
  have h1 := ((hasDerivAt_dlt v u).ofReal_comp).const_mul I
  have h := h1.mul (hasDerivAt_Ulag v u)
  convert h using 1
  ring_nf; rw [Complex.I_sq]; ring

lemma continuous_psR1 : Continuous psR1 := by
  have hc := contDiff_line analyticOnNhd_digamma (v := 0) (by simp) 1
  simp only [add_zero] at hc
  have hcd : Continuous (deriv fun w : ℝ => digamma (6 + w * I)) := hc.continuous_deriv le_rfl
  have e : psR1 = fun w => (deriv (fun w : ℝ => digamma (6 + w * I)) w).re := by
    funext w; unfold psR1; rw [(differentiable_digamma_line w).deriv]
  rw [e]
  exact Complex.continuous_re.comp hcd

lemma continuous_psR : Continuous psR :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_psR u).continuousAt

lemma continuous_Ulag (v : ℝ) : Continuous (Ulag v) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_Ulag v u).continuousAt

lemma continuous_Ulag2 (v : ℝ) :
    Continuous fun u => (I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u := by
  have h1 : Continuous (dlt1 v) := continuous_psR1.sub (continuous_psR1.comp (by fun_prop))
  have h2 : Continuous (dlt v) := continuous_psR.sub (continuous_psR.comp (by fun_prop))
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp h1)).sub
    ((Complex.continuous_ofReal.comp h2).pow 2)).mul (continuous_Ulag v)

lemma norm_Ulag (v u : ℝ) : ‖Ulag v u‖ = 1 := by
  unfold Ulag; exact norm_Ush u (u + v)

/-! ## Bounds -/

lemma line_shift (u v : ℝ) : (6 + (u : ℂ) * I) + (((0:ℝ) : ℂ) + v * I) = 6 + ((u + v : ℝ) : ℂ) * I := by
  push_cast; ring

theorem abs_dlt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |v| ≤ 1 → |dlt v u| ≤ C / (1 + |u|) := by
  obtain ⟨C, hC0, hC⟩ := norm_digamma_diff_le (x := 0) (by norm_num)
  refine ⟨4 * C, by positivity, fun u v hv => ?_⟩
  have h := hC u v
  rw [line_shift] at h
  unfold dlt psR
  have h1 : |(digamma (6 + (u : ℂ) * I)).re - (digamma (6 + ((u + v : ℝ) : ℂ) * I)).re| ≤
      ‖digamma (6 + ((u + v : ℝ) : ℂ) * I) - digamma (6 + (u : ℂ) * I)‖ := by
    rw [abs_sub_comm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
  refine h1.trans (h.trans ?_)
  have hv1 : (1 + |v|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg v]
  have hu : 0 < 1 + |u| := by positivity
  rw [div_le_div_iff_of_pos_right hu]
  nlinarith

theorem abs_dlt1_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |v| ≤ 1 → |dlt1 v u| ≤ C / (1 + |u|) ^ 2 := by
  obtain ⟨D, hD0, hD⟩ := norm_iteratedDeriv_digamma_diff_le (x := 0) (by norm_num) 1
  refine ⟨8 * D, by positivity, fun u v hv => ?_⟩
  have h := hD u v
  rw [line_shift, iteratedDeriv_one] at h
  unfold dlt1 psR1
  have h1 : |(I * deriv digamma (6 + (u : ℂ) * I)).re -
        (I * deriv digamma (6 + ((u + v : ℝ) : ℂ) * I)).re| ≤
      ‖deriv digamma (6 + ((u + v : ℝ) : ℂ) * I) - deriv digamma (6 + (u : ℂ) * I)‖ := by
    rw [abs_sub_comm, ← Complex.sub_re, ← mul_sub]
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, one_mul]
  refine h1.trans (h.trans ?_)
  have hv1 : (1 + |v|) ^ (1 + 2) ≤ 8 := by
    have : 1 + |v| ≤ 2 := by linarith
    calc (1 + |v|) ^ (1 + 2) ≤ 2 ^ (1 + 2) := by gcongr
      _ = 8 := by norm_num
  have hu : 0 < (1 + |u|) ^ (1 + 1) := by positivity
  rw [show (2 : ℕ) = 1 + 1 from rfl, div_le_div_iff_of_pos_right hu]
  nlinarith

/-- **M2.0: the phase and its first two `u`-derivatives** (for `|v| ≤ 1`). -/
theorem Ulag_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |v| ≤ 1 →
    ‖Ulag v u‖ = 1 ∧ ‖I * (dlt v u : ℂ) * Ulag v u‖ ≤ C / (1 + |u|) ∧
      ‖(I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u‖ ≤ C / (1 + |u|) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_dlt_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := abs_dlt1_le
  refine ⟨C₁ + C₂ + C₁ ^ 2, by positivity, fun u v hv => ⟨norm_Ulag v u, ?_, ?_⟩⟩
  · rw [norm_mul, norm_mul, norm_Ulag, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
    refine (hC₁ u v hv).trans ?_
    have hu : 0 < 1 + |u| := by positivity
    rw [div_le_div_iff_of_pos_right hu]; nlinarith
  · have hu : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
    have hu0 : 0 < 1 + |u| := by linarith
    rw [norm_mul, norm_Ulag, mul_one]
    have hd := hC₁ u v hv
    have hd1 := hC₂ u v hv
    have hsq : |dlt v u| ^ 2 ≤ C₁ ^ 2 / (1 + |u|) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    calc ‖I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2‖
        ≤ ‖I * (dlt1 v u : ℂ)‖ + ‖(dlt v u : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = |dlt1 v u| + |dlt v u| ^ 2 := by
          rw [norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ C₂ / (1 + |u|) ^ 2 + C₁ ^ 2 / (1 + |u|) ^ 2 := add_le_add hd1 hsq
      _ ≤ (C₁ + C₂ + C₁ ^ 2) / (1 + |u|) ^ 2 := by
          rw [← add_div]; gcongr; linarith

end RamanujanTau.SelbergKey4
