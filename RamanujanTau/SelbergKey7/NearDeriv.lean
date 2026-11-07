/-
# Seventh pass, R3 (near part): the derivative of `H_ℓ`

For `P, Q ≥ 1`, `|v| ≤ 1`, `r > 0` and `2|ℓ| ≤ r`, with `ñ(r) = (Pr − ℓ)/Q`:

    ‖H_ℓ(r)‖ ≤ K Q / r,     ‖H_ℓ'(r)‖ ≤ K Q (1/r² + |u||ℓ|/r³)                    (`Hl_deriv`).

The `ξ`-derivative of `W̃` enters only through `SelbergKey4.Wxi_bound` (`|ξ ∂_ξ W̃| ≤ C`), and
`|W̃| ≤ C` is `SelbergKey2.Wsh_bound`. Level 1.
-/
import RamanujanTau.SelbergKey7.NearId

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex RamanujanTau.SelbergKey RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey4
open scoped Real

/-- `∂_ξ W̃`. -/
noncomputable def Wd (u v ξ : ℝ) : ℂ := -(Vl ((0 : ℝ) + 1) v ξ u / ξ)

lemma W_consts : ∃ CW Cξ : ℝ, 0 ≤ CW ∧ 0 ≤ Cξ ∧
    (∀ u u' ξ : ℝ, 0 < ξ → ‖Wsh u u' ξ‖ ≤ CW) ∧
    (∀ u v ξ : ℝ, 0 < ξ → HasDerivAt (fun ξ' => Wsh u (u + v) ξ') (Wd u v ξ) ξ ∧
      ‖(ξ : ℂ) * Wd u v ξ‖ ≤ Cξ) := by
  obtain ⟨CW, hCW0, hCW⟩ := Wsh_bound (A := 0) le_rfl
  obtain ⟨Cξ, hCξ0, hCξ⟩ := Wxi_bound (A := 0) le_rfl
  refine ⟨CW, Cξ, hCW0, hCξ0, fun u u' ξ hξ => ?_, fun u v ξ hξ => ?_⟩
  · have := hCW u u' ξ hξ; rwa [neg_zero, Real.rpow_zero, mul_one] at this
  · obtain ⟨h1, h2⟩ := hCξ u v ξ hξ
    rw [neg_zero, Real.rpow_zero, mul_one] at h2
    exact ⟨h1, h2⟩

lemma norm_cexp_Ef_le {u v r s Q : ℝ} (hr : 0 < r) (hs : 0 < s) (hQ : 1 ≤ Q)
    (hrs : (r / (2 * Q)) ^ 2 ≤ r * s) : ‖cexp (Ef u v r s)‖ ≤ 2 * Q / r := by
  rw [Complex.norm_exp]
  have hre : (Ef u v r s).re = -(1 / 2) * (Real.log r + Real.log s) := by
    simp [Ef]
  rw [hre, ← Real.log_mul hr.ne' hs.ne']
  have hq : 0 < r / (2 * Q) := by positivity
  have h1 : Real.log ((r / (2 * Q)) ^ 2) ≤ Real.log (r * s) := Real.log_le_log (by positivity) hrs
  rw [Real.log_pow] at h1
  have h2 : -(1 / 2) * Real.log (r * s) ≤ Real.log ((r / (2 * Q))⁻¹) := by
    rw [Real.log_inv]; push_cast at h1; linarith
  calc Real.exp (-(1 / 2) * Real.log (r * s)) ≤ Real.exp (Real.log ((r / (2 * Q))⁻¹)) :=
        Real.exp_le_exp.2 h2
    _ = 2 * Q / r := by rw [Real.exp_log (by positivity), inv_div]

/-- `ρ = P/(Pr − ℓ)` bounds. -/
lemma rho_bounds {P r ℓ : ℝ} (hP : 1 ≤ P) (hr : 0 < r) (hℓ : 2 * |ℓ| ≤ r) :
    P * r / 2 ≤ P * r - ℓ ∧ P / (P * r - ℓ) ≤ 2 / r ∧
      |P / (P * r - ℓ) - r⁻¹| ≤ 2 * |ℓ| / r ^ 2 := by
  have hl := le_abs_self ℓ
  have hPr : r ≤ P * r := le_mul_of_one_le_left hr.le hP
  have hy : P * r / 2 ≤ P * r - ℓ := by linarith
  have hy0 : 0 < P * r - ℓ := by nlinarith
  refine ⟨hy, ?_, ?_⟩
  · rw [div_le_div_iff₀ hy0 hr]; nlinarith
  · have e : P / (P * r - ℓ) - r⁻¹ = ℓ / (r * (P * r - ℓ)) := by field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : 0 < r * (P * r - ℓ))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : r ^ 2 ≤ 2 * (r * (P * r - ℓ)) := by nlinarith
    nlinarith [abs_nonneg ℓ]

lemma norm_ofReal_add_mul_I_le (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * I‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- The derivative of `r ↦ H_ℓ(r)`, explicitly. -/
lemma hasDerivAt_Hl (P Q : ℕ) (ℓ : ℤ) (u v r : ℝ) (hr : 0 < r) (hn : 0 < nt P Q ℓ r)
    {Wd' : ℂ} (hW : HasDerivAt (fun ξ' => Wsh u (u + v) ξ') Wd' (4 * π ^ 2 * r * nt P Q ℓ r)) :
    HasDerivAt (Hl P Q ℓ u v)
      (cexp (Ef u v r (nt P Q ℓ r)) *
          ((((-(1 / 2)) * (r⁻¹ + (nt P Q ℓ r)⁻¹ * (P / Q)) : ℝ) : ℂ) +
            ((v * ((nt P Q ℓ r)⁻¹ * (P / Q)) +
              u * ((nt P Q ℓ r)⁻¹ * (P / Q) - r⁻¹) : ℝ) : ℂ) * I) *
          Wsh u (u + v) (4 * π ^ 2 * r * nt P Q ℓ r) +
        cexp (Ef u v r (nt P Q ℓ r)) *
          (((4 * π ^ 2 * nt P Q ℓ r + 4 * π ^ 2 * r * (P / Q) : ℝ) : ℂ) * Wd')) r := by
  have dnt : HasDerivAt (nt P Q ℓ) ((P : ℝ) / Q) r := by
    unfold nt
    have := (((hasDerivAt_id r).const_mul (P : ℝ)).sub_const (ℓ : ℝ)).div_const (Q : ℝ)
    simpa using this
  have dL1 := Real.hasDerivAt_log hr.ne'
  have dL2 := (Real.hasDerivAt_log hn.ne').comp r dnt
  have dER := (dL1.add dL2).const_mul (-(1 / 2) : ℝ)
  have dEI := (dL2.const_mul v).add ((dL2.sub dL1).const_mul u)
  have dE := dER.ofReal_comp.add (dEI.ofReal_comp.mul_const I)
  have dξ := ((hasDerivAt_id r).const_mul (4 * π ^ 2)).mul dnt
  have dW := hW.scomp r dξ
  have dH := dE.cexp.mul dW
  convert dH using 1
  simp only [Ef, id, mul_one, Function.comp_def, real_smul, Pi.add_apply, Pi.mul_apply,
    Pi.sub_apply]

/-- **The `H_ℓ` bounds.** -/
theorem Hl_deriv : ∃ K : ℝ, 0 ≤ K ∧ ∀ (P Q : ℕ) (ℓ : ℤ) (u v r : ℝ), 1 ≤ P → 1 ≤ Q → |v| ≤ 1 →
    0 < r → 2 * |(ℓ : ℝ)| ≤ r →
      ‖Hl P Q ℓ u v r‖ ≤ K * Q / r ∧ ∃ D : ℂ, HasDerivAt (Hl P Q ℓ u v) D r ∧
        ‖D‖ ≤ K * Q * (1 / r ^ 2 + |u| * |(ℓ : ℝ)| / r ^ 3) := by
  obtain ⟨CW, Cξ, hCW0, hCξ0, hCW, hCξ⟩ := W_consts
  refine ⟨12 * CW + 6 * Cξ, by positivity, fun P Q ℓ u v r hP hQ hv hr hℓ => ?_⟩
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  obtain ⟨hy, hρ, hρ1⟩ := rho_bounds hP' hr hℓ
  have hy0 : 0 < (P : ℝ) * r - ℓ := by nlinarith
  have hnt : nt P Q ℓ r = ((P : ℝ) * r - ℓ) / Q := rfl
  have hn0 : 0 < nt P Q ℓ r := by rw [hnt]; positivity
  have hρe : (nt P Q ℓ r)⁻¹ * ((P : ℝ) / Q) = (P : ℝ) / ((P : ℝ) * r - ℓ) := by
    rw [hnt]; field_simp
  -- `(r/(2Q))² ≤ r ñ`
  have hrs : (r / (2 * Q)) ^ 2 ≤ r * nt P Q ℓ r := by
    rw [hnt, div_pow]
    have h1 : r / (2 * Q) ≤ ((P : ℝ) * r - ℓ) / Q := by
      have h3 : r ≤ 2 * ((P : ℝ) * r - ℓ) := by
        have := le_mul_of_one_le_left hr.le hP'; linarith
      rw [div_le_div_iff₀ (by positivity) hQ0]
      nlinarith [mul_le_mul_of_nonneg_right h3 hQ0.le]
    have h2 : r ^ 2 / (2 * Q) ^ 2 ≤ r * (r / (2 * Q)) := by
      rw [mul_div_assoc', ← pow_two]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by nlinarith)
    calc r ^ 2 / (2 * Q) ^ 2 ≤ r * (r / (2 * Q)) := h2
      _ ≤ r * (((P : ℝ) * r - ℓ) / Q) := mul_le_mul_of_nonneg_left h1 hr.le
  have hE := norm_cexp_Ef_le (u := u) (v := v) hr hn0 hQ' hrs
  have hξ0 : 0 < 4 * π ^ 2 * r * nt P Q ℓ r := by positivity
  obtain ⟨hWd, hWdb⟩ := hCξ u v (4 * π ^ 2 * r * nt P Q ℓ r) hξ0
  have hWb := hCW u (u + v) (4 * π ^ 2 * r * nt P Q ℓ r) hξ0
  have hEn : 0 ≤ ‖cexp (Ef u v r (nt P Q ℓ r))‖ := norm_nonneg _
  constructor
  · -- `‖H‖ ≤ (2Q/r) CW`
    unfold Hl Gf
    rw [norm_mul]
    calc ‖cexp (Ef u v r (nt P Q ℓ r))‖ * ‖Wsh u (u + v) (4 * π ^ 2 * r * nt P Q ℓ r)‖
        ≤ 2 * Q / r * CW := mul_le_mul hE hWb (norm_nonneg _) (by positivity)
      _ ≤ (12 * CW + 6 * Cξ) * Q / r := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]; nlinarith
  refine ⟨_, hasDerivAt_Hl P Q ℓ u v r hr hn0 hWd, ?_⟩
  rw [hρe]
  set ρ := (P : ℝ) / ((P : ℝ) * r - ℓ)
  have hρ0 : 0 ≤ ρ := by positivity
  -- the exponent derivative
  have hE' : ‖((((-(1 / 2)) * (r⁻¹ + ρ)) : ℝ) : ℂ) + ((v * ρ + u * (ρ - r⁻¹) : ℝ) : ℂ) * I‖ ≤
      4 / r + 2 * |u| * |(ℓ : ℝ)| / r ^ 2 := by
    refine (norm_ofReal_add_mul_I_le _ _).trans ?_
    have hr1 : 0 < r⁻¹ := inv_pos.2 hr
    have hρ' : ρ ≤ 2 * r⁻¹ := by rw [← div_eq_mul_inv]; exact hρ
    have a1 : |(-(1 / 2)) * (r⁻¹ + ρ)| ≤ 3 / 2 * r⁻¹ := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < r⁻¹ + ρ), abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    have a2 : |v * ρ + u * (ρ - r⁻¹)| ≤ 2 * r⁻¹ + 2 * |u| * |(ℓ : ℝ)| / r ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
      have b1 : |v| * ρ ≤ 2 * r⁻¹ := by
        calc |v| * ρ ≤ 1 * (2 * r⁻¹) := mul_le_mul hv hρ' hρ0 zero_le_one
          _ = 2 * r⁻¹ := one_mul _
      have b2 : |u| * |ρ - r⁻¹| ≤ 2 * |u| * |(ℓ : ℝ)| / r ^ 2 := by
        calc |u| * |ρ - r⁻¹| ≤ |u| * (2 * |(ℓ : ℝ)| / r ^ 2) :=
              mul_le_mul_of_nonneg_left hρ1 (abs_nonneg _)
          _ = _ := by ring
      linarith
    calc _ ≤ 3 / 2 * r⁻¹ + (2 * r⁻¹ + 2 * |u| * |(ℓ : ℝ)| / r ^ 2) := add_le_add a1 a2
      _ ≤ _ := by rw [div_eq_mul_inv 4 r]; linarith
  -- the `ξ`-derivative part
  have hξ' : ‖((4 * π ^ 2 * nt P Q ℓ r + 4 * π ^ 2 * r * (P / Q) : ℝ) : ℂ) *
      Wd u v (4 * π ^ 2 * r * nt P Q ℓ r)‖ ≤ 3 / r * Cξ := by
    have e : ((4 * π ^ 2 * nt P Q ℓ r + 4 * π ^ 2 * r * (P / Q) : ℝ) : ℂ) *
        Wd u v (4 * π ^ 2 * r * nt P Q ℓ r) = ((r⁻¹ + ρ : ℝ) : ℂ) *
        (((4 * π ^ 2 * r * nt P Q ℓ r : ℝ) : ℂ) * Wd u v (4 * π ^ 2 * r * nt P Q ℓ r)) := by
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      rw [← hρe]
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r⁻¹ + ρ)]
    have : r⁻¹ + ρ ≤ 3 / r := by
      have hρ' : ρ ≤ 2 * r⁻¹ := by rw [← div_eq_mul_inv]; exact hρ
      rw [div_eq_mul_inv]; linarith
    exact mul_le_mul this hWdb (norm_nonneg _) (by positivity)
  -- assemble
  have hu : 0 ≤ |u| * |(ℓ : ℝ)| := by positivity
  calc _ ≤ ‖cexp (Ef u v r (nt P Q ℓ r))‖ * ‖((((-(1 / 2)) * (r⁻¹ + ρ)) : ℝ) : ℂ) +
          ((v * ρ + u * (ρ - r⁻¹) : ℝ) : ℂ) * I‖ * ‖Wsh u (u + v) (4 * π ^ 2 * r * nt P Q ℓ r)‖ +
        ‖cexp (Ef u v r (nt P Q ℓ r))‖ * ‖((4 * π ^ 2 * nt P Q ℓ r + 4 * π ^ 2 * r * (P / Q) : ℝ) : ℂ) *
          Wd u v (4 * π ^ 2 * r * nt P Q ℓ r)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 2 * Q / r * (4 / r + 2 * |u| * |(ℓ : ℝ)| / r ^ 2) * CW + 2 * Q / r * (3 / r * Cξ) := by
        gcongr
    _ = Q * ((8 * CW + 6 * Cξ) * (1 / r ^ 2) + 4 * CW * (|u| * |(ℓ : ℝ)| / r ^ 3)) := by
        field_simp; ring
    _ ≤ Q * ((12 * CW + 6 * Cξ) * (1 / r ^ 2) + (12 * CW + 6 * Cξ) * (|u| * |(ℓ : ℝ)| / r ^ 3)) := by
        gcongr
        · linarith
        · linarith
    _ = _ := by ring

end RamanujanTau.SelbergKey7
