/-
# `Δ(i e^{iα})` vanishes to infinite order as `α → π/2⁻`

Put `α = π/2 − β`.  Then `z = i e^{iα} = −cos β + i sin β` tends to the cusp `−1`.  With
`v = z + 1` and `Δ(z) = Δ(v) = v^{−12} Δ(−1/v)` (periodicity and `Δ(−1/v) = v¹²Δ(v)`):
`Im(−1/v) = sin β/(2 − 2cos β) ≥ 1/(2 sin β)` and `|v|¹² ≥ sin¹²β`, so by the cusp decay
`|Δ(p)| ≤ A e^{−2π Im p}`,

    |Δ(z)| ≤ A e^{−π / sin β} / sin¹²β ≤ A (N+12)! β^N.
-/
import RamanujanTau.HardyZeros.Fourier

set_option autoImplicit false

namespace RamanujanTau.HardyZeros

open Complex ModularForm Filter Set
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL
open scoped MatrixGroups Real

lemma Dc_add_one (z : ℂ) : Dc (z + 1) = Dc z :=
  (SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL) z

lemma Dc_of_im_pos {w : ℂ} (hw : 0 < w.im) : Dc w = Δf ⟨w, hw⟩ := by
  simp only [Dc, Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hw]

lemma im_neg_one_div_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-1 / w).im := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have : (-1 / w).im = w.im / Complex.normSq w := by
    rw [neg_div, Complex.neg_im, Complex.div_im]; simp
  rw [this]
  exact div_pos hw (Complex.normSq_pos.mpr hw0)

/-- `Δ(−1/w) = w¹² Δ(w)` on `ℍ`. -/
lemma Dc_S {w : ℂ} (hw : 0 < w.im) : Dc (-1 / w) = w ^ 12 * Dc w := by
  set p : ℍ := ⟨w, hw⟩ with hp
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have him := im_neg_one_div_pos hw
  have h2 : Dc (-1 / w) = Δf (ModularGroup.S • p) := by
    rw [Dc_of_im_pos him]
    congr 1
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    show -1 / w = (-w)⁻¹
    rw [inv_neg, neg_div, one_div]
  have h := congrFun discriminant_S_invariant p
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  rw [h2, Dc_of_im_pos hw]
  show discriminant (ModularGroup.S • p) = w ^ 12 * discriminant p
  rw [← h]
  have hpc : (p : ℂ) = w := rfl
  rw [hpc, zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast]
  field_simp

/-- Cusp decay `‖Δ(p)‖ ≤ A e^{−2π Im p}` for `Im p ≥ Y`. -/
lemma Delta_cusp_bound : ∃ A Y : ℝ, 0 ≤ A ∧ 0 < Y ∧
    ∀ p : ℍ, Y ≤ p.im → ‖Δf p‖ ≤ A * Real.exp (-(2 * π) * p.im) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hC
  refine ⟨max C 0, max Y 1, le_max_right _ _, by positivity, fun p hp => ?_⟩
  have hb := hY p ((le_max_left _ _).trans hp)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_one] at hb
  have e : -2 * π * p.im = -(2 * π) * p.im := by ring
  rw [e] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- `x^{12} e^{−πx} ≤ (N+12)! x^{−N}`, written with `s = 1/x`. -/
lemma exp_neg_div_le {s : ℝ} (hs : 0 < s) (N : ℕ) :
    Real.exp (-(π / s)) / s ^ 12 ≤ ((N + 12).factorial : ℝ) * s ^ N := by
  set x : ℝ := 1 / s with hx
  have hxpos : 0 < x := by positivity
  have h1 : x ^ (N + 12) / ((N + 12).factorial : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hxpos.le _
  have h2 : Real.exp x ≤ Real.exp (π * x) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_gt_three]
  have hf : (0 : ℝ) < (N + 12).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : x ^ (N + 12) ≤ ((N + 12).factorial : ℝ) * Real.exp (π * x) := by
    rw [div_le_iff₀ hf] at h1; nlinarith
  have hπx : π / s = π * x := by rw [hx]; ring
  rw [hπx, div_le_iff₀ (pow_pos hs 12), Real.exp_neg]
  have hxs : x * s = 1 := by rw [hx]; field_simp
  have hE : 0 < Real.exp (π * x) := Real.exp_pos _
  -- multiply h3 by s^(N+12) e^{-πx}
  have hsN : (x * s) ^ (N + 12) = 1 := by rw [hxs, one_pow]
  rw [mul_pow] at hsN
  have key : 1 ≤ ((N + 12).factorial : ℝ) * Real.exp (π * x) * s ^ (N + 12) := by
    calc (1 : ℝ) = x ^ (N + 12) * s ^ (N + 12) := hsN.symm
      _ ≤ ((N + 12).factorial : ℝ) * Real.exp (π * x) * s ^ (N + 12) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
  rw [inv_eq_one_div, div_le_iff₀ hE]
  calc (1 : ℝ) ≤ ((N + 12).factorial : ℝ) * Real.exp (π * x) * s ^ (N + 12) := key
    _ = (N + 12).factorial * s ^ N * s ^ 12 * Real.exp (π * x) := by rw [pow_add]; ring

lemma exp_rot_mul_I (β : ℝ) :
    cexp (((π / 2 - β : ℝ) : ℂ) * I) * I = -(Real.cos β : ℂ) + (Real.sin β : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring_nf; rw [I_sq]; ring

/-- **Boundary decay**: `‖Δ(i e^{i(π/2−β)})‖ ≤ C β^N` for small `β > 0`. -/
theorem Dc_rot_decay (N : ℕ) : ∃ C β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 ∧ ∀ β, 0 < β → β ≤ β₀ →
    ‖Dc (cexp (((π / 2 - β : ℝ) : ℂ) * I) * I)‖ ≤ C * β ^ N := by
  obtain ⟨A, Y, hA, hY, hcusp⟩ := Delta_cusp_bound
  refine ⟨A * (N + 12).factorial, min 1 (1 / (2 * Y)), lt_min one_pos (by positivity),
    min_le_left _ _, fun β hβ hββ₀ => ?_⟩
  have hβ1 : β ≤ 1 := hββ₀.trans (min_le_left _ _)
  have hβY : β ≤ 1 / (2 * Y) := hββ₀.trans (min_le_right _ _)
  set s := Real.sin β with hs
  set c := Real.cos β with hc
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_gt_three])
  have hsβ : s ≤ β := Real.sin_le hβ.le
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have hc1 : c ≤ 1 := Real.cos_le_one β
  have hcpos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  rw [exp_rot_mul_I, ← hs, ← hc]
  set z : ℂ := -(c : ℂ) + (s : ℂ) * I with hz
  set v : ℂ := z + 1 with hv
  have hvre : v.re = 1 - c := by simp [hv, hz]; ring
  have hvim : v.im = s := by simp [hv, hz]
  have hvpos : 0 < v.im := by rw [hvim]; exact hspos
  have hnormSq : Complex.normSq v = 2 - 2 * c := by
    rw [Complex.normSq_apply, hvre, hvim]; nlinarith
  have h1c : 1 - c ≤ s ^ 2 := by nlinarith
  have hnorm2 : s ^ 2 ≤ Complex.normSq v := by rw [hnormSq]; nlinarith
  -- Im(−1/v)
  have him : (-1 / v).im = s / (2 - 2 * c) := by
    rw [neg_div, Complex.neg_im, Complex.div_im, hnormSq, hvim]; simp
  have himpos := im_neg_one_div_pos hvpos
  have himge : 1 / (2 * s) ≤ (-1 / v).im := by
    rw [him, div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  have hYim : Y ≤ (-1 / v).im := by
    refine le_trans ?_ himge
    rw [le_div_iff₀ (by positivity)]
    have : s * (2 * Y) ≤ β * (2 * Y) := mul_le_mul_of_nonneg_right hsβ (by positivity)
    have h2 : β * (2 * Y) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hβY
    nlinarith
  -- the transformation
  have hDz : Dc z = Dc v := (Dc_add_one z).symm
  have hS := Dc_S hvpos
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvpos; simp at hvpos
  have hnv : ‖v‖ ^ 12 = Complex.normSq v ^ 6 := by
    rw [Complex.normSq_eq_norm_sq, ← pow_mul]
  have hnvpos : 0 < ‖v‖ ^ 12 := pow_pos (norm_pos_iff.mpr hv0) _
  have hDv : ‖Dc v‖ = ‖Dc (-1 / v)‖ / ‖v‖ ^ 12 := by
    rw [hS, norm_mul, norm_pow]; field_simp
  have hbound : ‖Dc (-1 / v)‖ ≤ A * Real.exp (-(π / s)) := by
    rw [Dc_of_im_pos himpos]
    refine (hcusp ⟨-1 / v, himpos⟩ hYim).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA)
    show -(2 * π) * (-1 / v).im ≤ -(π / s)
    have : π / s = 2 * π * (1 / (2 * s)) := by field_simp
    rw [this]
    nlinarith [Real.pi_pos]
  have hs12 : s ^ 12 ≤ ‖v‖ ^ 12 := by
    rw [hnv, show s ^ 12 = (s ^ 2) ^ 6 by ring]
    exact pow_le_pow_left₀ (by positivity) hnorm2 6
  rw [hDz, hDv]
  calc ‖Dc (-1 / v)‖ / ‖v‖ ^ 12 ≤ A * Real.exp (-(π / s)) / s ^ 12 :=
        div_le_div₀ (by positivity) hbound (by positivity) hs12
    _ = A * (Real.exp (-(π / s)) / s ^ 12) := by ring
    _ ≤ A * (((N + 12).factorial : ℝ) * s ^ N) :=
        mul_le_mul_of_nonneg_left (exp_neg_div_le hspos N) hA
    _ ≤ A * (((N + 12).factorial : ℝ) * β ^ N) := by
        gcongr
    _ = A * (N + 12).factorial * β ^ N := by ring

end RamanujanTau.HardyZeros
