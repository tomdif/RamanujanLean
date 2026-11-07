/-
# `f(i e^{iα})` vanishes to infinite order as `α → π/2⁻`, for a level-one cusp form `f`

Put `α = π/2 − β`, `z = i e^{iα} = −cos β + i sin β → −1`, `v = z + 1`.  Periodicity and
`f(−1/v) = v^k f(v)` give `f(z) = v^{−k} f(−1/v)`; `Im(−1/v) ≥ 1/(2 sin β)`, `|v| ≥ sin β`, and
the cusp decay `|f(p)| ≤ A e^{−2π Im p}` (Mathlib `CuspFormClass.exp_decay_atImInfty`) give

    |f(z)| ≤ A e^{−π / sin β} / sin^k β ≤ A (N+k)! β^N.
-/
import RamanujanTau.HardyZerosGeneral.Fourier

set_option autoImplicit false

namespace RamanujanTau.HardyZerosGeneral

open Complex ModularForm Filter Set
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real

variable {k : ℕ}

lemma Fc_add_one (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℂ) : Fc f (z + 1) = Fc f z :=
  (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL) z

lemma Fc_of_im_pos (f : CuspForm 𝒮ℒ (k : ℤ)) {w : ℂ} (hw : 0 < w.im) :
    Fc f w = f ⟨w, hw⟩ := by
  simp only [Fc, Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hw]

lemma im_neg_one_div_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-1 / w).im := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have : (-1 / w).im = w.im / Complex.normSq w := by
    rw [neg_div, Complex.neg_im, Complex.div_im]; simp
  rw [this]
  exact div_pos hw (Complex.normSq_pos.mpr hw0)

/-- `f(−1/w) = w^k f(w)` on `ℍ`. -/
lemma Fc_S (f : CuspForm 𝒮ℒ (k : ℤ)) {w : ℂ} (hw : 0 < w.im) :
    Fc f (-1 / w) = w ^ k * Fc f w := by
  set p : ℍ := ⟨w, hw⟩ with hp
  have him := im_neg_one_div_pos hw
  have hSp : ModularGroup.S • p = (⟨-1 / w, him⟩ : ℍ) := by
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    show (-w)⁻¹ = -1 / w
    rw [inv_neg, neg_div, one_div]
  have h := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩) p
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • p = ModularGroup.S • p := rfl
  rw [hs, hSp] at h
  rw [Fc_of_im_pos f him, Fc_of_im_pos f hw, h]
  congr 1
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) p = w := by
    simp [denom, ModularGroup.S, hp]
  rw [hd, zpow_natCast]

/-- Cusp decay `‖f(p)‖ ≤ A e^{−2π Im p}` for `Im p ≥ Y`. -/
lemma cusp_bound (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ A Y : ℝ, 0 ≤ A ∧ 0 < Y ∧
    ∀ p : ℍ, Y ≤ p.im → ‖f p‖ ≤ A * Real.exp (-(2 * π) * p.im) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := (k : ℤ)) f one_pos
    one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hC
  refine ⟨max C 0, max Y 1, le_max_right _ _, by positivity, fun p hp => ?_⟩
  have hb := hY p ((le_max_left _ _).trans hp)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_one] at hb
  have e : -2 * π * p.im = -(2 * π) * p.im := by ring
  rw [e] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- `x^k e^{−πx} ≤ (N+k)! x^{−N}`, written with `s = 1/x`. -/
lemma exp_neg_div_le {s : ℝ} (hs : 0 < s) (k N : ℕ) :
    Real.exp (-(π / s)) / s ^ k ≤ ((N + k).factorial : ℝ) * s ^ N := by
  set x : ℝ := 1 / s with hx
  have hxpos : 0 < x := by positivity
  have h1 : x ^ (N + k) / ((N + k).factorial : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hxpos.le _
  have h2 : Real.exp x ≤ Real.exp (π * x) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_gt_three]
  have hf : (0 : ℝ) < (N + k).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : x ^ (N + k) ≤ ((N + k).factorial : ℝ) * Real.exp (π * x) := by
    rw [div_le_iff₀ hf] at h1; nlinarith
  have hπx : π / s = π * x := by rw [hx]; ring
  rw [hπx, div_le_iff₀ (pow_pos hs k), Real.exp_neg]
  have hxs : x * s = 1 := by rw [hx]; field_simp
  have hE : 0 < Real.exp (π * x) := Real.exp_pos _
  have hsN : (x * s) ^ (N + k) = 1 := by rw [hxs, one_pow]
  rw [mul_pow] at hsN
  have key : 1 ≤ ((N + k).factorial : ℝ) * Real.exp (π * x) * s ^ (N + k) := by
    calc (1 : ℝ) = x ^ (N + k) * s ^ (N + k) := hsN.symm
      _ ≤ ((N + k).factorial : ℝ) * Real.exp (π * x) * s ^ (N + k) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
  rw [inv_eq_one_div, div_le_iff₀ hE]
  calc (1 : ℝ) ≤ ((N + k).factorial : ℝ) * Real.exp (π * x) * s ^ (N + k) := key
    _ = (N + k).factorial * s ^ N * s ^ k * Real.exp (π * x) := by rw [pow_add]; ring

lemma exp_rot_mul_I (β : ℝ) :
    cexp (((π / 2 - β : ℝ) : ℂ) * I) * I = -(Real.cos β : ℂ) + (Real.sin β : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring_nf; rw [I_sq]; ring

/-- **Boundary decay at the cusp `−1`**: `‖f(i e^{i(π/2−β)})‖ ≤ C β^N` for small `β > 0`. -/
theorem Fc_rot_decay (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) :
    ∃ C β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 ∧ ∀ β, 0 < β → β ≤ β₀ →
      ‖Fc f (cexp (((π / 2 - β : ℝ) : ℂ) * I) * I)‖ ≤ C * β ^ N := by
  obtain ⟨A, Y, hA, hY, hcusp⟩ := cusp_bound f
  refine ⟨A * (N + k).factorial, min 1 (1 / (2 * Y)), lt_min one_pos (by positivity),
    min_le_left _ _, fun β hβ hββ₀ => ?_⟩
  have hβ1 : β ≤ 1 := hββ₀.trans (min_le_left _ _)
  have hβY : β ≤ 1 / (2 * Y) := hββ₀.trans (min_le_right _ _)
  set s := Real.sin β with hs
  set c := Real.cos β with hc
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_gt_three])
  have hsβ : s ≤ β := Real.sin_le hβ.le
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have hc1 : c ≤ 1 := Real.cos_le_one β
  have hcpos : 0 < c := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
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
  have hDz : Fc f z = Fc f v := (Fc_add_one f z).symm
  have hS := Fc_S f hvpos
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvpos; simp at hvpos
  have hnvpos : 0 < ‖v‖ ^ k := pow_pos (norm_pos_iff.mpr hv0) _
  have hDv : ‖Fc f v‖ = ‖Fc f (-1 / v)‖ / ‖v‖ ^ k := by
    rw [hS, norm_mul, norm_pow]; field_simp
  have hbound : ‖Fc f (-1 / v)‖ ≤ A * Real.exp (-(π / s)) := by
    rw [Fc_of_im_pos f himpos]
    refine (hcusp ⟨-1 / v, himpos⟩ hYim).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA)
    show -(2 * π) * (-1 / v).im ≤ -(π / s)
    have : π / s = 2 * π * (1 / (2 * s)) := by field_simp
    rw [this]
    nlinarith [Real.pi_pos]
  have hsv : s ≤ ‖v‖ := by
    have : s ^ 2 ≤ ‖v‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hnorm2
    nlinarith [norm_nonneg v]
  have hsk : s ^ k ≤ ‖v‖ ^ k := pow_le_pow_left₀ hspos.le hsv k
  rw [hDz, hDv]
  calc ‖Fc f (-1 / v)‖ / ‖v‖ ^ k ≤ A * Real.exp (-(π / s)) / s ^ k :=
        div_le_div₀ (by positivity) hbound (by positivity) hsk
    _ = A * (Real.exp (-(π / s)) / s ^ k) := by ring
    _ ≤ A * (((N + k).factorial : ℝ) * s ^ N) :=
        mul_le_mul_of_nonneg_left (exp_neg_div_le hspos k N) hA
    _ ≤ A * (((N + k).factorial : ℝ) * β ^ N) := by
        gcongr
    _ = A * (N + k).factorial * β ^ N := by ring

end RamanujanTau.HardyZerosGeneral
