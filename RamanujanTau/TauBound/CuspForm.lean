/-
# `P₁` is a cusp form: discharging `PoincareIsCuspForm`

`poincareCuspForm : CuspForm 𝒮ℒ 12` has underlying function `pSeries / 2`, where
`pSeries z = ∑_{(c,d) coprime} (cz+d)^{-12} e(γ_{(c,d)} z)` (`CuspFormSlash.lean`).

* slash invariance: `pSeries_smul` (re-indexing `v ↦ vγ`);
* holomorphy: `differentiableOn_tsum_of_summable_norm` on open vertical strips, with the weight-12
  Eisenstein majorant `summand_bound_of_mem_verticalStrip`;
* vanishing at `∞`: `|e(γz)| = exp(-2π y/|cz+d|²) ≤ |cz+d|²/(2πy)`, so each term is
  `≤ |cz+d|^{-10}/y`; after a `T`-translate into `|Re z| ≤ 1`, the weight-10 Eisenstein majorant gives
  `|pSeries z| ≤ C/y`.

`pSeries = 2 · poincare` (`CuspFormSum.lean`) then gives `poincareIsCuspForm : PoincareIsCuspForm`.
-/
import RamanujanTau.TauBound.CuspFormSum
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.Identities

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex UpperHalfPlane ModularGroup EisensteinSeries Matrix ModularForm Filter
open scoped MatrixGroups Real Manifold

/-! ### Slash invariance -/

/-- The cusp form candidate: `pSeries / 2` (equal to `poincare` on `ℍ`). -/
noncomputable def pHalf (z : ℍ) : ℂ := pSeries z / 2

lemma pHalf_smul (γ : SL(2, ℤ)) (z : ℍ) : pHalf (γ • z) = (denom γ z) ^ (12 : ℤ) * pHalf z := by
  unfold pHalf; rw [pSeries_smul]; ring

lemma pHalf_slash (γ : SL(2, ℤ)) : pHalf ∣[(12 : ℤ)] γ = pHalf := by
  funext z
  rw [SL_slash_apply, pHalf_smul, mul_comm, ← mul_assoc, ← zpow_add₀ (denom_ne_zero _ z)]
  simp

/-! ### Holomorphy -/

noncomputable def eeSmul (g : SL(2, ℤ)) (w : ℍ) : ℂ := ee ((g • w : ℍ) : ℂ)

lemma mdiff_ee_smul (g : SL(2, ℤ)) : MDiff (eeSmul g) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => (g : GL (Fin 2) ℝ) • w) :=
    mdifferentiable_smul (by simp)
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => (((g : GL (Fin 2) ℝ) • w : ℍ) : ℂ)) :=
    mdifferentiable_coe.comp h1
  have h3 : Differentiable ℂ ee := by
    unfold ee; fun_prop
  exact h3.comp_mdifferentiable h2

lemma mdiff_pTerm (v : Fin 2 → ℤ) : MDiff (pTerm v) := by
  have h1 : MDiff (eisSummand 12 v) :=
    UpperHalfPlane.mdifferentiable_iff.mpr (eisSummand_extension_differentiableOn 12 v)
  exact h1.mul (mdiff_ee_smul (gOf v))

lemma norm_pTerm_le_strip (v : Fin 2 → ℤ) {A B : ℝ} (hB : 0 < B) {z : ℍ}
    (hz : z ∈ verticalStrip A B) :
    ‖pTerm v z‖ ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-12 : ℝ) * ‖v‖ ^ (-12 : ℝ) := by
  refine (norm_pTerm_le v z).trans ?_
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound_of_mem_verticalStrip (k := 12) (by norm_num) v hB hz

lemma mdiff_pSeries : MDiff pSeries := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro w0 hw0
  have hw0' : 0 < w0.im := hw0
  set A : ℝ := |w0.re| + 1
  set B : ℝ := w0.im / 2
  have hB : 0 < B := by simp only [B]; linarith
  set U : Set ℂ := {w | |w.re| < A} ∩ {w | B < w.im}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hτU : w0 ∈ U := ⟨by simp only [Set.mem_setOf_eq, A]; linarith,
    by simp only [Set.mem_setOf_eq, B]; linarith⟩
  have hUH : U ⊆ {w : ℂ | 0 < w.im} := fun w hw => lt_trans hB hw.2
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' v : gammaSet 1 1 0, (pTerm v.1 ∘ ofComplex) w) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun v : gammaSet 1 1 0 => r ⟨⟨A, B⟩, hB⟩ ^ (-12 : ℝ) * ‖v.1‖ ^ (-12 : ℝ)) ?_ ?_ hU ?_
    · exact ((summable_one_div_norm_rpow (k := 12) (by norm_num)).subtype _).mul_left _
    · intro v
      exact ((UpperHalfPlane.mdifferentiable_iff.mp (mdiff_pTerm v.1)).mono hUH)
    · intro v w hw
      have hw0 : 0 < w.im := hUH hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw0]
      refine norm_pTerm_le_strip v.1 hB ?_
      exact ⟨by simpa using hw.1.le, by simpa using hw.2.le⟩
  have : DifferentiableAt ℂ (pSeries ∘ ofComplex) w0 := by
    have := hd.differentiableAt (hU.mem_nhds hτU)
    convert this using 1
  exact this.differentiableWithinAt

/-! ### Vanishing at `∞` -/

lemma norm_pTerm_le_decay (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) (z : ℍ) :
    ‖pTerm v z‖ ≤ ‖(v 0 : ℂ) * z + v 1‖ ^ (-10 : ℝ) / z.im := by
  obtain ⟨r0, r1⟩ := gOf_row v hv
  set s : ℝ := ‖(v 0 : ℂ) * z + v 1‖
  have hden : denom (gOf v) z = (v 0 : ℂ) * z + v 1 := by
    rw [denom_apply]; simp [r0, r1]
  have hs : 0 < s := by
    have := denom_ne_zero (gOf v) z
    rw [hden] at this
    exact norm_pos_iff.mpr this
  have hy := z.im_pos
  have him : ((gOf v • z : ℍ) : ℂ).im = z.im / s ^ 2 := by
    rw [UpperHalfPlane.coe_im, ModularGroup.im_smul_eq_div_normSq, hden, Complex.normSq_eq_norm_sq]
  unfold pTerm
  rw [norm_mul, norm_ee, him]
  simp only [eisSummand, norm_zpow]
  set t : ℝ := 2 * π * (z.im / s ^ 2)
  have ht : 0 < t := by positivity
  have hexp : Real.exp (-2 * π * (z.im / s ^ 2)) ≤ t⁻¹ := by
    rw [show -2 * π * (z.im / s ^ 2) = -t by ring, Real.exp_neg]
    exact inv_anti₀ ht (by linarith [Real.add_one_le_exp t])
  have e10 : s ^ (-10 : ℝ) = (s ^ 10)⁻¹ := by
    rw [Real.rpow_neg hs.le]; norm_cast
  rw [e10, show (s ^ (-12 : ℤ)) = (s ^ 12)⁻¹ by rw [_root_.zpow_neg]; norm_cast]
  calc (s ^ 12)⁻¹ * Real.exp (-2 * π * (z.im / s ^ 2)) ≤ (s ^ 12)⁻¹ * t⁻¹ := by gcongr
    _ = (s ^ 10)⁻¹ / z.im * (2 * π)⁻¹ := by
        simp only [t]; field_simp
    _ ≤ (s ^ 10)⁻¹ / z.im * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
    _ = _ := mul_one _

/-- `pSeries (T^n z) = pSeries z`. -/
lemma pSeries_T_zpow (n : ℤ) (z : ℍ) : pSeries (T ^ n • z) = pSeries z := by
  rw [pSeries_smul, denom_apply]
  simp [coe_T_zpow]

/-- Weight-10 Eisenstein constant on the strip `|Re z| ≤ 1`, `Im z ≥ 1`. -/
noncomputable def decayConst : ℝ :=
  r ⟨⟨1, 1⟩, one_pos⟩ ^ (-10 : ℝ) * ∑' v : gammaSet 1 1 0, ‖v.1‖ ^ (-10 : ℝ)

lemma norm_pSeries_le (z : ℍ) (hz : 1 ≤ z.im) : ‖pSeries z‖ ≤ decayConst / z.im := by
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z (N := 1) one_pos
  set z' := T ^ ((1 : ℕ) * n) • z
  have hz' : z' ∈ verticalStrip 1 1 := by
    have := verticalStrip_anti_right (1 : ℕ) hz hn
    simpa using this
  have him : z'.im = z.im := by
    simp only [z']; rw [modular_T_zpow_smul]; simp
  rw [← pSeries_T_zpow ((1 : ℕ) * n) z]
  have hS : Summable fun v : gammaSet 1 1 0 => ‖v.1‖ ^ (-10 : ℝ) :=
    (summable_one_div_norm_rpow (k := 10) (by norm_num)).subtype _
  have hy : 0 < z.im := z.im_pos
  have hb : ∀ v : gammaSet 1 1 0, ‖pTerm v.1 z'‖ ≤
      (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-10 : ℝ) / z.im) * ‖v.1‖ ^ (-10 : ℝ) := by
    intro v
    refine (norm_pTerm_le_decay v.1 ((mem_gammaSet_one _).mp v.2) z').trans ?_
    rw [him, div_mul_eq_mul_div]
    gcongr
    exact summand_bound_of_mem_verticalStrip (k := 10) (by norm_num) v.1 one_pos hz'
  have hsum : Summable fun v : gammaSet 1 1 0 =>
      (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-10 : ℝ) / z.im) * ‖v.1‖ ^ (-10 : ℝ) := hS.mul_left _
  calc ‖pSeries z'‖ ≤ ∑' v : gammaSet 1 1 0, ‖pTerm v.1 z'‖ :=
        norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hb)
    _ ≤ ∑' v : gammaSet 1 1 0, (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-10 : ℝ) / z.im) * ‖v.1‖ ^ (-10 : ℝ) :=
        (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hb).tsum_le_tsum hb hsum
    _ = decayConst / z.im := by
        rw [tsum_mul_left, decayConst]; ring

lemma decayConst_nonneg : 0 ≤ decayConst :=
  mul_nonneg (Real.rpow_nonneg (r_pos _).le _) (tsum_nonneg fun _ => by positivity)

lemma isZeroAtImInfty_pHalf : IsZeroAtImInfty pHalf := by
  rw [isZeroAtImInfty_iff]
  intro ε hε
  refine ⟨max 1 (decayConst / ε), fun z hz => ?_⟩
  have h1 : 1 ≤ z.im := le_trans (le_max_left _ _) hz
  have h2 : decayConst / ε ≤ z.im := le_trans (le_max_right _ _) hz
  have hy : 0 < z.im := by linarith
  unfold pHalf
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have h3 := norm_pSeries_le z h1
  have h4 : decayConst / z.im ≤ ε := by
    rw [div_le_iff₀ hy]; rw [div_le_iff₀ hε] at h2; linarith
  linarith [norm_nonneg (pSeries z)]

/-! ### The cusp form -/

/-- **The Poincaré series `P₁` as a weight-12 cusp form for `SL₂(ℤ)`.** -/
noncomputable def poincareCuspForm : CuspForm 𝒮ℒ 12 where
  toFun := pHalf
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact pHalf_slash A
  holo' := by
    show MDiff pHalf
    have : pHalf = fun z => (1 / 2 : ℂ) * pSeries z := by
      funext z; unfold pHalf; ring
    rw [this]
    exact mdifferentiable_const.mul mdiff_pSeries
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [pHalf_slash γ]
    exact isZeroAtImInfty_pHalf

lemma poincareCuspForm_apply (z : ℍ) : poincareCuspForm z = poincare z := by
  show pHalf z = poincare z
  unfold pHalf
  rw [pSeries_eq_two_mul_poincare]; ring

/-- **`PoincareIsCuspForm` holds** (the last hypothesis of the sub-Hecke bound). -/
theorem poincareIsCuspForm : PoincareIsCuspForm := ⟨poincareCuspForm, poincareCuspForm_apply⟩

end RamanujanTau.TauBound
