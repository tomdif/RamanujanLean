import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The Hecke bound for `G/η^j`

For a level-one cusp form `G` and `j < 24`, the function `G²⁴/Δ^j` is again a level-one cusp form.
The bound for it in Mathlib gives `|G/η^j| ≪ v^(-k/2)` with `k = k' - j/2`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open UpperHalfPlane ModularForm Filter Asymptotics
open scoped MatrixGroups Manifold

noncomputable section

variable {k' : ℤ}

/-- `G²⁴/Δ^j` as a function. -/
def kFun (G : CuspForm 𝒮ℒ k') (j : ℕ) (τ : ℍ) : ℂ := G τ ^ 24 / discriminant τ ^ j

lemma kFun_smul (G : CuspForm 𝒮ℒ k') (j : ℕ) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) (τ : ℍ) :
    kFun G j (γ • τ) = denom γ τ ^ (24 * k' - 12 * (j : ℤ)) * kFun G j τ := by
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ _
  have hG := SlashInvariantForm.slash_action_eqn'' G hγ τ
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  have hD' : discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * discriminant τ := hD
  have h0 := discriminant_ne_zero τ
  unfold kFun
  rw [hG, hD', mul_pow, mul_pow, ← zpow_natCast, ← zpow_natCast (denom γ τ ^ (12 : ℤ)),
    ← zpow_mul, ← zpow_mul, zpow_sub₀ hd]
  push_cast
  field_simp
  rw [mul_comm k' 24]
  ring

/-- The function `G²⁴/Δ^j` is holomorphic. -/
lemma kFun_mdiff (G : CuspForm 𝒮ℒ k') (j : ℕ) : MDiff (kFun G j) := by
  have hG : MDiff G := CuspFormClass.holo G
  have hD : MDiff discriminant := CuspFormClass.holo CuspForm.discriminant
  rw [UpperHalfPlane.mdifferentiable_iff] at hG hD ⊢
  refine ((hG.pow 24).div (hD.pow j) fun z hz => ?_).congr fun z hz => ?_
  · exact pow_ne_zero j (discriminant_ne_zero _)
  · simp [kFun, Function.comp]

lemma kFun_isZero (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) : IsZeroAtImInfty (kFun G j) := by
  have hO := CuspForm.exp_decay_isBigO_discriminant G
  obtain ⟨C, hC, hb⟩ := hO.exists_pos
  have hb' := hb.bound
  have hbound : ∀ᶠ τ in atImInfty, ‖kFun G j τ‖ ≤ C ^ 24 * ‖discriminant τ‖ ^ (24 - j) := by
    filter_upwards [hb'] with τ hτ
    have h0 : ‖discriminant τ‖ ≠ 0 := norm_ne_zero_iff.mpr (discriminant_ne_zero τ)
    unfold kFun
    rw [norm_div, norm_pow, norm_pow, div_le_iff₀ (by positivity), mul_assoc, ← pow_add,
      Nat.sub_add_cancel hj.le, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hτ 24
  have hto : Tendsto (fun τ : ℍ => C ^ 24 * ‖discriminant τ‖ ^ (24 - j)) atImInfty (nhds 0) := by
    have h1 : Tendsto (fun τ : ℍ => ‖discriminant τ‖) atImInfty (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp discriminant_isZeroAtImInfty
    have h2 := (h1.pow (24 - j)).const_mul (C ^ 24)
    rw [zero_pow (by omega), mul_zero] at h2
    exact h2
  exact squeeze_zero_norm' hbound hto

lemma kFun_slash (G : CuspForm 𝒮ℒ k') (j : ℕ) (γ : SL(2, ℤ)) :
    kFun G j ∣[24 * k' - 12 * (j : ℤ)] γ = kFun G j := by
  ext τ
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hd : denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply]
  have h := kFun_smul G j hmem τ
  change kFun G j (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ) * _ = _
  rw [h]
  have e : denom γ τ = denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := rfl
  rw [e, zpow_neg]
  field_simp

/-- `G²⁴/Δ^j` as a cusp form. -/
def kForm (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) : CuspForm 𝒮ℒ (24 * k' - 12 * (j : ℤ)) where
  toFun := kFun G j
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact kFun_slash G j γ
  holo' := kFun_mdiff G j
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [kFun_slash]
    exact kFun_isZero G hj

/-- **The Hecke bound for `G/η^j`.** -/
theorem hecke_half (G : CuspForm 𝒮ℒ k') {j : ℕ} (hj : j < 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, ‖G τ / η (τ : ℂ) ^ j‖ ≤ C * τ.im ^ (-((k' : ℝ) / 2 - j / 4)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (kForm G hj)
  have hC0 : 0 ≤ C := by
    have h := hC UpperHalfPlane.I
    have h1 := (norm_nonneg _).trans h
    have h2 : 0 < UpperHalfPlane.I.im ^ (((24 * k' - 12 * (j : ℤ) : ℤ) : ℝ) / 2) := by
      have := UpperHalfPlane.I.im_pos
      positivity
    exact (div_nonneg_iff.mp h1).elim (·.1) fun h3 => absurd h3.2 (not_le.mpr h2)
  refine ⟨C ^ ((1 : ℝ) / 24), by positivity, fun τ => ?_⟩
  have hw := τ.im_pos
  have h1 : ‖G τ / η (τ : ℂ) ^ j‖ ^ 24 = ‖kFun G j τ‖ := by
    unfold kFun discriminant
    simp only [norm_div, norm_pow]
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring
  have h2 : ‖kFun G j τ‖ ≤ C / τ.im ^ (((24 * k' - 12 * (j : ℤ) : ℤ) : ℝ) / 2) := hC τ
  have h3 : (C ^ ((1 : ℝ) / 24) * τ.im ^ (-((k' : ℝ) / 2 - j / 4))) ^ 24 =
      C / τ.im ^ (((24 * k' - 12 * (j : ℤ) : ℤ) : ℝ) / 2) := by
    have e1 : (C ^ ((1 : ℝ) / 24)) ^ 24 = C := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hC0]
      norm_num
    have e2 : (τ.im ^ (-((k' : ℝ) / 2 - j / 4))) ^ 24 =
        (τ.im ^ (((24 * k' - 12 * (j : ℤ) : ℤ) : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le, ← Real.rpow_neg hw.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, e1, e2]
    exact (div_eq_mul_inv _ _).symm
  have h4 : ‖G τ / η (τ : ℂ) ^ j‖ ^ 24 ≤
      (C ^ ((1 : ℝ) / 24) * τ.im ^ (-((k' : ℝ) / 2 - j / 4))) ^ 24 := by
    rw [h1, h3]
    exact h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h4

end

end RamanujanTau.ThetaLift
