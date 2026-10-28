import RamanujanTau.RamanujanODE.QSeries
import RamanujanTau.RamanujanODE.SerreSlash
import RamanujanTau.Igusa.Serre

/-!
# Ramanujan's differential equations

`ramanujanODE : Igusa.RamanujanODE`, i.e. over `ℤ⟦q⟧`
  `3 θE₄ = E₂E₄ − E₆`, `2 θE₆ = E₂E₆ − E₄²`, `12 θE₂ = E₂² − E₄`.

Proof: the Serre derivatives `∂₄E₄`, `∂₆E₆`, `∂₁E₂ = D E₂ − E₂²/12` are level-one modular forms of
weights `6, 8, 4` (`SerreSlash`); their q-expansions are computed term by term (`QSeries`); weight
`< 12` forms are determined by their constant term; descend from `ℂ` to `ℤ`.
-/

set_option autoImplicit false

namespace RamanujanODEProof
open UpperHalfPlane hiding I
open Complex Filter Function Derivative ModularForm EisensteinSeries ModularFormClass
open scoped MatrixGroups Manifold

noncomputable section

lemma isQSeries_mf {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    IsQSeries f (fun n => (qExpansion 1 f).coeff n) := fun τ =>
  hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f
    one_mem_strictPeriods_SL) (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

lemma mk_e2c : PowerSeries.mk e2c = Igusa.E2 ℂ := by
  ext n
  simp only [PowerSeries.coeff_mk, Igusa.E2, Igusa.e2Z, PowerSeries.coeff_map, e2c]
  rw [show (24 : PowerSeries ℤ) = PowerSeries.C (24 : ℤ) by simp, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_mk]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]

lemma serre_eq (k : ℂ) (F : ℍ → ℂ) :
    serreDerivative k F = D F - (k * 12⁻¹) • (E2 * F) := by
  ext z; simp only [serreDerivative_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul]; ring

lemma serre_bdd (k : ℂ) {F : ℍ → ℂ} {c : ℕ → ℂ} (hF : IsQSeries F c) :
    IsBoundedAtImInfty (serreDerivative k F) := by
  rw [serre_eq]
  exact hF.D.isBoundedAtImInfty.add
    ((isQSeries_E2.isBoundedAtImInfty.mul hF.isBoundedAtImInfty).smul _).neg

lemma qExpansion_serre (k : ℂ) {F : ℍ → ℂ} {c : ℕ → ℂ} (hF : IsQSeries F c) (hhol : MDiff F) :
    qExpansion 1 (serreDerivative k F) =
      Igusa.theta (PowerSeries.mk c) - (k * 12⁻¹) • (Igusa.E2 ℂ * PowerSeries.mk c) := by
  have hDa := hF.D.analyticAt (normalizedDerivOfComplex_mdifferentiable hhol)
  have hEa := isQSeries_E2.analyticAt E2_mdifferentiable
  have hFa := hF.analyticAt hhol
  have hPa : AnalyticAt ℂ (cuspFunction 1 (E2 * F)) 0 := by
    rw [cuspFunction_mul hEa.continuousAt hFa.continuousAt]; exact hEa.mul hFa
  have hSa : AnalyticAt ℂ (cuspFunction 1 ((k * 12⁻¹) • (E2 * F))) 0 := by
    rw [cuspFunction_smul hPa.continuousAt]; exact hPa.const_smul
  rw [serre_eq, qExpansion_sub hDa hSa, qExpansion_smul hPa, qExpansion_mul hEa hFa,
    hF.D.qExpansion_eq (normalizedDerivOfComplex_mdifferentiable hhol),
    isQSeries_E2.qExpansion_eq E2_mdifferentiable, hF.qExpansion_eq hhol, mk_e2c]
  congr 1
  ext n; simp [Igusa.coeff_theta]

/-- The Serre derivative of a level-one modular form, as a modular form. -/
def serreMF (k : ℤ) (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k + 2) where
  toFun := serreDerivative k f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    have hf : (f : ℍ → ℂ) ∣[k] A = f :=
      SlashInvariantFormClass.slash_action_eq f (A : GL (Fin 2) ℝ) ⟨A, rfl⟩
    exact serre_slash_invariant k f (ModularFormClass.holo f) A hf
  holo' := serreDerivative_mdifferentiable _ (ModularFormClass.holo f)
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hf : (f : ℍ → ℂ) ∣[k] γ = f :=
      SlashInvariantFormClass.slash_action_eq f (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
    rw [serre_slash_invariant k f (ModularFormClass.holo f) γ hf]
    exact serre_bdd _ (isQSeries_mf f)

/-- `∂₁E₂ = D E₂ − E₂²/12` as a modular form of weight 4. -/
def serreE2MF : ModularForm 𝒮ℒ 4 where
  toFun := serreDerivative 1 E2
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact serreE2_slash_invariant A
  holo' := serreDerivative_mdifferentiable _ E2_mdifferentiable
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [serreE2_slash_invariant γ]
    exact serre_bdd _ isQSeries_E2

/-- A level-one form of weight `< 12` with vanishing constant term is zero. -/
lemma qExpansion_eq_zero_of_coeff_zero {k : ℤ} (hk : k < 12) (G : ModularForm 𝒮ℒ k)
    (h0 : (qExpansion 1 G).coeff 0 = 0) : qExpansion 1 G = 0 := by
  have hr := CuspForm.rank_eq_zero_of_weight_lt_twelve hk
  rw [rank_zero_iff_forall_zero] at hr
  have : (G : ℍ → ℂ) = 0 := by
    ext z
    have := congrArg (fun F : CuspForm 𝒮ℒ k => F z) (hr (ModularForm.toCuspForm G h0))
    simpa using this
  rw [this, qExpansion_zero]

/-- If `F, M` have weight `k < 12` and `M` has constant term `1`, then `F = F₀ · M`. -/
lemma qExpansion_eq_const_smul {k : ℤ} (hk : k < 12) (F M : ModularForm 𝒮ℒ k)
    (hM : (qExpansion 1 M).coeff 0 = 1) :
    qExpansion 1 F = (qExpansion 1 F).coeff 0 • qExpansion 1 M := by
  set c := (qExpansion 1 F).coeff 0
  have hq : qExpansion 1 ((F - c • M : ModularForm 𝒮ℒ k) : ℍ → ℂ) =
      qExpansion 1 F - c • qExpansion 1 M := by
    rw [ModularForm.coe_sub, qExpansion_sub (ModularFormClass.analyticAt_cuspFunction_zero F
      one_pos one_mem_strictPeriods_SL) (by
        rw [show ((c • M : ModularForm 𝒮ℒ k) : ℍ → ℂ) = c • (M : ℍ → ℂ) from rfl,
          cuspFunction_smul (ModularFormClass.analyticAt_cuspFunction_zero M one_pos
            one_mem_strictPeriods_SL).continuousAt]
        exact (ModularFormClass.analyticAt_cuspFunction_zero M one_pos
          one_mem_strictPeriods_SL).const_smul),
      show ((c • M : ModularForm 𝒮ℒ k) : ℍ → ℂ) = c • (M : ℍ → ℂ) from rfl,
      qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero M one_pos
        one_mem_strictPeriods_SL)]
  have h0 := qExpansion_eq_zero_of_coeff_zero hk (F - c • M) (by
    rw [hq, map_sub, PowerSeries.coeff_smul, hM]; simp [c])
  rw [hq] at h0
  exact sub_eq_zero.mp h0

/-! ### The three identities over `ℂ` -/

lemma coeff_zero_theta (f : PowerSeries ℂ) : (Igusa.theta f).coeff 0 = 0 := by
  simp [Igusa.coeff_theta]

lemma constantCoeff_E2 : (Igusa.E2 ℂ).coeff 0 = 1 := by
  rw [← mk_e2c, PowerSeries.coeff_mk]; simp [e2c]

lemma mf_E4 : PowerSeries.mk (fun n => (qExpansion 1 E₄).coeff n) = ModP.E4 ℂ := by
  ext n; rw [PowerSeries.coeff_mk, ModP.qExpansion_E4]

lemma mf_E6 : PowerSeries.mk (fun n => (qExpansion 1 E₆).coeff n) = ModP.E6 ℂ := by
  ext n; rw [PowerSeries.coeff_mk, ModP.qExpansion_E6]

lemma c0E4 : (ModP.E4 ℂ).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ModP.constantCoeff_E4]

lemma c0E6 : (ModP.E6 ℂ).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ModP.constantCoeff_E6]

lemma coeff_zero_mul' (f g : PowerSeries ℂ) : (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

lemma finish {A P E : PowerSeries ℂ} {a c m : ℂ} (h : A - a • P = c • E) (hc : c = -a)
    (hm : m * a = 1) : PowerSeries.C m * A = P - E := by
  subst hc
  rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_neg] at h
  have hma : PowerSeries.C m * PowerSeries.C a = 1 := by rw [← map_mul, hm, map_one]
  linear_combination PowerSeries.C m * h + (P - E) * hma

theorem ode4_C : 3 * Igusa.theta (ModP.E4 ℂ) = Igusa.E2 ℂ * ModP.E4 ℂ - ModP.E6 ℂ := by
  have hS := qExpansion_serre (4 : ℤ) (isQSeries_mf E₄) (ModularFormClass.holo E₄)
  rw [mf_E4] at hS
  have hC := qExpansion_eq_const_smul (k := 6) (by norm_num)
    (ModularForm.mcast (by norm_num) (serreMF 4 E₄)) E₆ (by rw [ModP.qExpansion_E6, c0E6])
  rw [ModP.qExpansion_mcast, ModP.qExpansion_E6] at hC
  change qExpansion 1 (serreDerivative (4 : ℤ) E₄) = _ at hC
  rw [hS] at hC
  have h0 := congrArg (PowerSeries.coeff 0) hC
  simp only [map_sub, PowerSeries.coeff_smul, coeff_zero_theta, smul_eq_mul, c0E6,
    coeff_zero_mul', constantCoeff_E2, c0E4] at h0
  rw [show (3 : PowerSeries ℂ) = PowerSeries.C 3 from (map_ofNat PowerSeries.C 3).symm]
  exact finish hC (by push_cast at h0 ⊢; linear_combination -h0) (by norm_num)

theorem ode6_C : 2 * Igusa.theta (ModP.E6 ℂ) = Igusa.E2 ℂ * ModP.E6 ℂ - ModP.E4 ℂ ^ 2 := by
  have hS := qExpansion_serre (6 : ℤ) (isQSeries_mf E₆) (ModularFormClass.holo E₆)
  rw [mf_E6] at hS
  have hM : qExpansion 1 (ModularForm.mcast (show (4 : ℤ) + 4 = 8 by norm_num) (E₄.mul E₄)) =
      ModP.E4 ℂ ^ 2 := by
    rw [ModP.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModP.qExpansion_E4, sq]
  have hC := qExpansion_eq_const_smul (k := 8) (by norm_num)
    (ModularForm.mcast (by norm_num) (serreMF 6 E₆))
    (ModularForm.mcast (show (4 : ℤ) + 4 = 8 by norm_num) (E₄.mul E₄))
    (by rw [hM, sq, coeff_zero_mul', c0E4, mul_one])
  rw [ModP.qExpansion_mcast, hM] at hC
  change qExpansion 1 (serreDerivative (6 : ℤ) E₆) = _ at hC
  rw [hS] at hC
  have h0 := congrArg (PowerSeries.coeff 0) hC
  simp only [map_sub, PowerSeries.coeff_smul, coeff_zero_theta, smul_eq_mul, sq,
    coeff_zero_mul', constantCoeff_E2, c0E4, c0E6] at h0
  rw [show (2 : PowerSeries ℂ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm]
  exact finish hC (by push_cast at h0 ⊢; linear_combination -h0) (by norm_num)

theorem ode2_C : 12 * Igusa.theta (Igusa.E2 ℂ) = Igusa.E2 ℂ ^ 2 - ModP.E4 ℂ := by
  have hS := qExpansion_serre (1 : ℂ) isQSeries_E2 E2_mdifferentiable
  rw [mk_e2c] at hS
  have hC := qExpansion_eq_const_smul (k := 4) (by norm_num) serreE2MF E₄
    (by rw [ModP.qExpansion_E4, c0E4])
  rw [ModP.qExpansion_E4] at hC
  change qExpansion 1 (serreDerivative (1 : ℂ) E2) = _ at hC
  rw [hS] at hC
  have h0 := congrArg (PowerSeries.coeff 0) hC
  simp only [map_sub, PowerSeries.coeff_smul, coeff_zero_theta, smul_eq_mul,
    coeff_zero_mul', constantCoeff_E2, c0E4] at h0
  rw [show (12 : PowerSeries ℂ) = PowerSeries.C 12 from (map_ofNat PowerSeries.C 12).symm, sq]
  exact finish hC (by linear_combination -h0) (by norm_num)

/-! ### Descent to `ℤ` -/

lemma descendZ {X Y : PowerSeries ℤ}
    (h : PowerSeries.map (Int.castRingHom ℂ) X = PowerSeries.map (Int.castRingHom ℂ) Y) : X = Y :=
  PowerSeries.map_injective _ (RingHom.injective_int _) h

/-- **Ramanujan's differential equations** `3θE₄ = E₂E₄ − E₆`, `2θE₆ = E₂E₆ − E₄²`,
`12θE₂ = E₂² − E₄` in `ℤ⟦q⟧`. -/
theorem ramanujanODE : Igusa.RamanujanODE := by
  refine ⟨descendZ ?_, descendZ ?_, descendZ ?_⟩
  · simpa [Igusa.map_theta, ModP.map_E4, ModP.map_E6, Igusa.map_E2, map_ofNat] using ode4_C
  · simpa [Igusa.map_theta, ModP.map_E4, ModP.map_E6, Igusa.map_E2, map_ofNat] using ode6_C
  · simpa [Igusa.map_theta, ModP.map_E4, ModP.map_E6, Igusa.map_E2, map_ofNat] using ode2_C

end

end RamanujanODEProof

