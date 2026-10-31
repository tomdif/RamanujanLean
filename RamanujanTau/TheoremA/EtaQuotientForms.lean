import RamanujanTau.TheoremA.EtaCuspDecay

/-!
# A finite certificate for level-six eta quotients of arbitrary weight

An integral exponent vector for η(z)², η(2z)², η(3z)², η(6z)² defines an
actual modular form when the 24 generator phases vanish and the twelve
cusp rates are nonnegative. Zero cusp rates are allowed. This extends the
strictly cuspidal weight-six construction to the forms needed for the
graded ring of level-six modular forms.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm CongruenceSubgroup Filter Asymptotics
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold Topology Real

noncomputable def quotientFunction (r : Fin 4 → ℤ) (z : ℍ) : ℂ :=
  ∏ j : Fin 4, scaledEta (dilation j) (dilation_pos j) z ^ r j

def PhaseCertificate (r : Fin 4 → ℤ) : Prop :=
  ∀ b i, 12 ∣ ∑ j : Fin 4, wordExponent (generatorWord b i j) * r j

def CuspCertificate (r : Fin 4 → ℤ) : Prop :=
  ∀ i, 0 ≤ ∑ j : Fin 4, (r j : ℚ) * cuspA i j / cuspD i j

theorem quotientFunction_generator (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r) (b : Bool) (i : Fin 12) :
    quotientFunction r ∣[k] LevelSix.generator (b, i) = quotientFunction r := by
  ext z
  rw [SL_slash_apply]
  simp only [quotientFunction, scaledEta_generator_apply, mul_zpow,
    Finset.prod_mul_distrib]
  have hphase : (∏ j : Fin 4, phase (wordExponent (generatorWord b i j)) ^ r j) = 1 := by
    simp_rw [← phase_mul]
    rw [← phase_sum]
    exact phase_eq_one_of_dvd (hp b i)
  have hd := denom_ne_zero (LevelSix.generator (b, i)) z
  rw [hphase, one_mul, ← zpow_sum_of_ne_zero _ _ hd, hk]
  rw [mul_assoc, ← zpow_add₀ hd]
  simp

theorem quotientFunction_slash (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 6) :
    quotientFunction r ∣[k] γ = quotientFunction r :=
  LevelSix.slash_invariant_of_generators (quotientFunction_generator r hk hp) γ hγ

theorem quotientFunction_ne_zero (r : Fin 4 → ℤ) (z : ℍ) :
    quotientFunction r z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact zpow_ne_zero _ (scaledEta_ne_zero _ _ _)

theorem quotientFunction_holo (r : Fin 4 → ℤ) : MDiff (quotientFunction r) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  let F : ℂ → ℂ := fun z => ∏ j : Fin 4, (eta ((dilation j : ℂ) * z) ^ 2) ^ r j
  have hF : DifferentiableOn ℂ F upperHalfPlaneSet := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.fun_finsetProd
    intro j _
    have hd : (dilation j : ℝ) > 0 := by exact_mod_cast dilation_pos j
    have hpos : (dilation j : ℂ) * z ∈ upperHalfPlaneSet := by
      simpa using mul_pos hd hz
    exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hpos).comp z
      (by fun_prop)).pow 2).zpow (Or.inl (pow_ne_zero _ (eta_ne_zero hpos)))
  refine hF.congr fun z hz => ?_
  simp [F, quotientFunction, scaledEta, etaSquared, scale, ofComplex_apply_of_im_pos hz]

noncomputable def quotientCuspConstant (r : Fin 4 → ℤ) (i : Fin 12) : ℂ :=
  ∏ j : Fin 4, (phase (wordExponent (cuspWord i j)) / cuspD i j) ^ r j

theorem quotientFunction_rep_apply (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (i : Fin 12) (z : ℍ) :
    (quotientFunction r ∣[k] LevelSix.rep i) z =
      quotientCuspConstant r i * ∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ r j := by
  rw [SL_slash_apply]
  simp only [quotientFunction, scaledEta_rep_apply, mul_zpow, Finset.prod_mul_distrib]
  rw [← zpow_sum_of_ne_zero _ _ (denom_ne_zero _ _), hk,
    mul_assoc, ← zpow_add₀ (denom_ne_zero _ _)]
  simp [quotientCuspConstant]

noncomputable def quotientCuspRate (r : Fin 4 → ℤ) (i : Fin 12) : ℝ :=
  ∑ j : Fin 4, (r j : ℝ) * cuspA i j / cuspD i j

theorem quotientCuspRate_nonneg (r : Fin 4 → ℤ) (hc : CuspCertificate r) (i : Fin 12) :
    0 ≤ quotientCuspRate r i := by
  unfold quotientCuspRate
  exact_mod_cast hc i

lemma quotient_discriminant_product_norm (r : Fin 4 → ℤ) (i : Fin 12) (z : ℍ) :
    ‖∏ j : Fin 4, discriminant (cuspAffine i j z) ^ r j‖ =
      Real.exp ((-2 * π * quotientCuspRate r i) * z.im) *
        ∏ j : Fin 4, deltaFactor (cuspAffine i j z) ^ r j := by
  simp only [norm_prod, norm_zpow, norm_discriminant, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  simp_rw [← real_exp_int_mul, cuspAffine_im]
  rw [← Real.exp_sum]
  congr 1
  unfold quotientCuspRate
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quotient_discriminant_product_bdd (r : Fin 4 → ℤ) (i : Fin 12)
    (hr : 0 ≤ quotientCuspRate r i) :
    IsBoundedAtImInfty (fun z : ℍ => ∏ j : Fin 4,
      discriminant (cuspAffine i j z) ^ r j) := by
  have hp : Tendsto (fun z : ℍ => ∏ j : Fin 4,
      deltaFactor (cuspAffine i j z) ^ r j) atImInfty (𝓝 1) := by
    simpa using tendsto_finsetProd Finset.univ (fun j _ =>
      (deltaFactor_tendsto.comp (cuspAffine_tendsto i j)).zpow₀ (r j) (Or.inl one_ne_zero))
  have hpO : IsBoundedAtImInfty (fun z : ℍ => ∏ j : Fin 4,
      deltaFactor (cuspAffine i j z) ^ r j) := hp.isBigO_one ℝ
  rw [isBoundedAtImInfty_iff] at hpO ⊢
  obtain ⟨M, A, hM⟩ := hpO
  refine ⟨M, A, fun z hz => ?_⟩
  rw [quotient_discriminant_product_norm]
  have he : Real.exp ((-2 * π * quotientCuspRate r i) * z.im) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnonneg : 0 ≤ (2 * π * quotientCuspRate r i) * z.im := by positivity
    nlinarith
  have hpos : 0 ≤ ∏ j : Fin 4, deltaFactor (cuspAffine i j z) ^ r j := by
    apply Finset.prod_nonneg
    intro j _
    exact zpow_nonneg (norm_nonneg _) _
  exact (mul_le_of_le_one_left hpos he).trans
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hM z hz)

lemma quotient_eta_product_pow (r : Fin 4 → ℤ) (i : Fin 12) (z : ℍ) :
    (∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ r j) ^ 12 =
      ∏ j : Fin 4, discriminant (cuspAffine i j z) ^ r j := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← zpow_natCast, ← zpow_mul, mul_comm (r j), zpow_mul, zpow_natCast]
  congr 1
  simp [etaSquared, discriminant, ← pow_mul]

lemma bounded_of_pow {f : ℍ → ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : IsBoundedAtImInfty (fun z => f z ^ n)) : IsBoundedAtImInfty f := by
  rw [isBoundedAtImInfty_iff] at h ⊢
  obtain ⟨M, A, hM⟩ := h
  refine ⟨max 1 M, A, fun z hz => ?_⟩
  apply le_of_pow_le_pow_left₀ hn (by positivity)
  have hpow : M ≤ (max 1 M) ^ n :=
    (le_max_right 1 M).trans (le_self_pow₀ (le_max_left 1 M) hn)
  have hb : ‖f z‖ ^ n ≤ M := by simpa only [norm_pow] using hM z hz
  exact hb.trans hpow

theorem quotientFunction_rep_bdd (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hc : CuspCertificate r) (i : Fin 12) :
    IsBoundedAtImInfty (quotientFunction r ∣[k] LevelSix.rep i) := by
  have hb : IsBoundedAtImInfty (fun z : ℍ =>
      ∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ r j) := by
    apply bounded_of_pow (n := 12) (by decide)
    simp_rw [quotient_eta_product_pow]
    exact quotient_discriminant_product_bdd r i (quotientCuspRate_nonneg r hc i)
  simpa only [← quotientFunction_rep_apply r hk] using hb.const_mul_left (quotientCuspConstant r i)

theorem quotientFunction_slash_bdd (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r) (hc : CuspCertificate r)
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty (quotientFunction r ∣[k] γ) := by
  obtain ⟨i, hi⟩ := LevelSix.exists_rep γ
  have he : γ = (γ * (LevelSix.rep i)⁻¹) * LevelSix.rep i := by group
  rw [he, SlashAction.slash_mul, quotientFunction_slash r hk hp _ hi]
  exact quotientFunction_rep_bdd r hk hc i

/-- A finite, exact eta-quotient certificate produces an actual modular form. -/
noncomputable def quotientModularForm (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r) (hc : CuspCertificate r) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := quotientFunction r
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact quotientFunction_slash r hk hp γ hγ
  holo' := quotientFunction_holo r
  bdd_at_cusps' h := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at h
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z h]
    intro γ _
    exact quotientFunction_slash_bdd r hk hp hc γ

@[simp] theorem quotientModularForm_apply (r : Fin 4 → ℤ) {k : ℤ}
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r) (hc : CuspCertificate r) (z : ℍ) :
    quotientModularForm r hk hp hc z = quotientFunction r z := rfl

end RamanujanTau.TheoremA.EtaSquared
