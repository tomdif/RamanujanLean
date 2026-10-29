import RamanujanTau.TheoremA.EtaCuspTransform

/-! Positive finite cusp rates imply analytic vanishing of the eta quotients. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Real

lemma cuspAffine_im (i : Fin 12) (j : Fin 4) (z : ℍ) :
    (cuspAffine i j z).im = ((cuspA i j : ℝ) / cuspD i j) * z.im := by
  simp [cuspAffine]

lemma cuspAffine_tendsto (i : Fin 12) (j : Fin 4) :
    Tendsto (cuspAffine i j) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  change Tendsto (fun z : ℍ => (cuspAffine i j z).im) _ atTop
  simp_rw [cuspAffine_im]
  exact tendsto_comap.const_mul_atTop
    (div_pos (by exact_mod_cast (cusp_positive i j).1)
      (by exact_mod_cast (cusp_positive i j).2))

lemma real_exp_int_mul (x : ℝ) (n : ℤ) : Real.exp (n * x) = Real.exp x ^ n := by
  apply Complex.ofReal_injective
  push_cast
  exact Complex.exp_int_mul _ _

noncomputable def deltaFactor (z : ℍ) : ℝ :=
  ‖∏' n : ℕ, (1 - eta_q n z) ^ 24‖

lemma deltaFactor_tendsto : Tendsto deltaFactor atImInfty (𝓝 1) := by
  simpa [deltaFactor] using tendsto_atImInfty_tprod_one_sub_eta_q_pow.norm

lemma norm_discriminant (z : ℍ) :
    ‖discriminant z‖ = Real.exp (-2 * π * z.im) * deltaFactor z := by
  rw [discriminant_eq_q_prod, norm_mul]
  congr 1
  simp [Function.Periodic.qParam, Complex.norm_exp]

noncomputable def cuspRate (a : Fin 3) (i : Fin 12) : ℝ :=
  ∑ j : Fin 4, (basisExponent a j : ℝ) * cuspA i j / cuspD i j

lemma cuspRate_pos (a : Fin 3) (i : Fin 12) : 0 < cuspRate a i := by
  unfold cuspRate
  exact_mod_cast cusp_rate_positive a i

lemma discriminant_product_norm (a : Fin 3) (i : Fin 12) (z : ℍ) :
    ‖∏ j : Fin 4, discriminant (cuspAffine i j z) ^ basisExponent a j‖ =
      Real.exp ((-2 * π * cuspRate a i) * z.im) *
        ∏ j : Fin 4, deltaFactor (cuspAffine i j z) ^ basisExponent a j := by
  simp only [norm_prod, norm_zpow, norm_discriminant, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  simp_rw [← real_exp_int_mul, cuspAffine_im]
  rw [← Real.exp_sum]
  congr 1
  unfold cuspRate
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma discriminant_product_zero (a : Fin 3) (i : Fin 12) :
    IsZeroAtImInfty (fun z : ℍ =>
      ∏ j : Fin 4, discriminant (cuspAffine i j z) ^ basisExponent a j) := by
  change Tendsto _ _ (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [discriminant_product_norm]
  have hp : Tendsto (fun z : ℍ =>
      ∏ j : Fin 4, deltaFactor (cuspAffine i j z) ^ basisExponent a j) atImInfty (𝓝 1) := by
    simpa using tendsto_finsetProd Finset.univ (fun j _ =>
      ((deltaFactor_tendsto.comp (cuspAffine_tendsto i j)).zpow₀
        (basisExponent a j) (Or.inl one_ne_zero)))
  have he : Tendsto (fun z : ℍ => Real.exp ((-2 * π * cuspRate a i) * z.im))
      atImInfty (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hr := cuspRate_pos a i
    have ht : Tendsto (fun z : ℍ => (2 * π * cuspRate a i) * z.im) atImInfty atTop :=
      tendsto_comap.const_mul_atTop (by positivity)
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp ht
  simpa using he.mul hp

lemma eta_product_pow (a : Fin 3) (i : Fin 12) (z : ℍ) :
    (∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ basisExponent a j) ^ 12 =
      ∏ j : Fin 4, discriminant (cuspAffine i j z) ^ basisExponent a j := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← zpow_natCast, ← zpow_mul, mul_comm (basisExponent a j), zpow_mul, zpow_natCast]
  congr 1
  simp [etaSquared, discriminant, ← pow_mul]

lemma zero_of_pow {f : ℍ → ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : IsZeroAtImInfty (fun z => f z ^ n)) : IsZeroAtImInfty f := by
  rw [isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := h (ε ^ n) (pow_pos hε n)
  refine ⟨A, fun z hz => le_of_pow_le_pow_left₀ hn hε.le ?_⟩
  simpa only [norm_pow] using hA z hz

/-- Every one of the twelve translates vanishes at infinity. -/
theorem basisFunction_rep_zero (a : Fin 3) (i : Fin 12) :
    IsZeroAtImInfty (basisFunction a ∣[(6 : ℤ)] LevelSix.rep i) := by
  have hp : IsZeroAtImInfty (fun z : ℍ =>
      ∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ basisExponent a j) := by
    apply zero_of_pow (n := 12) (by decide)
    simp_rw [eta_product_pow]
    exact discriminant_product_zero a i
  change Tendsto _ _ (𝓝 0)
  simpa only [← basisFunction_rep_apply, mul_zero] using hp.const_mul (cuspConstant a i)

end RamanujanTau.TheoremA.EtaSquared
