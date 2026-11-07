import RamanujanTau.ThetaLift.KernelFold

/-!
# The term `(a,m) = (0,0)`

The term is independent of `w`, so it contributes a multiple of `y^(1-λ)` to the kernel.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex MeasureTheory
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups ModularForm ENNReal
open Rademacher ModularForm

noncomputable section

/-- The dual exponent at `(0,0)` does not depend on `w`. -/
lemma KData.dualE_00 (D : KData) (b : ℤ) :
    D.dualE 0 b 0 = D.σ * b / D.z - (π * D.vt * D.N * b ^ 2 / 6 : ℝ) -
      3 * D.σ ^ 2 / (2 * π * D.N * D.vt * D.z ^ 2) := by
  have hz := D.z_ne
  have hN := D.N_ne
  have hy := D.y_ne
  have hκ := D.κ_ne
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hvt : (D.vt : ℂ) ≠ 0 := by exact_mod_cast D.vt_pos.ne'
  have hκe : (D.κ : ℂ) = π * D.vt / (6 * D.N * D.y ^ 2) := by
    unfold KData.κ
    push_cast
    rfl
  unfold KData.dualE KData.τ₂ KData.τ₁ KData.s
  rw [hκe]
  push_cast
  field_simp
  linear_combination (72 * D.σ ^ 2 - 48 * D.N * D.z * π * D.vt * b * D.σ) * Complex.I_sq

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N) (lam : ℕ)

/-- The derivative of the term `(0,0)`, in terms of `z` alone. -/
def d00 (z : ℍ) : ℂ :=
  iteratedDeriv lam (fun s => ((kd 1 one_pos N hN 0 z).atσ s).dF 0 0) 0

/-- The term `(0,0)` is independent of `w`. -/
lemma dF00_indep {y : ℝ} (hy : 0 < y) (ξ : ℝ) (z : ℍ) (s : ℂ) :
    ((kd y hy N hN ξ z).atσ s).dF 0 0 = ((kd 1 one_pos N hN 0 z).atσ s).dF 0 0 := by
  unfold KData.dF KData.dualF
  refine tsum_congr fun b => ?_
  rw [KData.dualE_00, KData.dualE_00]
  rfl

/-- **The decomposition of the integrand.** -/
theorem phiI_decomp (hy' : 0 < (1 : ℝ)) (ξ : ℝ) {y : ℝ} (hy : 0 < y) (z : ℍ)
    {w : ℕ} (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) :
    phiI G j hN lam ((ξ : ℂ) + y * I) z =
      (((y ^ lam)⁻¹ * y : ℝ) : ℂ) * (((chiZ N : ℂ) * e24 (-3)) *
        ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z) +
          jN N 0 * ((sqrt (z : ℂ))⁻¹ * (cV' G j lam hN z * d00 hN lam z))) := by
  set D := kd y hy N hN ξ z with hD
  have hfold := fold_sum G j hN lam ξ y ht2 ht3 htj hjw hk hy z
  have hexp := D.kernel_expand (jN N) (norm_jN_le N) lam
  have hd00 : iteratedDeriv lam (fun s => (D.atσ s).dF 0 0) 0 = d00 hN lam z := by
    unfold d00
    congr 1
    funext s
    exact dF00_indep hN hy ξ z s
  have hSf := (D.taylor_dual (jN N) (norm_jN_le N) lam).summable
  have hsplit : ∑' p : ℤ × ℤ, jN N p.1 * iteratedDeriv lam (fun s => (D.atσ s).dF p.1 p.2) 0 =
      jN N 0 * d00 hN lam z + ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p := by
    classical
    rw [hSf.tsum_eq_add_tsum_ite ((0, 0) : ℤ × ℤ), hd00]
    congr 1
  rw [hsplit] at hexp
  have hsc0 : D.sc ≠ 0 := by
    have hz := D.z_ne
    have hN' := D.N_ne
    have hy' := D.y_ne
    exact div_ne_zero I_ne_zero (mul_ne_zero (mul_ne_zero hN' hz) hy')
  have hscp := pow_ne_zero lam hsc0
  have hS : ∑' x : ℤ × ℤ × ℤ, kTerm (jN N) N (kvt N z) (kZc N z) lam ((ξ : ℂ) + y * I) x =
      (D.sc ^ lam)⁻¹ * (((√(π / D.κ) : ℝ) : ℂ) *
        (jN N 0 * d00 hN lam z + ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p)) := by
    rw [← hexp, ← mul_assoc, inv_mul_cancel₀ hscp, one_mul]
    rfl
  have hc := constant_identity hN lam ξ y hy z
  have hz0 : (z : ℂ) ≠ 0 := D.z_ne
  have hsq : sqrt (z : ℂ) ≠ 0 := by
    rw [sqrt_exp_half hz0]
    exact Complex.exp_ne_zero _
  have him : ((ξ : ℂ) + y * I).im = y := by simp
  unfold phiI kernel
  rw [him, hS]
  push_cast at hc ⊢
  set P := qZ N lam z * ((y : ℂ) ^ (2 * lam))⁻¹ * (D.sc ^ lam)⁻¹ * ((√(π / D.κ) : ℝ) : ℂ) with hP
  have hP2 : P = ((y : ℂ) ^ lam)⁻¹ * y * (sqrt (z : ℂ))⁻¹ := by
    rw [← hc]
    field_simp
  calc _ = P * (cV' G j lam hN z * ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p) +
        P * (cV' G j lam hN z * (jN N 0 * d00 hN lam z)) := by
        rw [hP]
        ring
    _ = _ := by
      rw [hfold, hP2]
      field_simp

instance (N : ℕ) : Countable (cosetN N) := Quotient.countable

include hN in
/-- **The fold of a translation-invariant function is integrable.** -/
theorem integrableOn_fold (ξ y : ℝ) {w : ℕ} {hj : j < 24} (hy : 0 < y) (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N)
    (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w) (hk : k' = ((lam + w : ℕ) : ℤ)) :
    IntegrableOn (fun z : ℍ => ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z))
        (domainOf (gN N)) ∧
      ∫ z in domainOf (gN N), ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z) =
        ∫ z in stripSet, fTot G j hN lam ξ y (psiG N) z := by
  have hF := isFundamentalDomain_domainOf (gN N) (neg_one_mem N)
  have hSt := exactDomain_strip (T_mem N)
  have hg1 : ∀ g, ‖psiG N g‖ ≤ 1 := by
    intro g
    unfold psiG
    split_ifs
    · simp
    · exact norm_jN_le N _
  have hg0 : psiG N 0 = 0 := by simp [psiG]
  obtain ⟨-, hint, -⟩ := strip_total G j hN lam ξ y (hj := hj) hy hg1 hg0
  set f := fTot G j hN lam ξ y (psiG N) with hf
  have hinv := fTot_inv G j hN lam ξ y ht2 ht3 htj hjw hk (psiG N)
  have hmeas : Measurable f := by
    unfold fTot at hf
    rw [hf]
    exact Measurable.tsum fun g => (measurable_Hg G j hN lam ξ y g).const_mul _
  have hunf := unfold_integral hF hSt measurableSet_stripSet hint hinv
  refine ⟨?_, hunf.2.symm⟩
  have hsm : Measurable fun z : ℍ => ∑' r : cosetN N, f (r.out⁻¹ • z) :=
    Measurable.tsum fun r => hmeas.comp (measurable_const_smul _)
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  have hl := unfold_lintegral hF hSt measurableSet_stripSet (f := fun z => ‖f z‖ₑ) hmeas.enorm
    (fun a x => congrArg (fun u : ℂ => ‖u‖ₑ) (hinv a x))
  have hfin : ∫⁻ x in stripSet, ‖f x‖ₑ < ⊤ := hint.2
  rw [hl] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hfin
  exact enorm_tsum_le_tsum_enorm

/-- The power of `y` in front of the kernel. -/
def rY (lam : ℕ) (y : ℝ) : ℝ := (y ^ lam)⁻¹ * y

/-- The obstruction attached to `γ` and `t`. -/
def alphaF (lam : ℕ) (γ : SL(2, ℤ)) (t : ℂ) : ℂ :=
  (rY lam (mob γ t).im : ℂ) - lin γ t ^ (2 * lam) * (rY lam t.im : ℂ)

/-- The difference of the two sides of the covariance law. -/
def defectT (lam : ℕ) (γ : SL(2, ℤ)) (t : ℂ) : ℂ :=
  lamSum G j (N := N) (jN N) lam (mob γ t).re (mob γ t).im -
    lin γ t ^ (2 * lam) * lamSum G j (N := N) (jN N) lam t.re t.im

/-- The integrand of the defect. -/
def defX (lam : ℕ) (γ : SL(2, ℤ)) (t : ℂ) (z : ℍ) : ℂ :=
  lin γ t ^ (2 * lam) * (rY lam t.im : ℂ) *
      ∑' r : cosetN N, fTot G j hN lam t.re t.im (psiG N) (r.out⁻¹ • z) -
    (rY lam (mob γ t).im : ℂ) *
      ∑' r : cosetN N, fTot G j hN lam (mob γ t).re (mob γ t).im (psiG N) (r.out⁻¹ • z)

variable {w : ℕ}

include hN in
/-- The pointwise identity from covariance. -/
lemma alpha_defX (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (γ : SL(2, ℤ)) {E : ℤ} (hE : γ 1 0 = 6 * N * E) {t : ℂ}
    (ht : 0 < t.im) (z : ℍ) :
    alphaF lam γ t * (jN N 0 * ((sqrt (z : ℂ))⁻¹ * (cV' G j lam hN z * d00 hN lam z))) =
      ((chiZ N : ℂ) * e24 (-3)) * defX G j hN lam γ t z := by
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hγt : 0 < (mob γ t).im := mob_im_pos γ ht
  have e1 : (((mob γ t).re : ℝ) : ℂ) + ((mob γ t).im : ℝ) * I = mob γ t := Complex.re_add_im _
  have e2 : ((t.re : ℝ) : ℂ) + (t.im : ℝ) * I = t := Complex.re_add_im _
  have h1 := phiI_decomp G j hN lam one_pos (mob γ t).re hγt z ht2 ht3 htj hjw hk
  have h2 := phiI_decomp G j hN lam one_pos t.re ht z ht2 ht3 htj hjw hk
  rw [e1] at h1
  rw [e2] at h2
  have hcov : phiI G j hN lam (mob γ t) z = lin γ t ^ (2 * lam) * phiI G j hN lam t z := by
    unfold phiI
    rw [kernel_covariant (jN N) (N : ℤ) hNZ _ _ lam (fun a A k hA => jN_inv a A k hA) γ hE ht]
    ring
  rw [h1, h2] at hcov
  unfold alphaF defX rY
  push_cast at hcov ⊢
  linear_combination hcov

include hN in
/-- **The defect is proportional to the obstruction.** -/
theorem alpha_cross (hlam : lam ≠ 0) (hj : j < 24) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1)
    (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hneg : ∀ g, jN N (-g) = (-1) ^ lam * jN N g)
    (γ₁ γ₂ : SL(2, ℤ)) {E₁ E₂ : ℤ} (hE₁ : γ₁ 1 0 = 6 * N * E₁) (hE₂ : γ₂ 1 0 = 6 * N * E₂) {t₁ t₂ : ℂ}
    (ht₁ : 0 < t₁.im) (ht₂ : 0 < t₂.im) :
    alphaF lam γ₂ t₂ * defectT G j lam γ₁ t₁ (N := N) = alphaF lam γ₁ t₁ * defectT G j lam γ₂ t₂ (N := N) := by
  have hχ : ((chiZ N : ℤ) : ℂ) ≠ 0 := by exact_mod_cast chiZ_ne_zero ht2 ht3
  have he := e24_ne_zero (-3)
  have hc0 : (chiZ N : ℂ) * e24 (-3) ≠ 0 := mul_ne_zero hχ he
  have hK : 2 * (-1) ^ lam * (c0 lam : ℂ) ≠ 0 := by
    have h6 : (0 : ℝ) < √6 := Real.sqrt_pos.mpr (by norm_num)
    have hc : (c0 lam : ℂ) ≠ 0 := by
      have : (0 : ℝ) < c0 lam := by
        unfold c0
        positivity
      exact_mod_cast this.ne'
    have hs : ((-1 : ℂ) ^ lam) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs) hc
  have hval : ∀ (ξ : ℝ) {y : ℝ} (_ : 0 < y),
      IntegrableOn (fun z : ℍ => ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z))
        (domainOf (gN N)) ∧
      (rY lam y : ℂ) * ∫ z in domainOf (gN N), ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z) =
        2 * (-1) ^ lam * (c0 lam : ℂ) * lamSum G j (N := N) (jN N) lam ξ y := by
    intro ξ y hy
    obtain ⟨hI, hV⟩ := integrableOn_fold G j hN lam ξ y (hj := hj) hy ht2 ht3 htj hjw hk
    refine ⟨hI, ?_⟩
    have hc := strip_closed G j hN lam ξ y hlam (hj := hj) hNj hy (norm_jN_le N) hneg
    have hψg : (fun g : ℤ => if g = 0 then (0 : ℂ) else jN N (-g)) = psiG N := rfl
    rw [hψg] at hc
    rw [hV, hc]
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hyp := pow_ne_zero lam hyC
    unfold rY
    push_cast
    field_simp
  have hint : ∀ (γ : SL(2, ℤ)) {t : ℂ} (_ : 0 < t.im),
      ∫ z in domainOf (gN N), defX G j hN lam γ t z =
        -(2 * (-1) ^ lam * (c0 lam : ℂ) * defectT G j lam γ t (N := N)) := by
    intro γ t ht
    have hγt : 0 < (mob γ t).im := mob_im_pos γ ht
    obtain ⟨hI1, hV1⟩ := hval t.re ht
    obtain ⟨hI2, hV2⟩ := hval (mob γ t).re hγt
    unfold defX defectT
    rw [integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
      mul_assoc, hV1, hV2]
    ring
  have hpt : ∀ z : ℍ, alphaF lam γ₂ t₂ * defX G j hN lam γ₁ t₁ z =
      alphaF lam γ₁ t₁ * defX G j hN lam γ₂ t₂ z := by
    intro z
    have h1 := alpha_defX G j hN lam ht2 ht3 htj hjw hk γ₁ hE₁ ht₁ z
    have h2 := alpha_defX G j hN lam ht2 ht3 htj hjw hk γ₂ hE₂ ht₂ z
    apply mul_left_cancel₀ hc0
    linear_combination alphaF lam γ₁ t₁ * h2 - alphaF lam γ₂ t₂ * h1
  have hI : alphaF lam γ₂ t₂ * ∫ z in domainOf (gN N), defX G j hN lam γ₁ t₁ z =
      alphaF lam γ₁ t₁ * ∫ z in domainOf (gN N), defX G j hN lam γ₂ t₂ z := by
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint γ₁ ht₁, hint γ₂ ht₂] at hI
  apply mul_left_cancel₀ hK
  linear_combination -hI

end

end RamanujanTau.ThetaLift
