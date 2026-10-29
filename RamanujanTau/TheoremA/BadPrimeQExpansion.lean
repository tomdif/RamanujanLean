import RamanujanTau.TheoremA.BadPrimeForms
import RamanujanTau.TheoremA.Series
import RamanujanTau.HeckeQExp

/-!
# The actual bad-prime operator extracts q-expansion coefficients

This connects the analytic operator on `CuspForm (Γ₀(N)) k` to the
Boylan–Webb formal-series operator used in the ordinarity reduction.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.BadPrime
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Finset Complex
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

variable {p N : ℕ} [hp : Fact p.Prime] {k : ℤ}

lemma realRep_det (j : ZMod p) : (realRep p j).det.val = (p : ℝ) := by
  change (realRep p j).val.det = _
  rw [realRep_val]
  simp [representative, Matrix.det_fin_two]

lemma realRep_denom (j : ZMod p) (z : ℂ) : denom (realRep p j) z = (p : ℂ) := by
  simp [denom, realRep, rationalRep, representative]

lemma realRep_smul (j : ZMod p) (z : ℍ) :
    realRep p j • z = ofComplex (((z : ℂ) + j.val) / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have him := RamanujanTau.Hecke.im_div_nat (j := j.val) z.im_pos hp.out.pos
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [realRep_det]; exact hpR), ofComplex_apply_of_im_pos him]
  rw [realRep_denom]
  simp [num, realRep, rationalRep, representative, -ZMod.natCast_val]

/-- The normalization agrees with the usual averaged translates, in every weight. -/
lemma realRep_slash (j : ZMod p) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] realRep p j) z = (p : ℂ)⁻¹ * f (ofComplex (((z : ℂ) + j.val) / p)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [slash_apply, realRep_denom, realRep_smul]
  simp only [σ, realRep_det, if_pos hpR, ContinuousAlgEquiv.refl_apply,
    abs_of_pos hpR, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hpC]
  have he : k - 1 + -k = (-1 : ℤ) := by ring
  rw [he, _root_.zpow_neg_one, mul_comm]

lemma sum_zmod_val (F : ℕ → ℂ) : ∑ j : ZMod p, F j.val = ∑ j ∈ range p, F j := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv (ZMod.finEquiv p).symm _ _ ?_
  intro j
  cases p with
  | zero => exact (hp.out.ne_zero rfl).elim
  | succ n => rfl

theorem cuspU_eq_average [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    cuspU hN f z = (p : ℂ)⁻¹ * ∑ j ∈ range p, f (ofComplex (((z : ℂ) + j) / p)) := by
  simp only [cuspU_apply, slashU, Finset.sum_apply, realRep_slash]
  rw [← mul_sum, sum_zmod_val (fun j => f (ofComplex (((z : ℂ) + j) / p)))]

lemma one_period : (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp [strictPeriods_Gamma0]

lemma hasSum_cusp_Gamma0 [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 w ^ n) (f (ofComplex w)) := by
  have h := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_period)
    (ModularFormClass.holo f) (CuspFormClass.zero_at_infty f).isBoundedAtImInfty (ofComplex w)
  rw [ofComplex_apply_of_im_pos hw] at h ⊢
  simpa [smul_eq_mul] using h

/-- Fourier summation for the actual operator; no modularity or truncation input is assumed. -/
theorem hasSum_cuspU [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    HasSum (fun m => (qExpansion 1 f).coeff (p * m) * 𝕢 1 z ^ m) (cuspU hN f z) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h0 := hasSum_sum (s := range p) fun j _ => hasSum_cusp_Gamma0 f
    (RamanujanTau.Hecke.im_div_nat (j := j) z.im_pos hp.out.pos)
  have he : ∀ n, ∑ j ∈ range p, (qExpansion 1 f).coeff n * 𝕢 1 (((z : ℂ) + j) / p) ^ n =
      (qExpansion 1 f).coeff n * 𝕢 1 ((z : ℂ) / p) ^ n * (if p ∣ n then (p : ℂ) else 0) := by
    intro n
    simp_rw [RamanujanTau.Hecke.qP_shift, mul_pow, ← mul_sum, RamanujanTau.Hecke.root_sum]
    ring
  simp_rw [he] at h0
  rw [← RamanujanTau.Hecke.hasSum_mul_reindex p (fun n hn => by simp [hn])] at h0
  have hpow : ∀ m, 𝕢 1 ((z : ℂ) / p) ^ (p * m) = 𝕢 1 z ^ m := by
    intro m
    rw [pow_mul, ← RamanujanTau.Hecke.qP_mul, mul_div_cancel₀ _ hpC]
  simp_rw [hpow, if_pos (dvd_mul_right p _)] at h0
  rw [cuspU_eq_average]
  convert h0.mul_left (p : ℂ)⁻¹ using 1
  funext m
  field_simp

/-- **The analytic bad-prime Hecke operator is coefficient extraction.** -/
theorem qExpansion_cuspU [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (cuspU hN f) = BoylanWebb.U p (qExpansion 1 f) := by
  ext m
  rw [BoylanWebb.coeff_U]
  exact (ModularFormClass.qExpansion_coeff_unique (f := cuspU hN f)
    (c := fun m => (qExpansion 1 f).coeff (p * m)) one_pos one_period
    (fun z => by simpa [smul_eq_mul] using hasSum_cuspU hN f z) m).symm

/-- The bad-prime operator as a complex-linear endomorphism of the actual cusp space. -/
noncomputable def cuspULinear [NeZero N] (hN : p ∣ N) :
    Module.End ℂ (CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) where
  toFun := cuspU hN
  map_add' f g := by
    ext z
    change cuspU hN (f + g) z = cuspU hN f z + cuspU hN g z
    simp only [cuspU_eq_average, CuspForm.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext z
    change cuspU hN (c • f) z = c • cuspU hN f z
    rw [cuspU_eq_average, cuspU_eq_average]
    simp [← Finset.mul_sum, mul_left_comm]

@[simp] theorem cuspULinear_apply [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspULinear hN f = cuspU hN f := rfl

/-- q-expansion is a linear map on the actual cusp space. -/
noncomputable def cuspExpansionLinear (N : ℕ) (k : ℤ) :
    CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 f
  map_add' f g := by
    exact ModularFormClass.qExpansion_add one_pos one_period f g
  map_smul' c f := by
    exact ModularFormClass.qExpansion_smul one_pos one_period c f

/-- The analytic and formal operators intertwine without a missing identification hypothesis. -/
theorem cuspU_intertwines [NeZero N] (hN : p ∣ N) :
    (cuspExpansionLinear N k).comp (cuspULinear hN) =
      (uOperator p).comp (cuspExpansionLinear N k) := by
  ext f n
  exact congrArg (PowerSeries.coeff n) (qExpansion_cuspU hN f)

/-- Equality of the full q-expansions detects equality of actual cusp forms. -/
theorem cuspExpansionLinear_injective [NeZero N] :
    Function.Injective (cuspExpansionLinear N k) := by
  intro f g hfg
  ext z
  have hf := hasSum_cusp_Gamma0 f z.im_pos
  have hg := hasSum_cusp_Gamma0 g z.im_pos
  change qExpansion 1 f = qExpansion 1 g at hfg
  rw [hfg] at hf
  simpa only [ofComplex_apply] using hf.unique hg

/-- The actual operators at primes dividing the level commute. -/
theorem cuspU_commute {q : ℕ} [Fact q.Prime] [NeZero N]
    (hpN : p ∣ N) (hqN : q ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspU hpN (cuspU hqN f) = cuspU hqN (cuspU hpN f) := by
  apply cuspExpansionLinear_injective
  change qExpansion 1 _ = qExpansion 1 _
  simp only [qExpansion_cuspU]
  ext n
  simp only [BoylanWebb.coeff_U]
  rw [Nat.mul_left_comm q p n]

end RamanujanTau.TheoremA.BadPrime
