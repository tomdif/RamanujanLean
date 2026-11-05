/-
# Hecke's theorem for an arbitrary level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `k ≥ 1`, put `F(t) = f(it)` (`t > 0`). From `f(−1/z) = z^k f(z)` at
`z = it` we get `F(1/t) = i^k t^k F(t)`, and `F` decays exponentially at `∞`; hence `(F, F)` is a
Mathlib `StrongFEPair` of weight `k` and root number `i^k`. Its Mellin transform

    Λ(f,s) = ∫₀^∞ f(it) t^{s−1} dt = (2π)^{−s} Γ(s) L(f, s)      (Re s > (k+1)/2)

is entire, bounded on vertical strips, and `Λ(f, k − s) = i^k Λ(f, s)`.
(For odd `k` the space is `0`, so only even `k` carry content.)

Generalizes `HeckeL/Basic.lean` and `HeckeL/Main.lean` (`f = Δ`); the Mellin–Dirichlet identity
now holds on the full half-plane `Re s > (k+1)/2` thanks to `LSeriesSummable_coef`.
-/
import RamanujanTau.HeckeConvexGeneral.Summable
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

set_option autoImplicit false

namespace RamanujanTau.HeckeConvexGeneral

open Complex ModularForm Filter Asymptotics Set MeasureTheory LSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℕ}

/-- `F(t) = f(it)` (junk for `t ≤ 0`). -/
noncomputable def heckeF (f : CuspForm 𝒮ℒ (k : ℤ)) (t : ℝ) : ℂ := (f ∘ ofComplex) ((t : ℂ) * I)

/-- The point `it` of `ℍ`. -/
def pt {t : ℝ} (ht : 0 < t) : ℍ := ⟨(t : ℂ) * I, by simpa using ht⟩

lemma pt_coe {t : ℝ} (ht : 0 < t) : ((pt ht : ℍ) : ℂ) = (t : ℂ) * I := rfl

lemma pt_im {t : ℝ} (ht : 0 < t) : (pt ht).im = t := by
  show ((t : ℂ) * I).im = t
  simp

lemma heckeF_eq (f : CuspForm 𝒮ℒ (k : ℤ)) {t : ℝ} (ht : 0 < t) : heckeF f t = f (pt ht) := by
  unfold heckeF
  simp only [Function.comp_apply]
  congr 1
  rw [ofComplex_apply_of_im_pos (by simpa using ht)]
  rfl

lemma continuousOn_heckeF (f : CuspForm 𝒮ℒ (k : ℤ)) : ContinuousOn (heckeF f) (Ioi 0) := by
  have hd := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) * I) (Ioi 0) :=
    (continuous_ofReal.mul continuous_const).continuousOn
  exact hd.continuousOn.comp hc fun t ht => by simpa using ht

lemma locallyIntegrableOn_heckeF (f : CuspForm 𝒮ℒ (k : ℤ)) :
    LocallyIntegrableOn (heckeF f) (Ioi 0) :=
  (continuousOn_heckeF f).locallyIntegrableOn measurableSet_Ioi

/-- `S • (it) = i/t`. -/
lemma S_smul_pt {t : ℝ} (ht : 0 < t) : ModularGroup.S • pt ht = pt (one_div_pos.mpr ht) := by
  apply UpperHalfPlane.ext
  rw [modular_S_smul]
  show (-((t : ℂ) * I))⁻¹ = ((1 / t : ℝ) : ℂ) * I
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp
  rw [I_sq]

/-- **Modularity on the imaginary axis**: `f(i/t) = i^k t^k f(it)`. -/
lemma heckeF_inv (f : CuspForm 𝒮ℒ (k : ℤ)) {t : ℝ} (ht : 0 < t) :
    heckeF f (1 / t) = (I ^ k * (t : ℂ) ^ k) * heckeF f t := by
  have h := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩) (pt ht)
  rw [heckeF_eq f (one_div_pos.mpr ht), heckeF_eq f ht, ← S_smul_pt ht]
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) • pt ht = ModularGroup.S • pt ht :=
    rfl
  rw [hs] at h
  rw [h]
  congr 1
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) (pt ht) = (t : ℂ) * I := by
    simp [denom, ModularGroup.S, pt_coe]
  rw [hd, zpow_natCast, mul_pow, mul_comm]

/-- Exponential decay: `‖f(it)‖ ≤ C e^{−2πt}` eventually. -/
lemma heckeF_isBigO_exp (f : CuspForm 𝒮ℒ (k : ℤ)) :
    heckeF f =O[atTop] fun t => Real.exp (-(2 * π) * t) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := (k : ℤ)) f one_pos
    one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (max A 1)] with t htA
  have ht : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans htA)
  have hb := hA (pt ht) (by rw [pt_im]; exact (le_max_left _ _).trans htA)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pt_im,
    div_one] at hb
  rw [heckeF_eq f ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  convert hb using 3; ring

lemma heckeF_top (f : CuspForm 𝒮ℒ (k : ℤ)) (r : ℝ) : heckeF f =O[atTop] (· ^ r) :=
  (heckeF_isBigO_exp f).trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- **The strong functional-equation pair** `(f(it), f(it))`, weight `k`, root number `i^k`. -/
noncomputable def heckePair (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : StrongFEPair ℂ where
  f := heckeF f
  g := heckeF f
  k := k
  ε := I ^ k
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_heckeF f
  hg_int := locallyIntegrableOn_heckeF f
  hk := by exact_mod_cast hk
  hε := pow_ne_zero _ I_ne_zero
  h_feq := fun x hx => by
    rw [heckeF_inv f hx, smul_eq_mul, Real.rpow_natCast]
    push_cast; ring
  hf_top := fun r => by simpa using heckeF_top f r
  hg_top := fun r => by simpa using heckeF_top f r
  hf₀ := rfl
  hg₀ := rfl

/-- **Hecke's completed L-function** `Λ(f,s) = ∫₀^∞ f(it) t^{s−1} dt`. -/
noncomputable def heckeLambda (f : CuspForm 𝒮ℒ (k : ℤ)) : ℂ → ℂ := mellin (heckeF f)

lemma heckeLambda_eq_pair (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    heckeLambda f = (heckePair f hk).Λ := rfl

/-- **`Λ(f,·)` is entire.** -/
theorem heckeLambda_entire (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Differentiable ℂ (heckeLambda f) :=
  (heckePair f hk).differentiable_Λ

/-- **Hecke's functional equation** `Λ(f, k − s) = i^k Λ(f, s)`. -/
theorem heckeLambda_functional_equation (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (s : ℂ) :
    heckeLambda f (k - s) = I ^ k * heckeLambda f s := by
  have h := (heckePair f hk).functional_equation s
  have hk' : (((heckePair f hk).k : ℝ) : ℂ) = k := by simp [heckePair]
  rw [hk'] at h
  rw [heckeLambda_eq_pair f hk, h]
  simp [heckePair, StrongFEPair.symm, StrongFEPair.Λ, WeakFEPair.symm]

/-! ## The Mellin transform is the Dirichlet series -/

/-- `f(it) = ∑ a(n) e^{−2πnt}`. -/
lemma hasSum_heckeF (f : CuspForm 𝒮ℒ (k : ℤ)) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => coef f n * (Real.exp (-(2 * π * n) * t) : ℂ)) (heckeF f t) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have h := hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (pt ht)
  rw [heckeF_eq f ht]
  refine h.congr_fun fun n => ?_
  rw [smul_eq_mul]
  congr 1
  have hq : 𝕢 1 ((pt ht : ℍ) : ℂ) = ((Real.exp (-(2 * π) * t) : ℝ) : ℂ) := by
    unfold Function.Periodic.qParam
    rw [Complex.ofReal_exp, pt_coe]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]; ring
  rw [hq, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2; ring

/-- **Hecke**: `∫₀^∞ f(it) t^{s−1} dt = (2π)^{−s}Γ(s)L(f,s)` for `Re s > (k+1)/2`. -/
theorem heckeLambda_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ}
    (hs : ((k : ℝ) + 1) / 2 < s.re) :
    heckeLambda f s = (2 * π : ℂ) ^ (-s) * Gamma s * LSeries (coef f) s := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hp : ∀ n : ℕ, coef f n = 0 ∨ 0 < 2 * π * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (coef_zero f)
    · exact Or.inr (by positivity)
  have hsum : Summable fun n : ℕ => ‖coef f n‖ / (2 * π * n) ^ s.re := by
    have hL := (LSeriesSummable_coef f hk hs).norm
    refine (hL.mul_left ((2 * π) ^ (-s.re))).congr fun n => ?_
    rw [norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coef_zero]
    · rw [if_neg hn.ne', Real.mul_rpow h2π.le (Nat.cast_nonneg n), Real.rpow_neg h2π.le]
      field_simp
  have H := hasSum_mellin hp hs0 (fun t ht => hasSum_heckeF f ht) hsum
  have H2 : HasSum (fun n => Gamma s * coef f n / ((2 * π * n : ℝ) : ℂ) ^ s)
      ((2 * π : ℂ) ^ (-s) * Gamma s * LSeries (coef f) s) := by
    have hL := (LSeriesSummable_coef f hk hs).LSeriesHasSum.mul_left
      ((2 * π : ℂ) ^ (-s) * Gamma s)
    refine hL.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coef_zero]
    · rw [term_of_ne_zero hn.ne', Complex.ofReal_mul,
        mul_cpow_ofReal_nonneg h2π.le (Nat.cast_nonneg n), cpow_neg]
      push_cast
      ring
  exact H.unique H2

/-- `Λ(f,·)` is bounded on every vertical strip. -/
theorem heckeLambda_bdd_strip (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (a b : ℝ) :
    ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖heckeLambda f s‖ ≤ L := by
  set F := heckeF f
  have hconv : ∀ s : ℂ, MellinConvergent F s := fun s => ((heckePair f hk).hasMellin s).1
  set L := (∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • F t‖) +
    ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • F t‖ with hL
  refine ⟨L, fun s h1 h2 => ?_⟩
  rw [heckeLambda, mellin]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hia := (hconv a).norm
  have hib := (hconv b).norm
  rw [hL, ← integral_add hia hib]
  refine setIntegral_mono_on (hconv s).norm (hia.add hib) measurableSet_Ioi fun t ht => ?_
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_or_gt t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h (show a - 1 ≤ s.re - 1 by linarith)
    linarith [Real.rpow_pos_of_pos ht (b - 1)]
  · have := Real.rpow_le_rpow_of_exponent_le h.le (show s.re - 1 ≤ b - 1 by linarith)
    linarith [Real.rpow_pos_of_pos ht (a - 1)]

/-! ## The entire continuation `L(f,s)` -/

/-- The entire continuation of `L(f,s)`: `(2π)^s Γ(s)⁻¹ Λ(f,s)`. -/
noncomputable def fL (f : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : ℂ :=
  (2 * π : ℂ) ^ s * (Gamma s)⁻¹ * heckeLambda f s

lemma two_pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
  have : (0:ℝ) < 2 * π := by positivity
  exact_mod_cast this.ne'

lemma two_pi_cpow_ne_zero (s : ℂ) : (2 * π : ℂ) ^ s ≠ 0 :=
  (cpow_eq_zero_iff _ _).not.mpr fun h => two_pi_ne_zero h.1

/-- **`L(f,s)` is entire.** -/
theorem fL_entire (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : Differentiable ℂ (fL f) :=
  ((differentiable_id.const_cpow (Or.inl two_pi_ne_zero)).mul
    differentiable_one_div_Gamma).mul (heckeLambda_entire f hk)

/-- **`fL f` continues the Dirichlet series** `∑ a_f(n) n^{−s}` from `Re s > (k+1)/2`. -/
theorem fL_eq_LSeries (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ}
    (hs : ((k : ℝ) + 1) / 2 < s.re) : fL f s = LSeries (coef f) s := by
  rw [fL, heckeLambda_eq f hk hs, cpow_neg]
  have hG := Gamma_ne_zero_of_re_pos (show 0 < s.re from lt_of_le_of_lt (by positivity) hs)
  have hc := two_pi_cpow_ne_zero s
  field_simp

/-- `Λ(f,s) = (2π)^{−s} Γ(s) L(f,s)` away from the poles of `Γ`. -/
theorem heckeLambda_eq_fL (f : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    heckeLambda f s = (2 * π : ℂ) ^ (-s) * Gamma s * fL f s := by
  rw [fL, cpow_neg]
  have hG := Gamma_ne_zero hs
  have hc := two_pi_cpow_ne_zero s
  field_simp

/-- **Functional equation for `L(f,s)`** (away from the poles of both Gamma factors):
`(2π)^{−(k−s)} Γ(k−s) L(f,k−s) = i^k (2π)^{−s} Γ(s) L(f,s)`. -/
theorem fL_functional_equation (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs' : ∀ n : ℕ, (k : ℂ) - s ≠ -n) :
    (2 * π : ℂ) ^ (-((k : ℂ) - s)) * Gamma ((k : ℂ) - s) * fL f ((k : ℂ) - s) =
      I ^ k * ((2 * π : ℂ) ^ (-s) * Gamma s * fL f s) := by
  rw [← heckeLambda_eq_fL f hs, ← heckeLambda_eq_fL f hs', heckeLambda_functional_equation f hk]

/-- If `f = 0` then `L(f,·) = 0` (used for the weights `k < 12`, where `S_k = 0`). -/
lemma fL_of_eq_zero {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : f = 0) (s : ℂ) : fL f s = 0 := by
  subst hf
  have h0 : heckeF (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
    funext t; simp [heckeF]
  simp [fL, heckeLambda, h0, mellin]

end RamanujanTau.HeckeConvexGeneral
