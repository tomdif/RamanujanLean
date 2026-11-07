/-
# Hecke's theorem for Ramanujan's L-function

`f(t) = Δ(it)` (`t > 0`) satisfies `f(1/t) = t¹² f(t)` (from `Δ(−1/z) = z¹²Δ(z)`, `i¹² = 1`) and
decays exponentially at `∞`; hence `(f, f)` is a Mathlib `StrongFEPair` of weight `12`, root
number `1`.  Its Mellin transform

    Λ(s) = ∫₀^∞ Δ(it) t^{s−1} dt = (2π)^{−s} Γ(s) L(Δ, s)        (Re s > 7)

is entire, bounded on vertical strips, and `Λ(12 − s) = Λ(s)`.
-/
import RamanujanTau.TauLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

set_option autoImplicit false

namespace RamanujanTau.HeckeL

open Complex ModularForm Filter Asymptotics Set MeasureTheory LSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

/-- The discriminant as a function on `ℍ`. -/
noncomputable abbrev Δf : ℍ → ℂ := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)

/-- `f(t) = Δ(it)` (junk for `t ≤ 0`). -/
noncomputable def heckeF (t : ℝ) : ℂ := (Δf ∘ ofComplex) ((t : ℂ) * I)

/-- The point `it` of `ℍ`. -/
def pt {t : ℝ} (ht : 0 < t) : ℍ := ⟨(t : ℂ) * I, by simpa using ht⟩

lemma pt_coe {t : ℝ} (ht : 0 < t) : ((pt ht : ℍ) : ℂ) = (t : ℂ) * I := rfl

lemma pt_im {t : ℝ} (ht : 0 < t) : (pt ht).im = t := by
  show ((t : ℂ) * I).im = t
  simp

lemma heckeF_eq {t : ℝ} (ht : 0 < t) : heckeF t = Δf (pt ht) := by
  unfold heckeF
  simp only [Function.comp_apply]
  congr 1
  rw [ofComplex_apply_of_im_pos (by simpa using ht)]
  rfl

lemma continuousOn_heckeF : ContinuousOn heckeF (Ioi 0) := by
  have hd := UpperHalfPlane.mdifferentiable_iff.mp
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) * I) (Ioi 0) :=
    (continuous_ofReal.mul continuous_const).continuousOn
  exact hd.continuousOn.comp hc fun t ht => by simpa using ht

lemma locallyIntegrableOn_heckeF : LocallyIntegrableOn heckeF (Ioi 0) :=
  continuousOn_heckeF.locallyIntegrableOn measurableSet_Ioi

/-- `S • (it) = i/t`. -/
lemma S_smul_pt {t : ℝ} (ht : 0 < t) : ModularGroup.S • pt ht = pt (one_div_pos.mpr ht) := by
  apply UpperHalfPlane.ext
  rw [modular_S_smul]
  show (-((t : ℂ) * I))⁻¹ = ((1 / t : ℝ) : ℂ) * I
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp
  rw [I_sq]

/-- **Modularity on the imaginary axis**: `Δ(i/t) = t¹² Δ(it)`. -/
lemma heckeF_inv {t : ℝ} (ht : 0 < t) : heckeF (1 / t) = (t : ℂ) ^ 12 * heckeF t := by
  have h := congrFun discriminant_S_invariant (pt ht)
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  rw [heckeF_eq (one_div_pos.mpr ht), heckeF_eq ht, ← S_smul_pt ht]
  show discriminant (ModularGroup.S • pt ht) = (t : ℂ) ^ 12 * discriminant (pt ht)
  rw [← h, pt_coe]
  have hz : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') I_ne_zero
  have hI : ((t : ℂ) * I) ^ 12 = (t : ℂ) ^ 12 := by
    rw [mul_pow, show (12 : ℕ) = 4 * 3 by rfl, pow_mul I, I_pow_four]; simp
  rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast, hI]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

/-- Exponential decay: `‖Δ(it)‖ ≤ C e^{−2πt}` eventually. -/
lemma heckeF_isBigO_exp : heckeF =O[atTop] fun t => Real.exp (-(2 * π) * t) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (max A 1)] with t htA
  have ht : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans htA)
  have hb := hA (pt ht) (by rw [pt_im]; exact (le_max_left _ _).trans htA)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pt_im,
    div_one] at hb
  rw [heckeF_eq ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  convert hb using 3; ring

lemma heckeF_top (r : ℝ) : heckeF =O[atTop] (· ^ r) :=
  heckeF_isBigO_exp.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- **The strong functional-equation pair** `(Δ(it), Δ(it))`, weight `12`, root number `1`. -/
noncomputable def heckePair : StrongFEPair ℂ where
  f := heckeF
  g := heckeF
  k := 12
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_heckeF
  hg_int := locallyIntegrableOn_heckeF
  hk := by norm_num
  hε := one_ne_zero
  h_feq := fun x hx => by
    rw [heckeF_inv hx, one_mul, smul_eq_mul,
      show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    push_cast; rfl
  hf_top := fun r => by simpa using heckeF_top r
  hg_top := fun r => by simpa using heckeF_top r
  hf₀ := rfl
  hg₀ := rfl

/-- **Hecke's completed L-function** `Λ(s) = ∫₀^∞ Δ(it) t^{s−1} dt`. -/
noncomputable def heckeLambda : ℂ → ℂ := heckePair.Λ

lemma heckeLambda_eq_mellin : heckeLambda = mellin heckeF := rfl

/-- **`Λ` is entire.** -/
theorem heckeLambda_entire : Differentiable ℂ heckeLambda := heckePair.differentiable_Λ

/-- **Hecke's functional equation** `Λ(12 − s) = Λ(s)`. -/
theorem heckeLambda_functional_equation (s : ℂ) : heckeLambda (12 - s) = heckeLambda s := by
  have h := heckePair.functional_equation s
  have hk : ((heckePair.k : ℝ) : ℂ) = 12 := by simp [heckePair]
  rw [hk] at h
  rw [heckeLambda, h]
  simp [heckePair, StrongFEPair.symm, StrongFEPair.Λ, WeakFEPair.symm]

/-! ## The Mellin transform is the Dirichlet series -/

lemma tauC_zero : tauC 0 = 0 := by simp [tauC, tau_zero]

/-- `Δ(it) = ∑ τ(n) e^{−2πnt}`. -/
lemma hasSum_heckeF {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => tauC n * (Real.exp (-(2 * π * n) * t) : ℂ)) (heckeF t) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL
  have h := hasSum_qExpansion one_pos hper
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
    (ModularFormClass.bdd_at_infty (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) (pt ht)
  rw [heckeF_eq ht]
  refine h.congr_fun fun n => ?_
  have hc : (qExpansion 1 CuspForm.discriminant).coeff n = tauC n :=
    heckeData.coeff_discriminant n
  rw [hc, smul_eq_mul]
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

/-- **The Mellin transform of `Δ(it)`**: `∫₀^∞ Δ(it) t^{s−1} dt = (2π)^{−s}Γ(s)L(Δ,s)`, `Re s > 7`. -/
theorem mellin_heckeF {s : ℂ} (hs : 7 < s.re) :
    mellin heckeF s = (2 * π : ℂ) ^ (-s) * Gamma s * LSeries tauC s := by
  have hs0 : 0 < s.re := by linarith
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hp : ∀ n : ℕ, tauC n = 0 ∨ 0 < 2 * π * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl tauC_zero
    · exact Or.inr (by positivity)
  have hsum : Summable fun n : ℕ => ‖tauC n‖ / (2 * π * n) ^ s.re := by
    have hL := (LSeriesSummable_tau hs).norm
    refine (hL.mul_left ((2 * π) ^ (-s.re))).congr fun n => ?_
    rw [norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tauC_zero]
    · rw [if_neg hn.ne', Real.mul_rpow h2π.le (Nat.cast_nonneg n), Real.rpow_neg h2π.le]
      field_simp
  have H := hasSum_mellin hp hs0 (fun t ht => hasSum_heckeF ht) hsum
  have H2 : HasSum (fun n => Gamma s * tauC n / ((2 * π * n : ℝ) : ℂ) ^ s)
      ((2 * π : ℂ) ^ (-s) * Gamma s * LSeries tauC s) := by
    have hL := (LSeriesSummable_tau hs).LSeriesHasSum.mul_left ((2 * π : ℂ) ^ (-s) * Gamma s)
    refine hL.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tauC_zero]
    · rw [term_of_ne_zero hn.ne', Complex.ofReal_mul,
        mul_cpow_ofReal_nonneg h2π.le (Nat.cast_nonneg n), cpow_neg]
      push_cast
      ring
  exact H.unique H2

/-- **`Λ(s) = (2π)^{−s}Γ(s)L(Δ,s)`** for `Re s > 7`. -/
theorem heckeLambda_eq {s : ℂ} (hs : 7 < s.re) :
    heckeLambda s = (2 * π : ℂ) ^ (-s) * Gamma s * LSeries tauC s :=
  mellin_heckeF hs

/-- `Λ` is bounded on every vertical strip. -/
theorem heckeLambda_bdd_strip (a b : ℝ) :
    ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖heckeLambda s‖ ≤ L := by
  set f := heckeF
  have hconv : ∀ s : ℂ, MellinConvergent f s := fun s => (heckePair.hasMellin s).1
  set L := (∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
    ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ with hL
  refine ⟨L, fun s h1 h2 => ?_⟩
  rw [heckeLambda_eq_mellin, mellin]
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

end RamanujanTau.HeckeL
