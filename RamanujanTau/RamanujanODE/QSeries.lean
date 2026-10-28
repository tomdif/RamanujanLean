import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# Functions on `ℍ` given by an everywhere-convergent q-series

`IsQSeries f c` : `f τ = Σ c n qⁿ` (as a `HasSum`) for every `τ ∈ ℍ`, `q = e^{2πiτ}`.

* `IsQSeries.periodic`, `IsQSeries.isBoundedAtImInfty`, `IsQSeries.analyticAt`,
  `IsQSeries.qExpansion_eq` (`qExpansion 1 f = mk c` when `f` is holomorphic).
* `IsQSeries.D`: term-by-term differentiation, `D f = Σ n c n qⁿ`.
* `isQSeries_E2`: `E₂ = 1 − 24 Σ σ₁(n) qⁿ`.
-/

set_option autoImplicit false

namespace RamanujanODEProof
open UpperHalfPlane hiding I
open Real Complex Filter Function Derivative
open scoped Topology Manifold ArithmeticFunction.sigma

local notation "𝕢" => Periodic.qParam

/-- `f τ = Σ c n qⁿ` on all of `ℍ`. -/
def IsQSeries (f : ℍ → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n => c n • 𝕢 1 τ ^ n) (f τ)

lemma norm_qParam_one (w : ℂ) : ‖𝕢 1 w‖ = Real.exp (-2 * π * w.im) := by
  rw [Periodic.norm_qParam, div_one]

/-- The point `t·i ∈ ℍ`. -/
def ipt (t : ℝ) (ht : 0 < t) : ℍ := ⟨t * I, by simpa using ht⟩

lemma IsQSeries.summable_norm {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) {t : ℝ} (ht : 0 < t) :
    Summable fun n => ‖c n‖ * Real.exp (-2 * π * t) ^ n := by
  have h := summable_norm_iff.mpr (hf (ipt t ht)).summable
  refine h.congr fun n => ?_
  rw [norm_smul, norm_pow, norm_qParam_one]
  simp [ipt]

lemma IsQSeries.norm_term_le {c : ℕ → ℂ} {t : ℝ} {w : ℂ} (hw : t ≤ w.im) (n : ℕ) :
    ‖c n • 𝕢 1 w ^ n‖ ≤ ‖c n‖ * Real.exp (-2 * π * t) ^ n := by
  rw [norm_smul, norm_pow, norm_qParam_one]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) n) (norm_nonneg _)

lemma IsQSeries.periodic {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) :
    Periodic (f ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < im w
  · have hw1 : 0 < im (w + 1) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    refine (hf ⟨w + 1, hw1⟩).unique ?_
    have hq : 𝕢 1 (w + 1) = 𝕢 1 w := by
      simp only [Periodic.qParam, ofReal_one, div_one, mul_add, mul_one]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    simpa [UpperHalfPlane.coe_mk, hq] using hf ⟨w, hw⟩
  · have hw1 : im (w + 1) ≤ 0 := by simpa using not_lt.mp hw
    simp [ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

lemma IsQSeries.isBoundedAtImInfty {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) :
    IsBoundedAtImInfty f := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨∑' n, ‖c n‖ * Real.exp (-2 * π * 1) ^ n, 1, fun z hz => ?_⟩
  exact (hf z).norm_le_of_bounded (hf.summable_norm one_pos).hasSum
    (fun n => IsQSeries.norm_term_le (by simpa using hz) n)

lemma IsQSeries.analyticAt {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) (hhol : MDiff f) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 :=
  analyticAt_cuspFunction_zero one_pos hf.periodic hhol hf.isBoundedAtImInfty

/-- A wrapper type, so that Mathlib's `FunLike`-generic uniqueness lemma applies to plain functions. -/
def WrapFn : Type := ℍ → ℂ

instance : FunLike WrapFn ℍ ℂ := ⟨id, injective_id⟩

lemma IsQSeries.qExpansion_eq {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) (hhol : MDiff f) :
    qExpansion 1 f = PowerSeries.mk c := by
  ext m
  rw [PowerSeries.coeff_mk]
  exact (qExpansion_coeff_unique (F := WrapFn) f one_pos (hf.analyticAt hhol) hf m).symm

lemma hasDerivAt_qParam_pow (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => 𝕢 1 w ^ n) (2 * π * I * n * 𝕢 1 w ^ n) w := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * π * I * w / (1 : ℝ)) (2 * π * I / (1 : ℝ)) w := by
    simpa using (hasDerivAt_id w).const_mul (2 * π * I : ℂ)
  have h2 := (h1.cexp).pow n
  have : (fun w => 𝕢 1 w ^ n) = fun w => cexp (2 * π * I * w / (1 : ℝ)) ^ n := rfl
  rw [this]
  convert h2 using 1
  rcases n with _ | n
  · simp
  · simp only [Periodic.qParam, ofReal_one, div_one, Nat.cast_add, Nat.cast_one,
      add_tsub_cancel_right, pow_succ]
    ring

/-- **Term-by-term differentiation**: `D (Σ c n qⁿ) = Σ n c n qⁿ`. -/
lemma IsQSeries.D {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : IsQSeries f c) :
    IsQSeries (D f) (fun n => n * c n) := by
  intro τ
  set t := τ.im / 2 with ht_def
  have ht : 0 < t := by have := τ.im_pos; positivity
  set U : Set ℂ := {w | t < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by
    show t < (τ : ℂ).im
    have := τ.im_pos; simp only [UpperHalfPlane.coe_im]; linarith
  set F : ℕ → ℂ → ℂ := fun n w => c n • 𝕢 1 w ^ n with hF
  have hderF : ∀ n w, HasDerivAt (F n) (c n * (2 * π * I * n * 𝕢 1 w ^ n)) w := fun n w => by
    simpa [hF, smul_eq_mul] using (hasDerivAt_qParam_pow n w).const_mul (c n)
  have hsum := Complex.hasSum_deriv_of_summable_norm (F := F) (U := U) (z := (τ : ℂ))
    (hf.summable_norm ht) (fun n => fun w _ => (hderF n w).differentiableAt.differentiableWithinAt)
    hUo (fun n w hw => IsQSeries.norm_term_le (le_of_lt hw) n) hτU
  have heq : (fun w : ℂ => ∑' n, F n w) =ᶠ[𝓝 (τ : ℂ)] (f ∘ ofComplex) := by
    filter_upwards [hUo.mem_nhds hτU] with w hw
    have hw0 : 0 < w.im := lt_trans ht hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw0]
    exact (hf ⟨w, hw0⟩).tsum_eq
  rw [heq.deriv_eq] at hsum
  have := hsum.mul_left (2 * π * I)⁻¹
  unfold normalizedDerivOfComplex
  convert this using 1
  funext n
  rw [(hderF n τ).deriv, smul_eq_mul]
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ### `E₂` -/

/-- Coefficients of `E₂ = 1 − 24 Σ σ₁(n) qⁿ`. -/
noncomputable def e2c (n : ℕ) : ℂ := if n = 0 then 1 else -24 * (σ 1 n : ℂ)

lemma summable_sigma_one_mul_pow (z : ℍ) :
    Summable fun n : ℕ ↦ (σ 1 n : ℂ) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n)

lemma isQSeries_E2 : IsQSeries EisensteinSeries.E2 e2c := by
  intro τ
  have hS : Summable fun n : ℕ ↦ (σ 1 (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_one_mul_pow τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul,
    Finset.range_one, Finset.sum_singleton, e2c, pow_zero, mul_one]
  have hval : EisensteinSeries.E2 τ - 1 =
      -24 * ∑' n : ℕ, (σ 1 (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) := by
    rw [EisensteinSeries.E2_eq_tsum_cexp,
      ← tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ 1 n : ℂ) * cexp (2 * π * I * τ) ^ n)]
    ring
  rw [hval]
  convert (hS.mul_left (-24)).hasSum using 1
  · funext n; simp only [Periodic.qParam, ofReal_one, div_one]; ring
  · rw [tsum_mul_left]

end RamanujanODEProof
