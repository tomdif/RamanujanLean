import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Taylor coefficients of sums of entire functions

Termwise differentiation of a dominated sum of entire functions, to any order, and the Hermite
formula for the derivatives of a Gaussian exponential.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Filter Polynomial
open scoped Topology

noncomputable section

variable {ι : Type*}

/-- **Termwise iterated derivatives of a dominated sum of entire functions.** -/
theorem hasSum_iteratedDeriv {F : ι → ℂ → ℂ} {u : ι → ℝ} (hu : Summable u) {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ i, Differentiable ℂ (F i)) (hb : ∀ i σ, σ ∈ U → ‖F i σ‖ ≤ u i)
    (n : ℕ) {σ : ℂ} (hσ : σ ∈ U) :
    HasSum (fun i => iteratedDeriv n (F i) σ) (iteratedDeriv n (fun τ => ∑' i, F i τ) σ) := by
  have hdiff : ∀ (m : ℕ) (i : ι), Differentiable ℂ (iteratedDeriv m (F i)) := fun m i =>
    ((hF i).contDiff (n := ⊤)).differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)
  have key : ∀ m : ℕ, TendstoLocallyUniformlyOn
      (fun (s : Finset ι) τ => ∑ i ∈ s, iteratedDeriv m (F i) τ)
      (iteratedDeriv m (fun τ => ∑' i, F i τ)) atTop U := by
    intro m
    induction m with
    | zero =>
      simp only [iteratedDeriv_zero]
      exact (tendstoUniformlyOn_tsum hu fun i τ hτ => hb i τ hτ).tendstoLocallyUniformlyOn
    | succ m ih =>
      have hd := ih.deriv (Eventually.of_forall fun s =>
        (Differentiable.fun_sum fun i _ => hdiff m i).differentiableOn) hU
      rw [iteratedDeriv_succ]
      refine hd.congr fun s τ hτ => ?_
      simp only [Function.comp, iteratedDeriv_succ]
      rw [deriv_fun_sum fun i _ => (hdiff m i) τ]
  have := (key n).tendsto_at hσ
  exact this

lemma iteratedDeriv_exp_lin (A R : ℂ) (n : ℕ) (σ : ℂ) :
    iteratedDeriv n (fun τ => cexp (A * τ + R)) σ = A ^ n * cexp (A * σ + R) := by
  induction n generalizing σ with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have h : HasDerivAt (fun τ : ℂ => A * τ + R) A σ := by
      simpa using ((hasDerivAt_id σ).const_mul A).add_const R
    rw [(h.cexp.const_mul (A ^ n)).deriv]
    ring

/-- The derivatives of a Gaussian exponential are Hermite polynomials. -/
theorem iteratedDeriv_gauss (A b : ℂ) (hb : b ≠ 0) (n : ℕ) (σ : ℂ) :
    iteratedDeriv n (fun τ => cexp (A * τ - b ^ 2 * τ ^ 2 / 2)) σ =
      b ^ n * aeval ((A - b ^ 2 * σ) / b) (hermite n) * cexp (A * σ - b ^ 2 * σ ^ 2 / 2) := by
  induction n generalizing σ with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h : iteratedDeriv n (fun τ => cexp (A * τ - b ^ 2 * τ ^ 2 / 2)) = fun τ =>
        b ^ n * aeval ((A - b ^ 2 * τ) / b) (hermite n) * cexp (A * τ - b ^ 2 * τ ^ 2 / 2) :=
      funext ih
    rw [h]
    have hu : HasDerivAt (fun τ : ℂ => (A - b ^ 2 * τ) / b) (-b) σ := by
      have := ((hasDerivAt_id σ).const_mul (b ^ 2)).const_sub A |>.div_const b
      convert this using 1
      simp only [mul_one]
      field_simp
    have hP : HasDerivAt (fun τ : ℂ => aeval ((A - b ^ 2 * τ) / b) (hermite n))
        (aeval ((A - b ^ 2 * σ) / b) (derivative (hermite n)) * (-b)) σ := by
      have := (Polynomial.hasDerivAt_aeval (hermite n) ((A - b ^ 2 * σ) / b)).comp σ hu
      simpa using this
    have hE : HasDerivAt (fun τ : ℂ => cexp (A * τ - b ^ 2 * τ ^ 2 / 2))
        (cexp (A * σ - b ^ 2 * σ ^ 2 / 2) * (A - b ^ 2 * σ)) σ := by
      have h1 : HasDerivAt (fun τ : ℂ => A * τ - b ^ 2 * τ ^ 2 / 2) (A - b ^ 2 * σ) σ := by
        have h2 := ((hasDerivAt_id σ).const_mul A).sub
          (((hasDerivAt_id σ).pow 2).const_mul (b ^ 2) |>.div_const 2)
        convert h2 using 1
        simp
        ring
      exact h1.cexp
    have hD : HasDerivAt (fun τ : ℂ => b ^ n * aeval ((A - b ^ 2 * τ) / b) (hermite n) *
        cexp (A * τ - b ^ 2 * τ ^ 2 / 2)) _ σ := (hP.const_mul (b ^ n)).mul hE
    rw [hD.deriv, hermite_succ]
    simp only [map_sub, map_mul, aeval_X]
    field_simp
    ring

end

end RamanujanTau.ThetaLift
