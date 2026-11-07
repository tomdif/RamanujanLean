/-
# The rectangle integral of `1/(z − u)`

`rectInt f x₀ x₁ y₀ y₁` is Mathlib's oriented boundary integral of `f` over the rectangle
`[x₀,x₁] × [y₀,y₁]` (as in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).

* `rectInt_inv_of_mem`: for `u` in the open rectangle, `∮ 1/(z−u) dz = 2πi`.
  Each side is integrated with a branch `log (e (z − u))`, `e ∈ {1, −1, I, −I}`, holomorphic
  along that side; the four corner terms combine by `log (I w) = log w + iπ/2` (`Re w > 0`).
* `rectInt_inv_of_not_mem`: for `u` outside the closed rectangle, `∮ 1/(z−u) dz = 0` (Cauchy).
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set intervalIntegral MeasureTheory
open scoped Real Interval

/-- Oriented boundary integral over the rectangle `[x₀,x₁] × [y₀,y₁]`. -/
noncomputable def rectInt (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f (x + y₀ * I)) - (∫ x : ℝ in x₀..x₁, f (x + y₁ * I)) +
    I • (∫ y : ℝ in y₀..y₁, f (x₁ + y * I)) - I • (∫ y : ℝ in y₀..y₁, f (x₀ + y * I))

/-- Cauchy's theorem in `rectInt` form. -/
theorem rectInt_eq_zero {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (H : DifferentiableOn ℂ f ([[x₀, x₁]] ×ℂ [[y₀, y₁]])) : rectInt f x₀ x₁ y₀ y₁ = 0 := by
  have := integral_boundary_rect_eq_zero_of_differentiableOn f (x₀ + y₀ * I) (x₁ + y₁ * I)
    (by simpa using H)
  simpa [rectInt] using this

lemma log_I_mul {w : ℂ} (hw : 0 < w.re) : log (I * w) = log w + π / 2 * I := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have harg : |arg w| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [log_mul I_ne_zero hw0, log_I]
  · ring
  · rw [arg_I]
    obtain ⟨h1, h2⟩ := abs_lt.mp harg
    constructor <;> linarith [Real.pi_pos]

/-- FTC along an affine segment with the branch `log (e · (z − u))`. -/
lemma integral_inv_affine {c d e u : ℂ} {t₀ t₁ : ℝ} (he : e ≠ 0)
    (h : ∀ t ∈ [[t₀, t₁]], e * (c + t * d - u) ∈ slitPlane) :
    ∫ t : ℝ in t₀..t₁, d / (c + t * d - u) =
      log (e * (c + t₁ * d - u)) - log (e * (c + t₀ * d - u)) := by
  have hne : ∀ t ∈ [[t₀, t₁]], c + t * d - u ≠ 0 := by
    intro t ht h0
    have := slitPlane_ne_zero (h t ht)
    rw [h0, mul_zero] at this
    exact this rfl
  apply integral_eq_sub_of_hasDerivAt
  · intro t ht
    have h1 : HasDerivAt (fun t : ℝ => e * (c + (t : ℂ) * d - u)) (e * d) t := by
      have := ((hasDerivAt_id t).ofReal_comp.mul_const d).const_add c |>.sub_const u |>.const_mul e
      simpa using this
    have h2 := h1.clog_real (h t ht)
    convert h2 using 1
    rw [mul_div_mul_left _ _ he]
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · exact hne

/-- **`∮ 1/(z−u) = 2πi`** for `u` in the open rectangle. -/
theorem rectInt_inv_of_mem {x₀ x₁ y₀ y₁ : ℝ} {u : ℂ} (h0 : x₀ < u.re) (h1 : u.re < x₁)
    (h2 : y₀ < u.im) (h3 : u.im < y₁) :
    rectInt (fun z => 1 / (z - u)) x₀ x₁ y₀ y₁ = 2 * π * I := by
  set A00 : ℂ := x₀ + y₀ * I - u
  set A10 : ℂ := x₁ + y₀ * I - u
  set A11 : ℂ := x₁ + y₁ * I - u
  set A01 : ℂ := x₀ + y₁ * I - u
  -- bottom: branch `log (I (z − u))`
  have hb : ∫ x : ℝ in x₀..x₁, 1 / ((x : ℂ) + y₀ * I - u) = log (I * A10) - log (I * A00) := by
    have := integral_inv_affine (c := y₀ * I) (d := 1) (e := I) (u := u) (t₀ := x₀) (t₁ := x₁)
      I_ne_zero (fun t _ => Or.inl (by simp; linarith))
    convert this using 2
    · funext x; congr 1; ring
    · simp only [A10]; ring_nf
    · simp only [A00]; ring_nf
  -- top: branch `log (−I (z − u))`
  have ht : ∫ x : ℝ in x₀..x₁, 1 / ((x : ℂ) + y₁ * I - u) = log (-I * A11) - log (-I * A01) := by
    have := integral_inv_affine (c := y₁ * I) (d := 1) (e := -I) (u := u) (t₀ := x₀) (t₁ := x₁)
      (neg_ne_zero.mpr I_ne_zero) (fun t _ => Or.inl (by simp; linarith))
    convert this using 2
    · funext x; congr 1; ring
    · simp only [A11]; ring_nf
    · simp only [A01]; ring_nf
  -- right: branch `log (z − u)`
  have hr : I • ∫ y : ℝ in y₀..y₁, 1 / ((x₁ : ℂ) + y * I - u) = log A11 - log A10 := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    have := integral_inv_affine (c := x₁) (d := I) (e := 1) (u := u) (t₀ := y₀) (t₁ := y₁)
      one_ne_zero (fun t _ => Or.inl (by simp; linarith))
    convert this using 2
    · funext y; ring
    · simp only [A11]; ring_nf
    · simp only [A10]; ring_nf
  -- left: branch `log (−(z − u))`
  have hl : I • ∫ y : ℝ in y₀..y₁, 1 / ((x₀ : ℂ) + y * I - u) = log (-A01) - log (-A00) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    have := integral_inv_affine (c := x₀) (d := I) (e := -1) (u := u) (t₀ := y₀) (t₁ := y₁)
      (by norm_num) (fun t _ => Or.inl (by simp; linarith))
    convert this using 2
    · funext y; ring
    · simp only [A01]; ring_nf
    · simp only [A00]; ring_nf
  unfold rectInt
  simp only [] at hb ht hr hl ⊢
  rw [hb, ht, hr, hl]
  -- corner identities
  have c1 : log (I * A10) = log A10 + π / 2 * I := log_I_mul (by simp [A10]; linarith)
  have c2 : log A11 = log (-I * A11) + π / 2 * I := by
    have := log_I_mul (w := -I * A11) (by simp [A11]; linarith)
    rw [← this]; congr 1; rw [← mul_assoc]; simp
  have c3 : log (-I * A01) = log (-A01) + π / 2 * I := by
    have := log_I_mul (w := -A01) (by simp [A01]; linarith)
    rw [← this]; congr 1; ring
  have c4 : log (-A00) = log (I * A00) + π / 2 * I := by
    have := log_I_mul (w := I * A00) (by simp [A00]; linarith)
    rw [← this]; congr 1; rw [← mul_assoc]; simp
  rw [c1, c2, c3, c4]
  ring

/-- **`∮ 1/(z−u) = 0`** for `u` outside the closed rectangle. -/
theorem rectInt_inv_of_not_mem {x₀ x₁ y₀ y₁ : ℝ} {u : ℂ} (hu : u ∉ [[x₀, x₁]] ×ℂ [[y₀, y₁]]) :
    rectInt (fun z => 1 / (z - u)) x₀ x₁ y₀ y₁ = 0 := by
  apply rectInt_eq_zero
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div (differentiableAt_const _) (by fun_prop)
  intro h
  rw [sub_eq_zero] at h
  exact hu (h ▸ hz)

end RamanujanTau.ZeroCountRvM
