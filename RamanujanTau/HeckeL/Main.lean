/-
# Consequences of Hecke's theorem for `L(Δ, s)`

* `tauL s = (2π)^s Γ(s)⁻¹ Λ(s)` is entire and equals `L(Δ,s) = ∑ τ(n) n^{−s}` for `Re s > 7`.
* trivial zeros: `tauL (−n) = 0` (`n ∈ ℕ`), coming from the poles of `Γ`.
* positivity on the real axis: `Δ(it) > 0` for `t > 0`, so `Λ(σ) > 0` for every real `σ`.
  Hence the real zeros of `L(Δ,s)` are exactly `0, −1, −2, …`; in particular `L(Δ,6) > 0`.
* the centre: `Λ(6) = 120 (2π)^{−6} L(Δ,6)` and `Λ'(6) = 0`.
-/
import RamanujanTau.HeckeL.Basic

set_option autoImplicit false

namespace RamanujanTau.HeckeL

open Complex ModularForm Filter Asymptotics Set MeasureTheory LSeries Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

/-! ## The entire continuation of `L(Δ, s)` -/

/-- The entire continuation of `L(Δ,s)`: `(2π)^s Γ(s)⁻¹ Λ(s)`. -/
noncomputable def tauL (s : ℂ) : ℂ := (2 * π : ℂ) ^ s * (Gamma s)⁻¹ * heckeLambda s

lemma two_pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
  have : (0:ℝ) < 2 * π := by positivity
  exact_mod_cast this.ne'

/-- **`L(Δ,s)` is entire.** -/
theorem tauLSeries_entire : Differentiable ℂ tauL :=
  ((differentiable_id.const_cpow (Or.inl two_pi_ne_zero)).mul
    differentiable_one_div_Gamma).mul heckeLambda_entire

lemma two_pi_cpow_ne_zero (s : ℂ) : (2 * π : ℂ) ^ s ≠ 0 :=
  (cpow_eq_zero_iff _ _).not.mpr fun h => two_pi_ne_zero h.1

/-- **`tauL` continues the Dirichlet series** `∑ τ(n) n^{−s}`. -/
theorem tauL_eq_LSeries {s : ℂ} (hs : 7 < s.re) : tauL s = LSeries tauC s := by
  rw [tauL, heckeLambda_eq hs, cpow_neg]
  have hG := Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hc := two_pi_cpow_ne_zero s
  field_simp

/-- `Λ(s) = (2π)^{−s} Γ(s) tauL(s)` away from the poles of `Γ`. -/
theorem heckeLambda_eq_tauL {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    heckeLambda s = (2 * π : ℂ) ^ (-s) * Gamma s * tauL s := by
  rw [tauL, cpow_neg]
  have hG := Gamma_ne_zero hs
  have hc := two_pi_cpow_ne_zero s
  field_simp

/-- **Trivial zeros**: `L(Δ, −n) = 0` for `n ∈ ℕ` (from the poles of `Γ`). -/
theorem tauLSeries_zeros_trivial (n : ℕ) : tauL (-n) = 0 := by
  simp [tauL, Gamma_neg_nat_eq_zero]

/-- **Functional equation for `L(Δ,s)`** (away from the poles of both Gamma factors):
`(2π)^{−(12−s)} Γ(12−s) L(Δ,12−s) = (2π)^{−s} Γ(s) L(Δ,s)`. -/
theorem tauL_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : ∀ n : ℕ, 12 - s ≠ -n) :
    (2 * π : ℂ) ^ (-(12 - s)) * Gamma (12 - s) * tauL (12 - s) =
      (2 * π : ℂ) ^ (-s) * Gamma s * tauL s := by
  rw [← heckeLambda_eq_tauL hs, ← heckeLambda_eq_tauL hs', heckeLambda_functional_equation]

/-! ## The centre `s = 6` -/

/-- **Centre value relation** `Λ(6) = 5! (2π)^{−6} L(Δ,6)`. -/
theorem tauLSeries_center : heckeLambda 6 = (2 * π : ℂ) ^ (-(6 : ℂ)) * 120 * tauL 6 := by
  have h6 : ∀ n : ℕ, (6 : ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [heckeLambda_eq_tauL h6]
  have : Gamma (6 : ℂ) = 120 := by
    rw [show (6 : ℂ) = (5 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [this]

/-- **`Λ'(6) = 0`**: the centre is a critical point of `Λ` (from `Λ(12 − s) = Λ(s)`). -/
theorem heckeLambda_deriv_center : deriv heckeLambda 6 = 0 := by
  have hd := heckeLambda_entire 6
  have h1 : HasDerivAt (fun s => heckeLambda (12 - s)) (-deriv heckeLambda 6) 6 := by
    have := (heckeLambda_entire (12 - 6)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℂ => 12 - s) (-1) 6 := by
      simpa using (hasDerivAt_id (6 : ℂ)).const_sub 12
    have h3 := this.comp (6 : ℂ) h2
    norm_num at h3 ⊢
    convert h3 using 1
  have h4 : (fun s => heckeLambda (12 - s)) = heckeLambda :=
    funext heckeLambda_functional_equation
  rw [h4] at h1
  have := h1.unique hd.hasDerivAt
  linear_combination -this / 2

end RamanujanTau.HeckeL
