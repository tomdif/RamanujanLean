/-
# The primitive 16th root of unity `W = e^{πi/8}`

All coefficients at the `ψ₀` specialization point of `f_{1,4,1}` are powers of `W` (`i = W⁴`, `−1 = W⁸`).
`wsimp` collects products of powers of `W` into a single power; `W_mod` compares exponents mod 16.
-/
import RamanujanTau.ALBase
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace MTC.H141
open ALz

/-! ## The 16th root of unity -/

noncomputable def W16 : ℂ := Complex.exp (↑Real.pi * Complex.I / 8)

lemma W_ne : W16 ≠ 0 := Complex.exp_ne_zero _

lemma W_zpow (n : ℤ) : W16 ^ n = Complex.exp (n * (↑Real.pi * Complex.I / 8)) := (Complex.exp_int_mul _ n).symm

lemma W_16 : W16 ^ (16 : ℤ) = 1 := by
  rw [W_zpow]; push_cast
  rw [show (16 : ℂ) * (↑Real.pi * Complex.I / 8) = 2 * ↑Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

lemma W_mod {n k : ℤ} (h : n % 16 = k % 16) : W16 ^ n = W16 ^ k := by
  have e : n = k + 16 * ((n - k) / 16) := by omega
  rw [e, zpow_add₀ W_ne, zpow_mul, W_16, one_zpow, mul_one]

lemma W_eq_one {n : ℤ} (h : n % 16 = 0) : W16 ^ n = 1 := by
  rw [W_mod (k := 0) (by rw [h]; rfl), zpow_zero]

lemma W_neg1 : (-1 : ℂ) = W16 ^ (8 : ℤ) := by
  rw [W_zpow]; push_cast
  rw [show (8 : ℂ) * (↑Real.pi * Complex.I / 8) = ↑Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]

lemma W_neg' (a : ℂ) : -a = W16 ^ (8 : ℤ) * a := by rw [← W_neg1]; ring

lemma W_prim {n : ℤ} (h : W16 ^ n = 1) : n % 16 = 0 := by
  rw [W_zpow, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hpi : (↑Real.pi * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h2 : ((n : ℂ) - 16 * k) * (↑Real.pi * Complex.I) = 0 := by linear_combination 8 * hk
  have h3 : ((n - 16 * k : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.mp h2).resolve_right hpi
  have h4 : n - 16 * k = 0 := by exact_mod_cast h3
  omega

lemma W_ne_one {n : ℤ} (h : n % 16 ≠ 0) : W16 ^ n ≠ 1 := fun h' => h (W_prim h')

lemma W_ne_W {a b : ℤ} (h : (a - b) % 16 ≠ 0) : W16 ^ a ≠ W16 ^ b := fun h' =>
  h (W_prim (by rw [zpow_sub₀ W_ne, h', div_self (zpow_ne_zero _ W_ne)]))

lemma W_norm : ‖W16‖ = 1 := by
  rw [W16, show (↑Real.pi * Complex.I / 8) = ((Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- normal form of products of powers of `Z`. -/
macro "wsimp" : tactic =>
  `(tactic| simp only [W_neg', mul_zpow, ← zpow_mul, ← zpow_add₀ W_ne, mul_one, one_mul, zpow_one, zpow_zero])

lemma W_I : Complex.I = W16 ^ (4 : ℤ) := by
  rw [W_zpow]; push_cast
  rw [show (4 : ℂ) * (↑Real.pi * Complex.I / 8) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

end MTC.H141
