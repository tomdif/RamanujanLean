/-
# The primitive 84th root of unity `Z = e^{πi/42}`

All coefficients at the MTC₀ specialization point are powers of `Z` (`i = Z²¹`, `−1 = Z⁴²`).
`zsimp` collects products of powers of `Z` into a single power; `Z_mod` compares exponents mod 84.
-/
import RamanujanTau.ALBase
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace MTC
open ALz

/-! ## The 84th root of unity -/

noncomputable def Z84 : ℂ := Complex.exp (↑Real.pi * Complex.I / 42)

lemma Z_ne : Z84 ≠ 0 := Complex.exp_ne_zero _

lemma Z_zpow (n : ℤ) : Z84 ^ n = Complex.exp (n * (↑Real.pi * Complex.I / 42)) := (Complex.exp_int_mul _ n).symm

lemma Z_84 : Z84 ^ (84 : ℤ) = 1 := by
  rw [Z_zpow]; push_cast
  rw [show (84 : ℂ) * (↑Real.pi * Complex.I / 42) = 2 * ↑Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

lemma Z_mod {n k : ℤ} (h : n % 84 = k % 84) : Z84 ^ n = Z84 ^ k := by
  have e : n = k + 84 * ((n - k) / 84) := by omega
  rw [e, zpow_add₀ Z_ne, zpow_mul, Z_84, one_zpow, mul_one]

lemma Z_eq_one {n : ℤ} (h : n % 84 = 0) : Z84 ^ n = 1 := by
  rw [Z_mod (k := 0) (by rw [h]; rfl), zpow_zero]

lemma Z_neg1 : (-1 : ℂ) = Z84 ^ (42 : ℤ) := by
  rw [Z_zpow]; push_cast
  rw [show (42 : ℂ) * (↑Real.pi * Complex.I / 42) = ↑Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]

lemma Z_neg' (a : ℂ) : -a = Z84 ^ (42 : ℤ) * a := by rw [← Z_neg1]; ring

lemma Z_prim {n : ℤ} (h : Z84 ^ n = 1) : n % 84 = 0 := by
  rw [Z_zpow, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hpi : (↑Real.pi * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h2 : ((n : ℂ) - 84 * k) * (↑Real.pi * Complex.I) = 0 := by linear_combination 42 * hk
  have h3 : ((n - 84 * k : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.mp h2).resolve_right hpi
  have h4 : n - 84 * k = 0 := by exact_mod_cast h3
  omega

lemma Z_ne_one {n : ℤ} (h : n % 84 ≠ 0) : Z84 ^ n ≠ 1 := fun h' => h (Z_prim h')

lemma Z_ne_Z {a b : ℤ} (h : (a - b) % 84 ≠ 0) : Z84 ^ a ≠ Z84 ^ b := fun h' =>
  h (Z_prim (by rw [zpow_sub₀ Z_ne, h', div_self (zpow_ne_zero _ Z_ne)]))

lemma Z_norm : ‖Z84‖ = 1 := by
  rw [Z84, show (↑Real.pi * Complex.I / 42) = ((Real.pi / 42 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- normal form of products of powers of `Z`. -/
macro "zsimp" : tactic =>
  `(tactic| simp only [Z_neg', mul_zpow, ← zpow_mul, ← zpow_add₀ Z_ne, mul_one, one_mul, zpow_one, zpow_zero])

lemma Z_I : Complex.I = Z84 ^ (21 : ℤ) := by
  rw [Z_zpow]; push_cast
  rw [show (21 : ℂ) * (↑Real.pi * Complex.I / 42) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

end MTC
