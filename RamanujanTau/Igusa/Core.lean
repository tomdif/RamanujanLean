import Mathlib

/-!
# Igusa's argument, univariate core

Let `F` be a field of characteristic `p`. Suppose `a, b ∈ F[X]` satisfy the first-order system
  `b = u a' + w₁ a`,   `−r a = u b' + w₂ b`
(in the application `a`, `b` are charts of the Hasse polynomial `Ā` and of `∂Ā`, and the system comes
from Ramanujan's differential equations). If `a ≠ 0`, `deg a < p` and `u(t₀) ≠ 0`, then `t₀` is at most
a simple root of `a` (`not_sq_dvd`).

Proof: if `a = (X − t₀)^{m+2} g`, `g(t₀) ≠ 0`, then `b = (X − t₀)^{m+1} h` with
`h(t₀) = (m+2) u(t₀) g(t₀) ≠ 0`, and then `u b' + w₂ b = (X − t₀)^m [(m+1) u h + (X − t₀)(…)]` has
order exactly `m` at `t₀` (as `0 < m + 1, m + 2 < p`), while `−r a` has order `≥ m + 2`.
-/

set_option autoImplicit false

namespace Igusa
open Polynomial

variable {F : Type*} [Field F] {p : ℕ} [CharP F p]

lemma natCast_ne_zero_of_lt {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : F) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff F p]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

/-- **Igusa's core lemma.** -/
theorem not_sq_dvd {a b u w₁ w₂ r : F[X]} {t₀ : F} (ha : a ≠ 0)
    (hdeg : a.natDegree < p) (hu : u.eval t₀ ≠ 0)
    (hb : b = u * derivative a + w₁ * a) (hrel : -(r * a) = u * derivative b + w₂ * b) :
    ¬ (X - C t₀) ^ 2 ∣ a := by
  intro hsq
  obtain ⟨g, hag, hg⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha t₀
  set n := a.rootMultiplicity t₀ with hn
  have hn2 : 2 ≤ n := (le_rootMultiplicity_iff ha).mpr hsq
  have hnp : n < p := by
    have h1 : ((X - C t₀) ^ n).natDegree ≤ a.natDegree :=
      natDegree_le_of_dvd ⟨g, hag⟩ ha
    rw [natDegree_pow, natDegree_X_sub_C, mul_one] at h1
    omega
  have hg0 : g.eval t₀ ≠ 0 := by
    intro h; exact hg (dvd_iff_isRoot.mpr h)
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [hm] at hag hnp
  set y : F[X] := X - C t₀ with hy
  have hy0 : y.eval t₀ = 0 := by simp [hy]
  have hyd : derivative y = 1 := by simp [hy]
  have hyne : y ≠ 0 := X_sub_C_ne_zero t₀
  set h : F[X] := u * (C ((m + 2 : ℕ) : F) * g + y * derivative g) + w₁ * y * g with hh
  have hbh : b = y ^ (m + 1) * h := by
    rw [hb, hag, derivative_mul, derivative_pow, hyd, hh]
    simp only [mul_one]
    rw [show m + 2 - 1 = m + 1 by omega]
    push_cast
    simp only [map_add, map_natCast, map_ofNat]
    ring
  have hh0 : h.eval t₀ = u.eval t₀ * (((m + 2 : ℕ) : F) * g.eval t₀) := by
    simp [hh, hy0]
  have hh0' : h.eval t₀ ≠ 0 := by
    rw [hh0]
    exact mul_ne_zero hu (mul_ne_zero (natCast_ne_zero_of_lt (by omega) hnp) hg0)
  have key : y ^ m * (-(r * y ^ 2 * g)) =
      y ^ m * (u * (C ((m + 1 : ℕ) : F) * h + y * derivative h) + w₂ * y * h) := by
    have e1 : -(r * a) = y ^ m * (-(r * y ^ 2 * g)) := by rw [hag]; ring
    have e2 : u * derivative b + w₂ * b =
        y ^ m * (u * (C ((m + 1 : ℕ) : F) * h + y * derivative h) + w₂ * y * h) := by
      rw [hbh, derivative_mul, derivative_pow, hyd]
      simp only [mul_one, Nat.add_sub_cancel]
      push_cast
      simp only [map_add, map_natCast, map_one]
      ring
    rw [← e1, hrel, e2]
  have key' := mul_left_cancel₀ (pow_ne_zero m hyne) key
  have := congrArg (eval t₀) key'
  simp only [eval_neg, eval_mul, eval_pow, hy0, eval_add, eval_C] at this
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
    neg_zero, add_zero] at this
  have hm1 : ((m + 1 : ℕ) : F) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
  exact mul_ne_zero hu (mul_ne_zero hm1 hh0') this.symm

end Igusa
