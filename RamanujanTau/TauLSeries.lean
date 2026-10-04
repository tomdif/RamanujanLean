/-
# Ramanujan's L-function and its Euler product

For `Re s > 7`,

  `L(Δ, s) = Σ τ(n) n⁻ˢ = ∏_p (1 − τ(p) p⁻ˢ + p¹¹ p⁻²ˢ)⁻¹`   (`LSeries_tau_eulerProduct`).

The three ingredients are:
* **Hecke's bound** `τ(n) = O(n⁶)` (Mathlib's `CuspFormClass.qExpansion_isBigO` with `Δ`, via the q-expansion
  bridge). It gives absolute convergence for `Re s > 7`.
* **Mordell's multiplicativity** (`HeckeQExp.tau_mul_coprime`), which feeds Mathlib's `eulerProduct_hasProd`.
* **The local factor**: the Hecke recurrence `τ(p^{e+2}) = τ(p)τ(p^{e+1}) − p¹¹τ(p^e)` makes
  `(1 − τ(p)x + p¹¹x²)·Σ τ(pᵉ)xᵉ = 1`.
-/
import RamanujanTau.HeckeQExp
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Basic

set_option autoImplicit false

namespace RamanujanTau
open Complex LSeries Filter Asymptotics ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- `τ` as a complex arithmetic function. -/
noncomputable def tauC (n : ℕ) : ℂ := (τ n : ℂ)

/-- **Hecke's bound** `τ(n) = O(n⁶)`. -/
theorem tau_isBigO : tauC =O[atTop] fun n : ℕ => (n : ℝ) ^ (6 : ℝ) := by
  have h := CuspFormClass.qExpansion_isBigO (k := 12) (Γ := 𝒮ℒ) CuspForm.discriminant
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  have e : ∀ n, (qExpansion 1 CuspForm.discriminant).coeff n = tauC n := fun n =>
    heckeData.coeff_discriminant n
  simp_rw [e] at h
  convert h using 3; norm_num

theorem LSeriesSummable_tau {s : ℂ} (hs : 7 < s.re) : LSeriesSummable tauC s :=
  LSeriesSummable_of_isBigO_rpow hs (by convert tau_isBigO using 3; norm_num)

lemma term_pow (s : ℂ) (p e : ℕ) (hp : p ≠ 0) :
    term tauC s (p ^ e) = tauC (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_of_ne_zero (pow_ne_zero _ hp), Nat.cast_pow, ← natCast_cpow_natCast_mul, mul_comm (e : ℂ),
    cpow_mul_nat, div_eq_mul_inv, ← inv_pow, ← cpow_neg]

/-- **The local Euler factor.** -/
theorem tsum_local_factor {s : ℂ} (hs : 7 < s.re) {p : ℕ} (hp : p.Prime) :
    ∑' e, term tauC s (p ^ e) = (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  set x := (p : ℂ) ^ (-s)
  set a : ℕ → ℂ := fun e => tauC (p ^ e)
  have hsum : Summable fun e => a e * x ^ e := by
    have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
    have := (LSeriesSummable_tau hs).comp_injective hinj
    simpa [Function.comp_def, term_pow s _ _ hp.ne_zero, a, x] using this
  simp_rw [term_pow s _ _ hp.ne_zero]
  set S := ∑' e, a e * x ^ e
  have ha0 : a 0 = 1 := by simp [a, tauC, tau_one]
  have ha1 : a 1 = tauC p := by simp [a]
  have hrec : ∀ e, a (e + 2) = tauC p * a (e + 1) - (p : ℂ) ^ 11 * a e := fun e => by
    have := tau_hecke_recurrence hp (r := e + 1) (by omega)
    simp only [a, tauC]; rw [show e + 2 = e + 1 + 1 by ring, this]; push_cast; simp
  have h1 : S = a 0 + ∑' e, a (e + 1) * x ^ (e + 1) := hsum.tsum_eq_zero_add.trans (by simp)
  have hsum1 : Summable fun e => a (e + 1) * x ^ (e + 1) := (summable_nat_add_iff 1).mpr hsum
  have h2 : ∑' e, a (e + 1) * x ^ (e + 1) = a 1 * x + ∑' e, a (e + 2) * x ^ (e + 2) :=
    hsum1.tsum_eq_zero_add.trans (by simp)
  have h3 : ∑' e, a (e + 2) * x ^ (e + 2) =
      tauC p * x * ∑' e, a (e + 1) * x ^ (e + 1) - (p : ℂ) ^ 11 * x ^ 2 * S := by
    simp_rw [hrec]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub]
    · congr 1; funext e; ring
    · exact hsum1.mul_left _
    · exact hsum.mul_left _
  have key : S * (1 - tauC p * x + (p : ℂ) ^ 11 * x ^ 2) = 1 := by
    have h1' : S = 1 + ∑' e, a (e + 1) * x ^ (e + 1) := by rw [h1, ha0]
    rw [ha1] at h2
    linear_combination (1 - tauC p * x) * h1' + h2 + h3
  exact eq_inv_of_mul_eq_one_left key

/-- **The Euler product of Ramanujan's L-function** (Mordell 1917), for `Re s > 7`. -/
theorem LSeries_tau_eulerProduct {s : ℂ} (hs : 7 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹) (LSeries tauC s) := by
  have hf1 : term tauC s 1 = 1 := by simp [term_of_ne_zero, tauC, tau_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → term tauC s (m * n) = term tauC s m * term tauC s n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp
    rw [term_of_ne_zero (Nat.mul_ne_zero hm.ne' hn.ne'), term_of_ne_zero hm.ne', term_of_ne_zero hn.ne',
      tauC, tau_mul_coprime hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
    simp only [tauC]; push_cast; field_simp
  have hsum : Summable (‖term tauC s ·‖) := summable_norm_iff.mpr (LSeriesSummable_tau hs)
  have := EulerProduct.eulerProduct_hasProd hf1 hmul hsum (term_zero _ _)
  convert this using 1
  funext p
  exact (tsum_local_factor hs p.2).symm

end RamanujanTau
