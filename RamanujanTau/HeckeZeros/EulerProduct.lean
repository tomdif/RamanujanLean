/-
# Euler product and non-vanishing of `L(Δ,s)` on `Re s > 13/2`

Extends `RamanujanTau.LSeries_tau_eulerProduct` (proved for `Re s > 7` from Hecke's bound) to the full
half-plane of absolute convergence `Re s > 13/2` (Rankin, `HeckeConvex.LSeriesSummable_tau_of_gt_13_2`),
and deduces `tauL s ≠ 0` there: the polynomial factors `P_p(s) = 1 − τ(p)p^{−s} + p^{11−2s}` satisfy
`∑_p ‖P_p − 1‖ < ∞`, so `∏ P_p` converges to a non-zero limit (Mathlib's
`tprod_one_add_ne_zero_of_summable`), and `(∏ P_p) · L(Δ,s) = ∏ (P_p · P_p⁻¹) = 1`.
-/
import RamanujanTau.HeckeConvex.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false

namespace RamanujanTau.HeckeZeros

open Complex LSeries
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex

/-- The local polynomial `P_p(s) = 1 − τ(p) p^{−s} + p^{11} p^{−2s}`. -/
noncomputable def localPoly (s : ℂ) (p : ℕ) : ℂ :=
  1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2

/-- The local factor identity `P_p(s) · ∑_e τ(p^e) p^{−es} = 1` on `Re s > 13/2`. -/
theorem localPoly_mul_tsum {s : ℂ} (hs : 13 / 2 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e, term tauC s (p ^ e)) * localPoly s p = 1 := by
  set x := (p : ℂ) ^ (-s)
  set a : ℕ → ℂ := fun e => tauC (p ^ e)
  have hsum : Summable fun e => a e * x ^ e := by
    have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
    have := (LSeriesSummable_tau_of_gt_13_2 hs).comp_injective hinj
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
  have h1' : S = 1 + ∑' e, a (e + 1) * x ^ (e + 1) := by rw [h1, ha0]
  rw [ha1] at h2
  simp only [localPoly]
  linear_combination (1 - tauC p * x) * h1' + h2 + h3

lemma localPoly_ne_zero {s : ℂ} (hs : 13 / 2 < s.re) {p : ℕ} (hp : p.Prime) : localPoly s p ≠ 0 :=
  right_ne_zero_of_mul_eq_one (localPoly_mul_tsum hs hp)

/-- **Euler product of `L(Δ,s)` on the full half-plane `Re s > 13/2`** (Mordell 1917 + Rankin 1939):
`L(Δ,s) = ∏_p (1 − τ(p)p^{−s} + p^{11−2s})^{−1}`. -/
theorem LSeries_tau_eulerProduct_of_gt {s : ℂ} (hs : 13 / 2 < s.re) :
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
  have hsum : Summable (‖term tauC s ·‖) :=
    summable_norm_iff.mpr (LSeriesSummable_tau_of_gt_13_2 hs)
  have := EulerProduct.eulerProduct_hasProd hf1 hmul hsum (term_zero _ _)
  convert this using 1
  funext p
  exact (eq_inv_of_mul_eq_one_left (localPoly_mul_tsum hs p.2)).symm

/-- The same Euler product for the entire continuation `tauL`. -/
theorem tauL_eulerProduct {s : ℂ} (hs : 13 / 2 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹) (tauL s) := by
  rw [tauL_eq_LSeries_of_gt hs]; exact LSeries_tau_eulerProduct_of_gt hs

/-- `∑_p ‖P_p(s) − 1‖ < ∞` for `Re s > 13/2`. -/
lemma summable_localPoly_sub_one {s : ℂ} (hs : 13 / 2 < s.re) :
    Summable fun p : Nat.Primes => ‖localPoly s p - 1‖ := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  -- the `τ(p) p^{-s}` part
  have hA : Summable fun p : Nat.Primes => ‖tauC p * (p : ℂ) ^ (-s)‖ := by
    have h := ((LSeriesSummable_tau_of_gt_13_2 hs).norm).comp_injective hinj
    refine h.congr fun p => ?_
    have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
    simp only [Function.comp_apply, term_of_ne_zero hp0, cpow_neg, div_eq_mul_inv]
  -- the `p^{11-2s}` part
  have hB : Summable fun p : Nat.Primes => ‖(p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2‖ := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (11 - 2 * s.re) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine (h.comp_injective hinj).congr fun p => ?_
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    simp only [Function.comp_apply, norm_mul, norm_pow, Complex.norm_natCast]
    rw [norm_natCast_cpow_of_pos p.2.pos, neg_re, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
    congr 1; push_cast; ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hA.add hB)
  have : localPoly s p - 1 = -(tauC p * (p : ℂ) ^ (-s)) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2 := by
    simp only [localPoly]; ring
  rw [this]
  exact (norm_add_le _ _).trans (by rw [norm_neg])

/-- **Non-vanishing of `L(Δ,s)` on `Re s > 13/2`.** -/
theorem tauL_ne_zero_of_gt {s : ℂ} (hs : 13 / 2 < s.re) : tauL s ≠ 0 := by
  set f : Nat.Primes → ℂ := fun p => localPoly s p - 1
  have hf : ∀ p, 1 + f p ≠ 0 := fun p => by
    simpa [f] using localPoly_ne_zero hs p.2
  have hQ : ∏' p, (1 + f p) ≠ 0 := tprod_one_add_ne_zero_of_summable hf (summable_localPoly_sub_one hs)
  have hP : HasProd (fun p => 1 + f p) (∏' p, (1 + f p)) :=
    (multipliable_one_add_of_summable (summable_localPoly_sub_one hs)).hasProd
  have hE := tauL_eulerProduct hs
  have hprod := hP.mul hE
  have h1 : (fun p : Nat.Primes => (1 + f p) *
      (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹) = fun _ => 1 := by
    funext p
    have := localPoly_ne_zero hs p.2
    simp only [f, add_sub_cancel]
    exact mul_inv_cancel₀ this
  rw [h1] at hprod
  have h := hprod.unique hasProd_one
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-- Equivalently `L(Δ,s) = ∑ τ(n) n^{−s} ≠ 0` for `Re s > 13/2`. -/
theorem LSeries_tau_ne_zero_of_gt {s : ℂ} (hs : 13 / 2 < s.re) : LSeries tauC s ≠ 0 := by
  rw [← tauL_eq_LSeries_of_gt hs]; exact tauL_ne_zero_of_gt hs

end RamanujanTau.HeckeZeros
