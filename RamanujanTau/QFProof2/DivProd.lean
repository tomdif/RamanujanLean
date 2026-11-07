/-
# Sums over divisors of products of local factors

**`sum_divisors_prod_local`**: for `g ≠ 0` and any `φ : ℕ → ℕ → ℝ`,

  `Σ_{d | g} Π_{p | g} φ(p, v_p(d)) = Π_{p | g} Σ_{e ≤ v_p(g)} φ(p, e)`.

This is the exchange step of `QDecomp`: `Σ_{d|(h,k)} W(d)U(h,d)U(k,d) = Π_p Σ_{e≤min} W_p L_p L_p`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.QFProof2

open Finset

theorem sum_divisors_prod_local {g : ℕ} (hg : g ≠ 0) (φ : ℕ → ℕ → ℝ) :
    ∑ d ∈ g.divisors, ∏ p ∈ g.primeFactors, φ p (d.factorization p) =
      ∏ p ∈ g.primeFactors, ∑ e ∈ Icc 0 (g.factorization p), φ p e := by
  classical
  rw [Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hg, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_attach (Iic g.factorization)
    (fun f : ℕ →₀ ℕ => ∏ p ∈ g.primeFactors, φ p ((f.prod (· ^ ·)).factorization p))]
  have h1 : ∀ f ∈ Iic g.factorization,
      ∏ p ∈ g.primeFactors, φ p ((f.prod (· ^ ·)).factorization p) =
      ∏ p ∈ g.primeFactors, φ p (f p) := by
    intro f hf
    have hle : f ≤ g.factorization := mem_Iic.1 hf
    have hpr : ∀ p ∈ f.support, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (by
        rw [← Nat.support_factorization]
        exact Finsupp.support_mono hle hp)
    rw [Nat.prod_pow_factorization_eq_self hpr]
  rw [sum_congr rfl h1, prod_sum]
  have hI : Iic g.factorization = Icc 0 g.factorization := by
    ext f; simp
  rw [hI, Finsupp.Icc_eq, Finsupp.support_zero, empty_union, Nat.support_factorization]
  have hR : (⇑(Finsupp.rangeIcc 0 g.factorization)) = fun p => Icc 0 (g.factorization p) := by
    funext p; rw [Finsupp.coe_rangeIcc]; rfl
  unfold Finset.finsupp
  rw [sum_map, hR]
  refine sum_congr (by convert rfl) fun x _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← prod_attach g.primeFactors]
  refine prod_congr rfl fun p _ => ?_
  rw [Finsupp.indicator_of_mem p.2]

end RamanujanTau.QFProof2
