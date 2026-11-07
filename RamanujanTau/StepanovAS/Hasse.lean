/-
# Hasse derivatives in characteristic `p`

* `hasseDeriv_expand_eq_zero`: for `Q = p^s` and `0 < j < Q`, `D^{(j)} (expand Q g) = 0`;
* `hasseDeriv_mul_expand`: for `ℓ < Q`, `D^{(ℓ)} (f · expand Q g) = D^{(ℓ)} f · expand Q g`
  (polynomials in `X^Q` behave as constants for Hasse derivatives of order `< Q`);
* `le_rootMultiplicity_of_hasseDeriv`: if `D^{(ℓ)} f (x) = 0` for all `ℓ < M` and `f ≠ 0`,
  then `x` is a root of multiplicity `≥ M` (valid in every characteristic).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.StepanovAS

open Polynomial Finset

section Hasse

variable {K : Type*} [Field K]

/-- `binom(Q m, j) = 0` in characteristic `p` when `Q = p^s` does not divide `j`. -/
theorem choose_cast_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p] (s m j : ℕ)
    (hj : ¬ p ^ s ∣ j) : ((Nat.choose (p ^ s * m) j : ℕ) : K) = 0 := by
  have h1 : ((X + 1 : K[X]) ^ (p ^ s * m)).coeff j = ((Nat.choose (p ^ s * m) j : ℕ) : K) :=
    coeff_X_add_one_pow K _ j
  have h2 : (X + 1 : K[X]) ^ (p ^ s * m) = expand K (p ^ s) ((X + 1) ^ m) := by
    rw [pow_mul, add_pow_char_pow, one_pow, map_pow, map_add, expand_X, map_one]
  rw [← h1, h2, coeff_expand (pow_pos (Fact.out : p.Prime).pos s), if_neg hj]

theorem hasseDeriv_expand_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) (g : K[X])
    {j : ℕ} (hj0 : 0 < j) (hjQ : j < p ^ s) : hasseDeriv j (expand K (p ^ s) g) = 0 := by
  have hj : ¬ p ^ s ∣ j := fun h => absurd (Nat.le_of_dvd hj0 h) (by omega)
  induction g using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | monomial n a =>
    rw [expand_monomial, hasseDeriv_monomial, mul_comm n (p ^ s),
      choose_cast_eq_zero p s n j hj, zero_mul, monomial_zero_right]

theorem hasseDeriv_mul_expand (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) (f g : K[X])
    {ℓ : ℕ} (hℓ : ℓ < p ^ s) :
    hasseDeriv ℓ (f * expand K (p ^ s) g) = hasseDeriv ℓ f * expand K (p ^ s) g := by
  rw [hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  rw [Finset.sum_eq_zero, zero_add, Nat.sub_self, hasseDeriv_zero, LinearMap.id_apply]
  intro i hi
  rw [Finset.mem_range] at hi
  rw [hasseDeriv_expand_eq_zero p s g (by omega) (by omega), mul_zero]

/-- **Multiplicity from Hasse derivatives.** -/
theorem le_rootMultiplicity_of_hasseDeriv {f : K[X]} (hf : f ≠ 0) (x : K) (M : ℕ)
    (h : ∀ ℓ < M, (hasseDeriv ℓ f).eval x = 0) : M ≤ rootMultiplicity x f := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  have hT : f.comp (X + C x) ≠ 0 := by
    rw [← taylor_apply]
    intro h0
    apply hf
    have := congrArg (taylor (-x)) h0
    rwa [taylor_taylor, neg_add_cancel, taylor_zero, map_zero] at this
  apply le_natTrailingDegree hT
  intro m hm
  rw [← taylor_apply, taylor_coeff]
  exact h m hm

end Hasse

end RamanujanTau.StepanovAS

#print axioms RamanujanTau.StepanovAS.hasseDeriv_mul_expand
#print axioms RamanujanTau.StepanovAS.le_rootMultiplicity_of_hasseDeriv
