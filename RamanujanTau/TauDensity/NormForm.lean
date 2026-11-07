import RamanujanTau.TauDensity.Structure
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! # `τ` never vanishes on the values of `x² + 691 y²`

* `neg691_not_square`: if `q` is prime and `q ≡ −1 (mod 691)`, then `−691` is not a square mod `q`
  (Jacobi symbol: `J(−691 | q)` only depends on `q mod 2764`, and `J(−691 | 1381) = J(−691 | 2763) = −1`).
* `dvd_of_dvd_norm`: such a `q` dividing `x² + 691y²` divides both `x` and `y`.
* `even_factorization_norm`: `v_q(x² + 691y²)` is even for every such `q`.
* `tau_norm_form_ne_zero`: `τ(x² + 691y²) ≠ 0` whenever `x² + 691y² ≥ 1`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau

/-- **`−691` is a non-residue modulo every prime `q ≡ −1 (mod 691)`.** -/
theorem neg691_not_square {q : ℕ} (hq : q.Prime) (h : q % 691 = 690) :
    ¬ IsSquare (((-691 : ℤ) : ZMod q)) := by
  haveI := Fact.mk hq
  have hodd : Odd q := hq.odd_of_ne_two (by rintro rfl; norm_num at h)
  have hJ : jacobiSym (-691) q = -1 := by
    rw [jacobiSym.mod_right _ hodd]
    have h4 : q % (4 * (-691 : ℤ).natAbs) = 1381 ∨ q % (4 * (-691 : ℤ).natAbs) = 2763 := by
      have : (-691 : ℤ).natAbs = 691 := rfl
      rw [this]
      have := Nat.odd_iff.mp hodd
      omega
    rcases h4 with h4 | h4 <;> rw [h4] <;> norm_num
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hJ
  exact (legendreSym.eq_neg_one_iff q).mp hJ

/-- If a prime `q ≡ −1 (mod 691)` divides `x² + 691 y²`, it divides `x` and `y`. -/
theorem dvd_of_dvd_norm {q x y : ℕ} (hq : q.Prime) (h : q % 691 = 690)
    (hd : q ∣ x ^ 2 + 691 * y ^ 2) : q ∣ x ∧ q ∣ y := by
  haveI := Fact.mk hq
  have hy : q ∣ y := by
    by_contra hy
    have hy0 : (y : ZMod q) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h0 : ((x ^ 2 + 691 * y ^ 2 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h0
    apply neg691_not_square hq h
    refine ⟨(x : ZMod q) / y, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy0 hy0)]
    push_cast
    linear_combination -h0
  refine ⟨?_, hy⟩
  have h2 : q ∣ x ^ 2 := by
    have : q ∣ 691 * y ^ 2 := Dvd.dvd.mul_left (dvd_pow hy two_ne_zero) _
    exact (Nat.dvd_add_left this).mp hd
  exact hq.dvd_of_dvd_pow h2

/-- **Inert primes divide `x² + 691y²` to an even power.** -/
theorem even_factorization_norm {q : ℕ} (hq : q.Prime) (h : q % 691 = 690) :
    ∀ x y : ℕ, x ^ 2 + 691 * y ^ 2 ≠ 0 → Even ((x ^ 2 + 691 * y ^ 2).factorization q) := by
  intro x y
  induction hn : x ^ 2 + 691 * y ^ 2 using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    intro hn0
    by_cases hd : q ∣ n
    · subst hn
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := dvd_of_dvd_norm hq h hd
      have hq1 := hq.one_lt
      have hab : a ^ 2 + 691 * b ^ 2 ≠ 0 := by
        intro h0; apply hn0; rw [mul_pow, mul_pow]
        calc q ^ 2 * a ^ 2 + 691 * (q ^ 2 * b ^ 2) = q ^ 2 * (a ^ 2 + 691 * b ^ 2) := by ring
          _ = 0 := by rw [h0, mul_zero]
      have heq : (q * a) ^ 2 + 691 * (q * b) ^ 2 = q ^ 2 * (a ^ 2 + 691 * b ^ 2) := by ring
      have hlt : a ^ 2 + 691 * b ^ 2 < (q * a) ^ 2 + 691 * (q * b) ^ 2 := by
        rw [heq]
        have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq1
        have := Nat.pos_of_ne_zero hab
        nlinarith
      have ihab := ih _ hlt a b rfl hab
      rw [heq, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hab, Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hq.factorization_self, mul_one]
      exact even_two.add ihab
    · rw [Nat.factorization_eq_zero_of_not_dvd hd]; exact ⟨0, rfl⟩

/-- **`τ(x² + 691y²) ≠ 0`** for all `x, y` with `x² + 691y² ≥ 1`. -/
theorem tau_norm_form_ne_zero {x y : ℕ} (h : 1 ≤ x ^ 2 + 691 * y ^ 2) :
    τ (x ^ 2 + 691 * y ^ 2) ≠ 0 :=
  tau_ne_zero_of_mod691 h fun q hq hodd hmod =>
    Nat.not_even_iff_odd.mpr hodd (even_factorization_norm hq hmod x y (by omega))

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.neg691_not_square
#print axioms RamanujanTau.TauDensity.dvd_of_dvd_norm
#print axioms RamanujanTau.TauDensity.even_factorization_norm
#print axioms RamanujanTau.TauDensity.tau_norm_form_ne_zero
