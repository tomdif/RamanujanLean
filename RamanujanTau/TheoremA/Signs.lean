import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-!
# The bad-prime eigenvalues after four theta operations

Euler's criterion turns the eigenvalue prescribed by the proposed
Atkin–Lehner sign class into `q²` after multiplication by `q⁴`.
The modular-form formula for that original eigenvalue is a separate input.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA

/-- The sign calculation works over every residue field of characteristic `p`.
For `q = 2, 3`, the resulting eigenvalues are `4, 9`. -/
theorem theta_four_eigenvalue (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (K : Type*) [Field K] [CharP K p] (q : ℕ) :
    (q : K) ^ 4 * ((legendreSym p (q : ℤ) : K) * (q : K) ^ ((p - 5) / 2)) =
      (q : K) ^ 2 := by
  have he : (legendreSym p (q : ℤ) : K) = (q : K) ^ (p / 2) := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K) (legendreSym.eq_pow p (q : ℤ))
    simpa only [map_intCast, map_pow, Int.cast_natCast, map_natCast] using h
  have hpodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hexp : 4 + (p / 2 + (p - 5) / 2) = p + 1 := by omega
  have hfermat : (q : K) ^ p = q := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (q : ZMod p))
    simpa only [map_pow, map_natCast] using h
  rw [he, ← pow_add, ← pow_add, hexp, pow_succ, hfermat, pow_two]

end RamanujanTau.TheoremA
