import Mathlib.NumberTheory.Padics.RingHoms

/-! Recover a residue after exact division by p from a certificate modulo p². -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.PadicDivision
variable {p : ℕ} [Fact p.Prime]

lemma mod_pow_eq_iff_dvd (n : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]

lemma mod_eq_iff_dvd (x y : ℤ_[p]) :
    PadicInt.toZMod x = PadicInt.toZMod y ↔ (p : ℤ_[p]) ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

lemma cancel_mod_square (x y : ℤ_[p]) :
    PadicInt.toZModPow 2 ((p : ℤ_[p]) * x) = PadicInt.toZModPow 2 ((p : ℤ_[p]) * y) ↔
      PadicInt.toZMod x = PadicInt.toZMod y := by
  rw [mod_pow_eq_iff_dvd, mod_eq_iff_dvd, ← mul_sub, pow_two]
  exact mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

end RamanujanTau.FiniteArithmetic.PadicDivision
