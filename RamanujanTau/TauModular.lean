/-
# Consequences of the analytic–formal bridge

With `qExpansion_discriminant_coeff` (`[qⁿ]Δ = τ(n)` for the formal `τ`), the modular-forms results proved on
Mathlib's analytic `Δ` transfer to the combinatorial `τ`, and vice versa:

* **`tau_mod691`** — Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)` for `τ(n) = [qⁿ] q∏(1 − qᵏ)²⁴`, and
  **`tau_computable_mod691`** for the computable list-based `RamanujanTau.tau`.
* **`discriminant_formal_identity`** — the identity `1728·q∏(1 − qⁿ)²⁴ = E₄³ − E₆²` of *integer* formal power
  series, with `E₄ = 1 + 240Σσ₃(n)qⁿ`, `E₆ = 1 − 504Σσ₅(n)qⁿ`. It is a purely formal statement, proved here
  through the analytic theory (modularity + the dimension of `M₁₂`).
* **`qExpansion_discriminant_eq`** — `qExpansion(Δ)` is literally the image of `q(q;q)²⁴_∞` in `ℂ⟦q⟧`.
-/
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.Mod691
import RamanujanTau.TauBridge
import RamanujanTau.Congruences

set_option autoImplicit false

namespace RamanujanTau.TauModular
open ModularForm UpperHalfPlane PowerSeries
open scoped ArithmeticFunction.sigma
open RamanujanTau.DiscriminantBridge (Δmod qExpansion_discriminant_coeff)
open RamanujanTau.Mod691 (p4 p6)

/-- `qExpansion(Δ)` is the image in `ℂ⟦q⟧` of the integer series `q ∏ (1 − qᵏ)²⁴`. -/
theorem qExpansion_discriminant_eq :
    qExpansion 1 Δmod = PowerSeries.map (Int.castRingHom ℂ) (X * MockTheta5.JTP.qfacInf ^ 24) := by
  ext n
  rw [qExpansion_discriminant_coeff, coeff_map]; rfl

/-- **Ramanujan's congruence** for the formal `τ(n) = [qⁿ] q∏(1 − qᵏ)²⁴`: `τ(n) ≡ σ₁₁(n) (mod 691)`. -/
theorem tau_mod691 {n : ℕ} (hn : n ≠ 0) : (TauCong.tauPS n : ZMod 691) = (σ 11 n : ZMod 691) :=
  Mod691.tau_congruence_mod691 hn (qExpansion_discriminant_coeff n)

/-- Ramanujan's congruence for the computable `RamanujanTau.tau`. -/
theorem tau_computable_mod691 {n : ℕ} (hn : n ≠ 0) : (tau n : ZMod 691) = (σ 11 n : ZMod 691) := by
  rw [tau_eq_tauPS]; exact tau_mod691 hn

/-- `τ(p) ≡ 1 + p¹¹ (mod 691)` for primes `p`, for the formal `τ`. -/
theorem tau_prime_mod691 {p : ℕ} (hp : p.Prime) : (TauCong.tauPS p : ZMod 691) = 1 + (p : ZMod 691) ^ 11 := by
  have hσ : σ 11 p = 1 + p ^ 11 := by
    have h := ArithmeticFunction.sigma_apply_prime_pow (k := 11) (i := 1) hp
    rw [pow_one] at h
    rw [h, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  rw [tau_mod691 hp.ne_zero, hσ]; push_cast; ring

/-- **`1728·q∏(1 − qⁿ)²⁴ = E₄³ − E₆²`** as integer formal power series. -/
theorem discriminant_formal_identity : (1728 : PowerSeries ℤ) * (X * MockTheta5.JTP.qfacInf ^ 24) = p4 ^ 3 - p6 ^ 2 := by
  ext n
  apply Int.cast_injective (α := ℂ)
  have h := Mod691.tau_smul_eq_coeff n
  rw [qExpansion_discriminant_coeff, Mod691.qExpansion_E4_eq, Mod691.qExpansion_E6_eq, ← map_pow, ← map_pow,
    coeff_map, coeff_map] at h
  rw [show (1728 : PowerSeries ℤ) = C (1728 : ℤ) by simp, coeff_C_mul, map_sub]
  push_cast
  simp only [eq_intCast] at h
  exact h

/-- The `TauMod691` hypothesis class is now a theorem. -/
instance tauMod691 : TauMod691 where
  congruence n hn := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 691).mp
    rw [tau_computable_mod691 (by omega), sigma11, ArithmeticFunction.sigma_apply]
    push_cast; rfl

end RamanujanTau.TauModular
