/-
# The Tate-curve side of `U_p`: the roots-of-unity sum

On the Tate curve `Tate(q)` the `p` non-canonical order-`p` subgroups are `⟨ζ^k q^{1/p}⟩`, with
quotients `Tate(ζ^k t)`, `t = q^{1/p}`. For a form with q-expansion `F(q) = Σ c_n q^n`,
`Σ_{C ≠ H} f(Tate/C) = Σ_k F(ζ^k t)`. The identity proved here is

  `Σ_{k < p} F(ζ^k t) = p · Σ_n c_{pn} t^{pn} = p · (U_p F)(t^p) = p · (U_p F)(q)`

(`sum_rescale_coeff`, `sum_rescale_eq`), for `ζ` a primitive `p`-th root of unity in a domain.
This is the formal q-series content of "geometric `U` = coefficient extraction `U_p`" on the Tate
curve; the q-expansion principle that transfers it to all test curves is not formalized.
-/
import Mathlib

set_option autoImplicit false

namespace UpContraction
open PowerSeries

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `U_p` on power series: `Σ c_n q^n ↦ Σ c_{pn} q^n`. -/
noncomputable def Up (p : ℕ) (F : PowerSeries R) : PowerSeries R := PowerSeries.mk fun n => coeff (p * n) F

/-- **Roots-of-unity sum**, coefficientwise: `[t^m] Σ_k F(ζ^k t) = p·c_m` if `p ∣ m`, else `0`. -/
theorem sum_rescale_coeff {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (F : PowerSeries R) (m : ℕ) :
    coeff m (∑ k ∈ Finset.range p, rescale (ζ ^ k) F) =
      if p ∣ m then (p : R) * coeff m F else 0 := by
  rw [map_sum]
  simp only [coeff_rescale]
  rw [← Finset.sum_mul]
  have hs : ∑ k ∈ Finset.range p, (ζ ^ k) ^ m = ∑ k ∈ Finset.range p, (ζ ^ m) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hs]
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := hm
    have h1 : ζ ^ (p * n) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [h1]
  · have hcop : m.Coprime p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))
    have hz : IsPrimitiveRoot (ζ ^ m) p := hζ.pow_of_coprime m hcop
    rw [hz.geom_sum_eq_zero hp.one_lt, zero_mul]

/-- **Roots-of-unity sum**: `Σ_{k<p} F(ζ^k t) = p · (U_p F)(t^p)`. -/
theorem sum_rescale_eq {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (F : PowerSeries R) :
    ∑ k ∈ Finset.range p, rescale (ζ ^ k) F =
      C (p : R) * PowerSeries.mk fun m => if p ∣ m then coeff (p * (m / p)) (F) else 0 := by
  ext m
  rw [sum_rescale_coeff hp hζ F m, coeff_C_mul, coeff_mk]
  split_ifs with hm
  · rw [Nat.mul_div_cancel' hm]
  · rw [mul_zero]

/-- The same, with `U_p`: the `T^{pn}` coefficient of `Σ_k F(ζ^k t)` is `p · [q^n] U_p F`, and the
other coefficients vanish. -/
theorem sum_rescale_Up {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (F : PowerSeries R) (n : ℕ) :
    coeff (p * n) (∑ k ∈ Finset.range p, rescale (ζ ^ k) F) = (p : R) * coeff n (Up p F) := by
  rw [sum_rescale_coeff hp hζ F, if_pos (dvd_mul_right p n), Up, coeff_mk]

end UpContraction
