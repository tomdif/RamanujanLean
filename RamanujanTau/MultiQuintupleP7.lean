/-
# A three-quintuple-product vanishing target at p = 7

The exact coefficient scan discovers

  Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7)

with zero coefficient progressions `7n+3`, `7n+5`, and `7n+6`.  Multiplying the five
q-Pochhammer factors in each `Q` and sorting residue classes gives the factorization

  phi(-q) * (q^7;q^7)_inf * (q^14;q^14)_inf.

This file proves the coefficient-vanishing theorem for that factorized target.  The remaining
interface lemma is to connect the repo's eventual one-variable specialization of the quintuple
product identity to `p7TripleFactorized`; the arithmetic/support theorem itself is complete.
No `sorry`.
-/
import RamanujanTau.MockTheta5RamanujanTheta
import RamanujanTau.MockTheta5PartitionCongruence7
import RamanujanTau.MultiQuintupleVanishing

namespace Ramanujan.MultiQuintuple
open PowerSeries
open MockTheta5.JTP

/-- Substitution `q |-> q^14`. -/
noncomputable def E14 : PowerSeries ℤ →+* PowerSeries ℤ :=
  (PowerSeries.expand 14 (by norm_num)).toRingHom

/-- The product supported on multiples of seven in the factorized `p=7` triple. -/
noncomputable def p7Tail : PowerSeries ℤ := E7 qfacInf * E14 qfacInf

/-- Factorized target for `Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7)`. -/
noncomputable def p7TripleFactorized : PowerSeries ℤ := phiNeg * p7Tail

lemma coeff_E7 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (E7 f) = if 7 ∣ n then coeff (n / 7) f else 0 := by
  change coeff n (PowerSeries.expand 7 (by norm_num) f) = _
  rw [PowerSeries.coeff_expand]

lemma coeff_E14 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (E14 f) = if 14 ∣ n then coeff (n / 14) f else 0 := by
  change coeff n (PowerSeries.expand 14 (by norm_num) f) = _
  rw [PowerSeries.coeff_expand]

/-- A square modulo seven is one of `0,1,2,4`. -/
lemma square_mod_seven (x : ℕ) :
    x ^ 2 % 7 = 0 ∨ x ^ 2 % 7 = 1 ∨ x ^ 2 % 7 = 2 ∨ x ^ 2 % 7 = 4 := by
  rw [pow_two, Nat.mul_mod]
  have hx : x % 7 < 7 := Nat.mod_lt x (by norm_num)
  interval_cases h : x % 7 <;> norm_num [h]

/-- The alternating square theta has no coefficients in the quadratic nonresidues modulo seven. -/
lemma coeff_phiNeg_zero_of_nonresidue {a : ℕ}
    (ha : a % 7 = 3 ∨ a % 7 = 5 ∨ a % 7 = 6) : coeff a phiNeg = 0 := by
  rw [phiNeg, MockTheta5.JTP.coeff_map_evm1_bilateralTheta]
  have ha0 : a ≠ 0 := by omega
  rw [if_neg ha0, zero_add]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg]
  intro ham
  have hsquare := square_mod_seven (m + 1)
  rw [ham] at ha
  omega

/-- The tail of the factorized target is supported only on multiples of seven. -/
lemma coeff_p7Tail_zero {b : ℕ} (hb : ¬7 ∣ b) : coeff b p7Tail = 0 := by
  rw [p7Tail, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pair hpair => ?_
  obtain ⟨x, y⟩ := pair
  have hxy : x + y = b := Finset.mem_antidiagonal.mp hpair
  by_cases hx : 7 ∣ x
  · have hy : ¬14 ∣ y := by
      intro hy14
      have hy7 : 7 ∣ y := dvd_trans (by norm_num : 7 ∣ 14) hy14
      exact hb (hxy ▸ dvd_add hx hy7)
    rw [coeff_E14, if_neg hy, mul_zero]
  · rw [coeff_E7, if_neg hx, zero_mul]

/-- The factorized `p=7` triple vanishes in every quadratic nonresidue class. -/
theorem coeff_p7TripleFactorized_zero (n r : ℕ)
    (hr : r = 3 ∨ r = 5 ∨ r = 6) : coeff (7 * n + r) p7TripleFactorized = 0 := by
  rw [p7TripleFactorized, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pair hpair => ?_
  obtain ⟨a, b⟩ := pair
  have hab : a + b = 7 * n + r := Finset.mem_antidiagonal.mp hpair
  by_cases hb : 7 ∣ b
  · obtain ⟨k, hk⟩ := hb
    have ha : a % 7 = 3 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      rcases hr with rfl | rfl | rfl <;> omega
    rw [coeff_phiNeg_zero_of_nonresidue ha, zero_mul]
  · rw [coeff_p7Tail_zero hb, mul_zero]

theorem coeff_p7TripleFactorized_7n3 (n : ℕ) :
    coeff (7 * n + 3) p7TripleFactorized = 0 :=
  coeff_p7TripleFactorized_zero n 3 (Or.inl rfl)

theorem coeff_p7TripleFactorized_7n5 (n : ℕ) :
    coeff (7 * n + 5) p7TripleFactorized = 0 :=
  coeff_p7TripleFactorized_zero n 5 (Or.inr (Or.inl rfl))

theorem coeff_p7TripleFactorized_7n6 (n : ℕ) :
    coeff (7 * n + 6) p7TripleFactorized = 0 :=
  coeff_p7TripleFactorized_zero n 6 (Or.inr (Or.inr rfl))

end Ramanujan.MultiQuintuple
