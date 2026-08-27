/-
# A three-quintuple-product vanishing target at p = 7

The exact coefficient scan discovers

  Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7)

with zero coefficient progressions `7n+3`, `7n+5`, and `7n+6`.  Multiplying the five
q-Pochhammer factors in each `Q` and sorting residue classes gives the factorization

  phi(-q) * (q^7;q^7)_inf * (q^14;q^14)_inf.

This file proves the factor collection from the paper's five-factor definition of `Q`, identifies
the triple with `p7TripleFactorized`, and proves all three coefficient-vanishing progressions.
No `sorry`.
-/
import RamanujanTau.MockTheta5RamanujanTheta
import RamanujanTau.MockTheta5PartitionCongruence7
import RamanujanTau.MultiQuintupleVanishing
import RamanujanTau.MultiQuintuplePochhammer

namespace Ramanujan.MultiQuintuple
open PowerSeries
open MockTheta5.JTP
open MockTheta5.Bailey

/-- Substitution `q |-> q^14`. -/
noncomputable def E14 : PowerSeries ℤ →+* PowerSeries ℤ :=
  (PowerSeries.expand 14 (by norm_num)).toRingHom

/-- The product supported on multiples of seven in the factorized `p=7` triple. -/
noncomputable def p7Tail : PowerSeries ℤ := E7 qfacInf * E14 qfacInf

/-- Factorized target for `Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7)`. -/
noncomputable def p7TripleFactorized : PowerSeries ℤ := phiNeg * p7Tail

private def residues7 : List (ℕ × ℕ) :=
  [(1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7)]

private def oddResidues14 : List (ℕ × ℕ) :=
  [(1, 14), (3, 14), (5, 14), (7, 14), (9, 14), (11, 14), (13, 14)]

private lemma residues7_valid : ∀ factor ∈ residues7, 0 < factor.1 ∧ 0 < factor.2 := by
  intro factor hfactor
  simp [residues7] at hfactor
  rcases hfactor with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma oddResidues14_valid : ∀ factor ∈ oddResidues14, 0 < factor.1 ∧ 0 < factor.2 := by
  intro factor hfactor
  simp [oddResidues14] at hfactor
  rcases hfactor with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Seven residue-class blocks reassemble the first `7N` Euler factors. -/
private lemma residues7_finite (N : ℕ) :
    pochhammerFinite 1 7 N * pochhammerFinite 2 7 N * pochhammerFinite 3 7 N
      * pochhammerFinite 4 7 N * pochhammerFinite 5 7 N * pochhammerFinite 6 7 N
      * pochhammerFinite 7 7 N = qfac (7 * N)
    := by
  induction N with
  | zero => simp [pochhammerFinite, qfac]
  | succ N ih =>
      have hq : qfac (7 * (N + 1)) = qfac (7 * N) * (1 - X ^ (7 * N + 1))
          * (1 - X ^ (7 * N + 2)) * (1 - X ^ (7 * N + 3))
          * (1 - X ^ (7 * N + 4)) * (1 - X ^ (7 * N + 5))
          * (1 - X ^ (7 * N + 6)) * (1 - X ^ (7 * N + 7)) := by
        rw [show 7 * (N + 1) = 7 * N + 7 by ring,
          show 7 * N + 7 = (7 * N + 6) + 1 by ring, qfac_succ,
          show 7 * N + 6 = (7 * N + 5) + 1 by ring, qfac_succ,
          show 7 * N + 5 = (7 * N + 4) + 1 by ring, qfac_succ,
          show 7 * N + 4 = (7 * N + 3) + 1 by ring, qfac_succ,
          show 7 * N + 3 = (7 * N + 2) + 1 by ring, qfac_succ,
          show 7 * N + 2 = (7 * N + 1) + 1 by ring, qfac_succ,
          show 7 * N + 1 = 7 * N + 1 by ring, qfac_succ]
      rw [pochhammerFinite_succ, pochhammerFinite_succ, pochhammerFinite_succ,
        pochhammerFinite_succ, pochhammerFinite_succ, pochhammerFinite_succ,
        pochhammerFinite_succ, hq, ← ih]
      ring

/-- Seven odd residue-class blocks reassemble the first `7N` odd factors. -/
private lemma oddResidues14_finite (N : ℕ) :
    pochhammerFinite 1 14 N * pochhammerFinite 3 14 N * pochhammerFinite 5 14 N
      * pochhammerFinite 7 14 N * pochhammerFinite 9 14 N * pochhammerFinite 11 14 N
      * pochhammerFinite 13 14 N = oddFac (7 * N)
    := by
  induction N with
  | zero => simp [pochhammerFinite, oddFac]
  | succ N ih =>
      have hodd : oddFac (7 * (N + 1)) = oddFac (7 * N) * (1 - X ^ (14 * N + 1))
          * (1 - X ^ (14 * N + 3)) * (1 - X ^ (14 * N + 5))
          * (1 - X ^ (14 * N + 7)) * (1 - X ^ (14 * N + 9))
          * (1 - X ^ (14 * N + 11)) * (1 - X ^ (14 * N + 13)) := by
        rw [show 7 * (N + 1) = 7 * N + 7 by ring,
          show 7 * N + 7 = (7 * N + 6) + 1 by ring, oddFac_succ,
          show 7 * N + 6 = (7 * N + 5) + 1 by ring, oddFac_succ,
          show 7 * N + 5 = (7 * N + 4) + 1 by ring, oddFac_succ,
          show 7 * N + 4 = (7 * N + 3) + 1 by ring, oddFac_succ,
          show 7 * N + 3 = (7 * N + 2) + 1 by ring, oddFac_succ,
          show 7 * N + 2 = (7 * N + 1) + 1 by ring, oddFac_succ,
          show 7 * N + 1 = 7 * N + 1 by ring, oddFac_succ]
        ring_nf
      rw [pochhammerFinite_succ, pochhammerFinite_succ, pochhammerFinite_succ,
        pochhammerFinite_succ, pochhammerFinite_succ, pochhammerFinite_succ,
        pochhammerFinite_succ, hodd, ← ih]
      ring

/-- Splitting multiples of seven by parity. -/
private lemma multiples7_split_finite (N : ℕ) :
    pochhammerFinite 7 14 N * pochhammerFinite 14 14 N
      = pochhammerFinite 7 7 (2 * N) := by
  induction N with
  | zero => simp [pochhammerFinite]
  | succ N ih =>
      rw [pochhammerFinite_succ, pochhammerFinite_succ,
        show 2 * (N + 1) = (2 * N + 1) + 1 by ring,
        pochhammerFinite_succ, pochhammerFinite_succ, ← ih]
      ring

/-- Infinite residue-class reassembly modulo seven. -/
lemma residues7_reassembly :
    pochhammerInf 1 7 * pochhammerInf 2 7 * pochhammerInf 3 7
        * pochhammerInf 4 7 * pochhammerInf 5 7 * pochhammerInf 6 7
        * pochhammerInf 7 7 = qfacInf := by
  have hlist : pochhammerProductInf residues7 = qfacInf := by
    ext k
    rw [coeff_pochhammerProductInf residues7_valid (le_refl (k + 1))]
    rw [show pochhammerProductFinite residues7 (k + 1)
          = pochhammerFinite 1 7 (k + 1) * pochhammerFinite 2 7 (k + 1)
              * pochhammerFinite 3 7 (k + 1) * pochhammerFinite 4 7 (k + 1)
              * pochhammerFinite 5 7 (k + 1) * pochhammerFinite 6 7 (k + 1)
              * pochhammerFinite 7 7 (k + 1) from by
            simp [pochhammerProductFinite, residues7]; ring,
      residues7_finite, ← coeff_qfacInf (show k + 1 ≤ 7 * (k + 1) by omega)]
  calc
    pochhammerInf 1 7 * pochhammerInf 2 7 * pochhammerInf 3 7
          * pochhammerInf 4 7 * pochhammerInf 5 7 * pochhammerInf 6 7
          * pochhammerInf 7 7
        = pochhammerProductInf residues7 := by
            simp [pochhammerProductInf, residues7]; ring
    _ = qfacInf := hlist

/-- Infinite reassembly of the odd residue classes modulo fourteen. -/
lemma oddResidues14_reassembly :
    pochhammerInf 1 14 * pochhammerInf 3 14 * pochhammerInf 5 14
        * pochhammerInf 7 14 * pochhammerInf 9 14 * pochhammerInf 11 14
        * pochhammerInf 13 14 = oddPochInf := by
  have hlist : pochhammerProductInf oddResidues14 = oddPochInf := by
    ext k
    rw [coeff_pochhammerProductInf oddResidues14_valid (le_refl (k + 1))]
    rw [show pochhammerProductFinite oddResidues14 (k + 1)
          = pochhammerFinite 1 14 (k + 1) * pochhammerFinite 3 14 (k + 1)
              * pochhammerFinite 5 14 (k + 1) * pochhammerFinite 7 14 (k + 1)
              * pochhammerFinite 9 14 (k + 1) * pochhammerFinite 11 14 (k + 1)
              * pochhammerFinite 13 14 (k + 1) from by
            simp [pochhammerProductFinite, oddResidues14]; ring,
      oddResidues14_finite, ← coeff_oddPochInf (show k + 1 ≤ 7 * (k + 1) by omega)]
  calc
    pochhammerInf 1 14 * pochhammerInf 3 14 * pochhammerInf 5 14
          * pochhammerInf 7 14 * pochhammerInf 9 14 * pochhammerInf 11 14
          * pochhammerInf 13 14
        = pochhammerProductInf oddResidues14 := by
            simp [pochhammerProductInf, oddResidues14]; ring
    _ = oddPochInf := hlist

/-- Infinite split of the multiples of seven into odd and even multiples. -/
lemma multiples7_split :
    pochhammerInf 7 14 * pochhammerInf 14 14 = pochhammerInf 7 7 := by
  rw [show pochhammerInf 7 14 * pochhammerInf 14 14
      = pochhammerProductInf [(7, 14), (14, 14)] from by
        simp [pochhammerProductInf]]
  ext k
  have hvalid : ∀ factor ∈ ([(7, 14), (14, 14)] : List (ℕ × ℕ)),
      0 < factor.1 ∧ 0 < factor.2 := by
    intro factor hfactor
    simp at hfactor
    rcases hfactor with rfl | rfl <;> norm_num
  rw [coeff_pochhammerProductInf hvalid (le_refl (k + 1)),
    show pochhammerProductFinite [(7, 14), (14, 14)] (k + 1)
      = pochhammerFinite 7 14 (k + 1) * pochhammerFinite 14 14 (k + 1) from by
        simp [pochhammerProductFinite],
    multiples7_split_finite,
    ← coeff_pochhammerInf (by norm_num) (by norm_num)
      (show k + 1 ≤ 2 * (k + 1) by omega)]

lemma coeff_E7 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (E7 f) = if 7 ∣ n then coeff (n / 7) f else 0 := by
  change coeff n (PowerSeries.expand 7 (by norm_num) f) = _
  rw [PowerSeries.coeff_expand]

lemma coeff_E14 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (E14 f) = if 14 ∣ n then coeff (n / 14) f else 0 := by
  change coeff n (PowerSeries.expand 14 (by norm_num) f) = _
  rw [PowerSeries.coeff_expand]

/-- The diagonal Pochhammer is exactly the expanded Euler product at base `q^7`. -/
lemma pochhammerInf_7_7 : pochhammerInf 7 7 = E7 qfacInf := by
  ext k
  rw [coeff_pochhammerInf (by norm_num) (by norm_num) (le_refl (k + 1)),
    pochhammerFinite_diag 7 (k + 1) (by norm_num)]
  change coeff k (E7 (qfac (k + 1))) = coeff k (E7 qfacInf)
  rw [coeff_E7, coeff_E7]
  split_ifs with hk
  · rw [coeff_qfacInf (show k / 7 + 1 ≤ k + 1 by omega)]
  · rfl

/-- The diagonal Pochhammer is exactly the expanded Euler product at base `q^14`. -/
lemma pochhammerInf_14_14 : pochhammerInf 14 14 = E14 qfacInf := by
  ext k
  rw [coeff_pochhammerInf (by norm_num) (by norm_num) (le_refl (k + 1)),
    pochhammerFinite_diag 14 (k + 1) (by norm_num)]
  change coeff k (E14 (qfac (k + 1))) = coeff k (E14 qfacInf)
  rw [coeff_E14, coeff_E14]
  split_ifs with hk
  · rw [coeff_qfacInf (show k / 14 + 1 ≤ k + 1 by omega)]
  · rfl

/-- **The complete product bridge at `p=7`.**  The product built from the paper's
five-factor definition of each specialized quintuple product is the factorized theta target. -/
theorem quintupleSpecialized_p7_triple_eq_factorized :
    quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3
      = p7TripleFactorized := by
  apply mul_right_cancel₀ (isUnit_pochhammerInf (by norm_num : 0 < 7) (by norm_num : 0 < 14)).ne_zero
  rw [p7TripleFactorized, p7Tail, ← pochhammerInf_7_7, ← pochhammerInf_14_14]
  calc
    quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3
          * pochhammerInf 7 14
        = (pochhammerInf 1 7 * pochhammerInf 2 7 * pochhammerInf 3 7
              * pochhammerInf 4 7 * pochhammerInf 5 7 * pochhammerInf 6 7
              * pochhammerInf 7 7)
            * pochhammerInf 7 7 ^ 2
            * (pochhammerInf 1 14 * pochhammerInf 3 14 * pochhammerInf 5 14
              * pochhammerInf 7 14 * pochhammerInf 9 14 * pochhammerInf 11 14
              * pochhammerInf 13 14) := by
          simp [quintupleSpecialized, pochhammerProductInf]
          ring
    _ = qfacInf * pochhammerInf 7 7 ^ 2 * oddPochInf := by
          rw [residues7_reassembly, oddResidues14_reassembly]
    _ = phiNeg * pochhammerInf 7 7 ^ 2 := by
          rw [← qfac2Inf_mul_oddPochInf, phiNeg_product]
          ring
    _ = (phiNeg * (pochhammerInf 7 7 * pochhammerInf 14 14))
          * pochhammerInf 7 14 := by
          rw [← multiples7_split]
          ring

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

/-- **Three-quintuple-product vanishing at `p=7`.**  For the actual product-side
specializations `Q(q,q^7)Q(q^2,q^7)Q(q^3,q^7)`, every quadratic-nonresidue progression
has zero coefficient. -/
theorem coeff_quintupleSpecialized_p7_zero (n r : ℕ)
    (hr : r = 3 ∨ r = 5 ∨ r = 6) :
    coeff (7 * n + r)
      (quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3) = 0 := by
  rw [quintupleSpecialized_p7_triple_eq_factorized]
  exact coeff_p7TripleFactorized_zero n r hr

theorem quintuple_product_p7_vanishing_7n3 (n : ℕ) :
    coeff (7 * n + 3)
      (quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3) = 0 :=
  coeff_quintupleSpecialized_p7_zero n 3 (Or.inl rfl)

theorem quintuple_product_p7_vanishing_7n5 (n : ℕ) :
    coeff (7 * n + 5)
      (quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3) = 0 :=
  coeff_quintupleSpecialized_p7_zero n 5 (Or.inr (Or.inl rfl))

theorem quintuple_product_p7_vanishing_7n6 (n : ℕ) :
    coeff (7 * n + 6)
      (quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3) = 0 :=
  coeff_quintupleSpecialized_p7_zero n 6 (Or.inr (Or.inr rfl))

end Ramanujan.MultiQuintuple
