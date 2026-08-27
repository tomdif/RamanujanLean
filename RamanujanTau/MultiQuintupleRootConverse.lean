/-
# Converse arithmetic for reflective index-p ternary lattices

This file isolates the arithmetic converse to the short-root construction.  A rational
Householder reflection with primitive integral normal `w` has denominator `||w||^2`.
If it is integral on the index-`p` congruence lattice, testing it on `p*e_1`, `p*e_2`,
and `p*e_3` forces that denominator to divide `2p`.  For prime odd `p`, every
non-integral-coordinate reflection therefore has normal square norm `p` or `2p`.

Once the denominator contains `p`, preservation of the congruence kernel says that
`x dot w = 0 (mod p)` whenever `x dot v = 0 (mod p)`.  The second theorem proves,
constructively, that `w` is then a projective lift of `v`.

The hypotheses are stated as the exact divisibilities supplied by a lattice-preserving
reflection.  This keeps the result independent of a particular matrix or basis API.
-/
import RamanujanTau.MultiQuintupleRootReflection

namespace Ramanujan.MultiQuintuple

/-- A positive divisor of twice an odd prime is `1`, `2`, `p`, or `2p`. -/
theorem eq_one_or_two_or_prime_or_two_prime_of_dvd
    {p n : ℕ} (hp : Nat.Prime p) (hn : n ∣ 2 * p) :
    n = 1 ∨ n = 2 ∨ n = p ∨ n = 2 * p := by
  obtain ⟨k, hk⟩ := hn
  have hp_dvd : p ∣ n * k := by
    refine ⟨2, ?_⟩
    omega
  rcases (hp.dvd_mul).mp hp_dvd with hpn | hpk
  · obtain ⟨d, rfl⟩ := hpn
    have hdk : d * k = 2 := by
      apply Nat.mul_left_cancel hp.pos
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk.symm
    have hd2 : d ∣ 2 := ⟨k, hdk.symm⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd2 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by simp)))
    · exact Or.inr (Or.inr (Or.inr (by ring)))
  · obtain ⟨d, rfl⟩ := hpk
    have hnd : n * d = 2 := by
      apply Nat.mul_right_cancel hp.pos
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk.symm
    have hn2 : n ∣ 2 := ⟨d, hnd.symm⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hn2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

/-- Testing an integral Householder reflection on the three vectors `p*e_i`
forces its primitive normal square norm to divide `2p`.

`hprimitive` is a Bézout certificate for the squares of the primitive normal;
the three divisibility hypotheses are exactly the diagonal-coordinate integrality
conditions for the reflected `p*e_i`. -/
theorem primitive_reflection_norm_dvd_two_mul
    (p n : ℕ) (w1 w2 w3 b1 b2 b3 : ℤ)
    (hprimitive : b1 * w1 ^ 2 + b2 * w2 ^ 2 + b3 * w3 ^ 2 = 1)
    (h1 : (n : ℤ) ∣ 2 * (p : ℤ) * w1 ^ 2)
    (h2 : (n : ℤ) ∣ 2 * (p : ℤ) * w2 ^ 2)
    (h3 : (n : ℤ) ∣ 2 * (p : ℤ) * w3 ^ 2) :
    n ∣ 2 * p := by
  obtain ⟨q1, hq1⟩ := h1
  obtain ⟨q2, hq2⟩ := h2
  obtain ⟨q3, hq3⟩ := h3
  have hint : (n : ℤ) ∣ (2 * p : ℕ) := by
    refine ⟨b1 * q1 + b2 * q2 + b3 * q3, ?_⟩
    calc
      (2 * p : ℕ) = (2 * (p : ℤ)) * 1 := by norm_num
      _ = (2 * (p : ℤ)) * (b1 * w1 ^ 2 + b2 * w2 ^ 2 + b3 * w3 ^ 2) := by
            rw [hprimitive]
      _ = b1 * (2 * (p : ℤ) * w1 ^ 2)
          + b2 * (2 * (p : ℤ) * w2 ^ 2)
          + b3 * (2 * (p : ℤ) * w3 ^ 2) := by ring
      _ = (n : ℤ) * (b1 * q1 + b2 * q2 + b3 * q3) := by
            rw [hq1, hq2, hq3]
            ring
  exact_mod_cast hint

/-- **Reflection-denominator converse.**  For an odd prime, a primitive reflection
denominator that is not one of the integral signed-coordinate cases `1` and `2`
must be `p` or `2p`. -/
theorem primitive_reflection_norm_eq_prime_or_two_prime
    {p n : ℕ} (hp : Nat.Prime p) (hn1 : n ≠ 1) (hn2 : n ≠ 2)
    (hdiv : n ∣ 2 * p) :
    n = p ∨ n = 2 * p := by
  rcases eq_one_or_two_or_prime_or_two_prime_of_dvd hp hdiv with h | h | h | h
  · exact (hn1 h).elim
  · exact (hn2 h).elim
  · exact Or.inl h
  · exact Or.inr h

/-- Kernel containment for two nonzero linear forms over `Z/pZ` forces their
coefficient vectors to be projectively proportional.  The proof is constructive:
`hcoprime` supplies an inverse of `v1` modulo `p`, and the two test vectors
`(v2,-v1,0)` and `(v3,0,-v1)` recover the remaining coordinates. -/
theorem congruence_kernel_forces_projective_lift
    (p v1 v2 v3 w1 w2 w3 bp bv : ℤ)
    (hcoprime : bp * p + bv * v1 = 1)
    (hkernel : ∀ x1 x2 x3 : ℤ,
      p ∣ ternaryDot v1 v2 v3 x1 x2 x3 →
        p ∣ ternaryDot w1 w2 w3 x1 x2 x3) :
    ∃ lambda a1 a2 a3 : ℤ,
      w1 = lambda * v1 + p * a1
        ∧ w2 = lambda * v2 + p * a2
        ∧ w3 = lambda * v3 + p * a3 := by
  have h12zero : ternaryDot v1 v2 v3 v2 (-v1) 0 = 0 := by
    simp [ternaryDot]
    ring
  have h13zero : ternaryDot v1 v2 v3 v3 0 (-v1) = 0 := by
    simp [ternaryDot]
    ring
  obtain ⟨q12, hq12⟩ := hkernel v2 (-v1) 0 (by rw [h12zero]; exact dvd_zero p)
  obtain ⟨q13, hq13⟩ := hkernel v3 0 (-v1) (by rw [h13zero]; exact dvd_zero p)
  refine ⟨bv * w1, bp * w1, bp * w2 - bv * q12, bp * w3 - bv * q13, ?_⟩
  constructor
  · calc
      w1 = w1 * 1 := by ring
      _ = w1 * (bp * p + bv * v1) := by rw [hcoprime]
      _ = (bv * w1) * v1 + p * (bp * w1) := by ring
  constructor
  · simp only [ternaryDot] at hq12
    calc
      w2 = w2 * 1 := by ring
      _ = w2 * (bp * p + bv * v1) := by rw [hcoprime]
      _ = (bv * w1) * v2 + p * (bp * w2 - bv * q12) := by
            linear_combination -bv * hq12
  · simp only [ternaryDot] at hq13
    calc
      w3 = w3 * 1 := by ring
      _ = w3 * (bp * p + bv * v1) := by rw [hcoprime]
      _ = (bv * w1) * v3 + p * (bp * w3 - bv * q13) := by
            linear_combination -bv * hq13

/-- Packaged arithmetic converse: the integrality tests classify the normal norm,
and congruence-kernel preservation makes that normal a projective lift. -/
theorem reflective_congruence_lattice_has_short_projective_root
    {p n : ℕ} (hp : Nat.Prime p) (hn1 : n ≠ 1) (hn2 : n ≠ 2)
    (v1 v2 v3 w1 w2 w3 b1 b2 b3 bp bv : ℤ)
    (hprimitive : b1 * w1 ^ 2 + b2 * w2 ^ 2 + b3 * w3 ^ 2 = 1)
    (h1 : (n : ℤ) ∣ 2 * (p : ℤ) * w1 ^ 2)
    (h2 : (n : ℤ) ∣ 2 * (p : ℤ) * w2 ^ 2)
    (h3 : (n : ℤ) ∣ 2 * (p : ℤ) * w3 ^ 2)
    (hnorm : ternaryNorm w1 w2 w3 = n)
    (hcoprime : bp * (p : ℤ) + bv * v1 = 1)
    (hkernel : ∀ x1 x2 x3 : ℤ,
      (p : ℤ) ∣ ternaryDot v1 v2 v3 x1 x2 x3 →
        (p : ℤ) ∣ ternaryDot w1 w2 w3 x1 x2 x3) :
    (ternaryNorm w1 w2 w3 = p ∨ ternaryNorm w1 w2 w3 = 2 * p)
      ∧ ∃ lambda a1 a2 a3 : ℤ,
        w1 = lambda * v1 + p * a1
          ∧ w2 = lambda * v2 + p * a2
          ∧ w3 = lambda * v3 + p * a3 := by
  have hdiv := primitive_reflection_norm_dvd_two_mul p n w1 w2 w3 b1 b2 b3
    hprimitive h1 h2 h3
  have hnorm_cases := primitive_reflection_norm_eq_prime_or_two_prime hp hn1 hn2 hdiv
  constructor
  · rcases hnorm_cases with rfl | rfl
    · exact Or.inl (by simpa using hnorm)
    · exact Or.inr (by simpa using hnorm)
  · exact congruence_kernel_forces_projective_lift (p : ℤ)
      v1 v2 v3 w1 w2 w3 bp bv hcoprime hkernel

end Ramanujan.MultiQuintuple
