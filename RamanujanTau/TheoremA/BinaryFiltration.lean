import RamanujanTau.TheoremA.BinaryDivisibility
import RamanujanTau.TheoremA.Series
import Mathlib.Data.Nat.Lattice

/-!
# Minimal representing weight in a fixed weight class

The half-weight filtration is the least n for which a series is represented
by a homogeneous binary polynomial of degree 2n, with n in a specified class
modulo (p−1)/2. This uses the proved integral model and Hasse divisibility;
no characteristic-p filtration axiom is assumed.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

variable {F : Type*} [Field F]

def BinaryRep (f : PowerSeries F) (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) F, BinaryHomogeneous P (2 * n) ∧ binaryEv F P = f

noncomputable def binaryHalfFiltration (p r : ℕ) (f : PowerSeries F) : ℕ :=
  sInf {n : ℕ | n % ((p - 1) / 2) = r % ((p - 1) / 2) ∧ BinaryRep f n}

theorem binaryHalfFiltration_le {p r n : ℕ} {f : PowerSeries F}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) (hf : BinaryRep f n) :
    binaryHalfFiltration p r f ≤ n := Nat.sInf_le ⟨hm, hf⟩

theorem binaryHalfFiltration_spec {p r n : ℕ} {f : PowerSeries F}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) (hf : BinaryRep f n) :
    binaryHalfFiltration p r f % ((p - 1) / 2) = r % ((p - 1) / 2) ∧
      BinaryRep f (binaryHalfFiltration p r f) :=
  by
    change sInf {m : ℕ | m % ((p - 1) / 2) = r % ((p - 1) / 2) ∧ BinaryRep f m} ∈
      {m : ℕ | m % ((p - 1) / 2) = r % ((p - 1) / 2) ∧ BinaryRep f m}
    exact Nat.sInf_mem ⟨n, hm, hf⟩

theorem binaryHalfFiltration_class_congr (p r s : ℕ) (f : PowerSeries F)
    (h : r % ((p - 1) / 2) = s % ((p - 1) / 2)) :
    binaryHalfFiltration p r f = binaryHalfFiltration p s f := by
  simp only [binaryHalfFiltration, h]

variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]

omit hp in
lemma twelve_ne_zero (hp5 : 5 ≤ p) : (12 : F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by omega : p ≠ 2)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by omega : p ≠ 3)
  have he : (12 : F) = 2 ^ 2 * 3 := by ring
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ h2) h3

/-- The theta numerator normalized to have exactly the theta q-expansion. -/
noncomputable def binaryTheta (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  C (12 : F)⁻¹ * binaryThetaNumerator hp5 n P

theorem binaryTheta_homogeneous (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n)) :
    BinaryHomogeneous (binaryTheta hp5 n P) (2 * (n + (p - 1) / 2 + 1)) := by
  have hd := hasse_degree_even hp5
  convert (binaryThetaNumerator_homogeneous hp5 n P hP).C_mul (12 : F)⁻¹ using 1
  omega

theorem binaryEv_theta (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n)) :
    binaryEv F (binaryTheta hp5 n P) = theta (binaryEv F P) := by
  rw [binaryTheta, map_mul, binaryEv_thetaNumerator hp5 n P hP]
  have hc : binaryEv F (C (12 : F)⁻¹) * 12 = (1 : PowerSeries F) := by
    have hev : binaryEv F (C (12 : F)⁻¹) = PowerSeries.C (12 : F)⁻¹ := by
      simp [binaryEv]
    rw [hev]
    rw [← map_ofNat (PowerSeries.C (R := F)) 12, ← map_mul,
      inv_mul_cancel₀ (twelve_ne_zero hp5), map_one]
  rw [← mul_assoc, hc, one_mul]
  rfl

theorem BinaryRep.theta (hp5 : 5 ≤ p) {f : PowerSeries F} {n : ℕ}
    (hf : BinaryRep f n) : BinaryRep (theta f) (n + (p - 1) / 2 + 1) := by
  obtain ⟨P, hP, rfl⟩ := hf
  exact ⟨binaryTheta hp5 n P, binaryTheta_homogeneous hp5 n P hP,
    binaryEv_theta hp5 n P hP⟩

private theorem dvd_C_mul_iff {A P : MvPolynomial (Fin 2) F} {c : F} (hc : c ≠ 0) :
    A ∣ C c * P ↔ A ∣ P := by
  constructor
  · intro hd
    have h := hd.mul_left (C c⁻¹)
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using h
  · exact fun h => h.mul_left _

theorem hasse_dvd_binaryTheta_iff (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n))
    (hk : (2 * n : F) ≠ 0) :
    binaryHasse F p hp5 ∣ binaryTheta hp5 n P ↔ binaryHasse F p hp5 ∣ P := by
  rw [binaryTheta, dvd_C_mul_iff (inv_ne_zero (twelve_ne_zero hp5)),
    hasse_dvd_theta_iff hp5 n P hP hk]

/-- A minimal nonzero representative cannot contain a Hasse factor. -/
theorem not_hasse_dvd_of_minimal (hp5 : 5 ≤ p) {r n : ℕ}
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n))
    (hP0 : P ≠ 0) (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2))
    (hmin : binaryHalfFiltration p r (binaryEv F P) = n) :
    ¬ binaryHasse F p hp5 ∣ P := by
  intro hd
  obtain ⟨hak, Q, hQ, he⟩ := homogeneous_quotient_of_chartT_dvd
    (binaryHasse_homogeneous hp5) hP
    (by rw [binaryHasse_at_infinity]; exact one_ne_zero) hP0 (map_dvd _ hd)
  have hperiod := hasse_degree_even hp5
  have hn : (p - 1) / 2 ≤ n := by omega
  have heven : 2 * n - (p - 1) = 2 * (n - (p - 1) / 2) := by omega
  have hrep : BinaryRep (binaryEv F P) (n - (p - 1) / 2) := by
    refine ⟨Q, by rwa [← heven], ?_⟩
    rw [he, map_mul, binaryEv_hasse, one_mul]
  have hmod : (n - (p - 1) / 2) % ((p - 1) / 2) = r % ((p - 1) / 2) := by
    have hh : (n - (p - 1) / 2 + (p - 1) / 2) % ((p - 1) / 2) =
        (n - (p - 1) / 2) % ((p - 1) / 2) := by simp
    rw [Nat.sub_add_cancel hn] at hh
    exact hh.symm.trans hm
  have hle := binaryHalfFiltration_le hmod hrep
  rw [hmin] at hle
  omega

/-- Conversely, a representative with no Hasse factor is already minimal in its class. -/
theorem minimal_of_not_hasse_dvd (hp5 : 5 ≤ p) {r n : ℕ}
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n))
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2))
    (hnd : ¬ binaryHasse F p hp5 ∣ P) :
    binaryHalfFiltration p r (binaryEv F P) = n := by
  have hrep : BinaryRep (binaryEv F P) n := ⟨P, hP, rfl⟩
  have hle := binaryHalfFiltration_le hm hrep
  obtain ⟨hmod, Q, hQ, he⟩ := binaryHalfFiltration_spec hm hrep
  obtain ⟨m, hn⟩ := (Nat.modEq_iff_exists_eq_add hle).mp (hmod.trans hm.symm)
  by_cases hm0 : m = 0
  · simpa [hm0] using hn.symm
  · exfalso
    apply hnd
    have hw : 2 * binaryHalfFiltration p r (binaryEv F P) + m * (p - 1) = 2 * n := by
      rw [hn]
      have hd := hasse_degree_even hp5
      nlinarith
    have heq := eq_binaryHasse_pow_mul hp5 hQ (by rw [hw]; exact hP) he
    rw [heq]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ hm0) _

omit hp [CharP F p] in
/-- Below one Hasse period, a representative has its displayed weight in its class. -/
theorem binaryHalfFiltration_eq_of_lt {n : ℕ}
    {f : PowerSeries F} (hf : BinaryRep f n) (hn : n < (p - 1) / 2) :
    binaryHalfFiltration p n f = n := by
  have hle := binaryHalfFiltration_le (p := p) rfl hf
  have hmod := (binaryHalfFiltration_spec (p := p) rfl hf).1
  rw [Nat.mod_eq_of_lt (hle.trans_lt hn), Nat.mod_eq_of_lt hn] at hmod
  exact hmod

omit hp in
lemma halfWeight_theta_class {r n : ℕ}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) :
    (n + (p - 1) / 2 + 1) % ((p - 1) / 2) = (r + 1) % ((p - 1) / 2) := by
  simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, hm]

/-- Theta has a representative at most p+1 weight units above the minimum. -/
theorem binaryHalfFiltration_theta_le (hp5 : 5 ≤ p) {r n : ℕ} {f : PowerSeries F}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) (hf : BinaryRep f n) :
    binaryHalfFiltration p (r + 1) (theta f) ≤
      binaryHalfFiltration p r f + (p - 1) / 2 + 1 := by
  obtain ⟨hmod, hrep⟩ := binaryHalfFiltration_spec hm hf
  exact binaryHalfFiltration_le (halfWeight_theta_class hmod) (hrep.theta hp5)

/-- Every theta step has a nonnegative drop which is a multiple of the Hasse period. -/
theorem binaryHalfFiltration_theta_step (hp5 : 5 ≤ p) {r n : ℕ} {f : PowerSeries F}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) (hf : BinaryRep f n) :
    ∃ d : ℕ, binaryHalfFiltration p r f + (p - 1) / 2 + 1 =
      binaryHalfFiltration p (r + 1) (theta f) + ((p - 1) / 2) * d := by
  obtain ⟨hmod, hrep⟩ := binaryHalfFiltration_spec hm hf
  have hnext := halfWeight_theta_class hmod
  have hmnext := (binaryHalfFiltration_spec hnext (hrep.theta hp5)).1
  exact (Nat.modEq_iff_exists_eq_add (binaryHalfFiltration_theta_le hp5 hm hf)).mp
    (hmnext.trans hnext.symm)

/-- Away from weights divisible by p, the minimum increases by exactly p+1. -/
theorem binaryHalfFiltration_theta_eq (hp5 : 5 ≤ p) {r n : ℕ} {f : PowerSeries F}
    (hm : n % ((p - 1) / 2) = r % ((p - 1) / 2)) (hf : BinaryRep f n)
    (hf0 : f ≠ 0) (hk : (2 * binaryHalfFiltration p r f : F) ≠ 0) :
    binaryHalfFiltration p (r + 1) (theta f) =
      binaryHalfFiltration p r f + (p - 1) / 2 + 1 := by
  obtain ⟨hmod, P, hP, he⟩ := binaryHalfFiltration_spec hm hf
  have hP0 : P ≠ 0 := by intro h; apply hf0; rw [← he, h, map_zero]
  have hmin : binaryHalfFiltration p r (binaryEv F P) = binaryHalfFiltration p r f := by rw [he]
  have hnd := not_hasse_dvd_of_minimal hp5 P hP hP0 hmod hmin
  have hndT : ¬ binaryHasse F p hp5 ∣ binaryTheta hp5 (binaryHalfFiltration p r f) P := by
    rwa [hasse_dvd_binaryTheta_iff hp5 _ P hP hk]
  have h := minimal_of_not_hasse_dvd hp5
    (binaryTheta hp5 (binaryHalfFiltration p r f) P) (binaryTheta_homogeneous hp5 _ P hP)
    (halfWeight_theta_class hmod) hndT
  simpa only [binaryEv_theta hp5 _ P hP, he] using h

end RamanujanTau.TheoremA
