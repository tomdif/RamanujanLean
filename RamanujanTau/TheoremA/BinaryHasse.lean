import RamanujanTau.TheoremA.BinaryPullback
import RamanujanTau.Igusa.Charts

/-!
# The Hasse invariant in the binary level-six model

The level-one Hasse invariant and its Serre companion pull back to homogeneous
binary polynomials with q-expansions 1 and E₂. Equality of expansions in a fixed
weight class is exactly multiplication by the appropriate Hasse power.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

noncomputable def binaryHasse (F : Type*) [Field F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) F :=
  binaryPullback F (Igusa.AF F p hp5)

noncomputable def binaryHasseCompanion (F : Type*) [Field F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (hp5 : 5 ≤ p) : MvPolynomial (Fin 2) F :=
  binaryPullback F (Igusa.BF F p hp5)

theorem binaryHasse_homogeneous (hp5 : 5 ≤ p) :
    BinaryHomogeneous (binaryHasse F p hp5) (p - 1) :=
  binaryPullback_homogeneous (Igusa.iso_AF hp5)

theorem binaryHasseCompanion_homogeneous (hp5 : 5 ≤ p) :
    BinaryHomogeneous (binaryHasseCompanion F p hp5) (p + 1) :=
  binaryPullback_homogeneous (Igusa.iso_BF hp5)

theorem binaryEv_hasse (hp5 : 5 ≤ p) : binaryEv F (binaryHasse F p hp5) = 1 := by
  rw [binaryHasse, binaryEv_pullback, Igusa.AF, ← ModP.map_ev, ModP.ev_hasseBar, map_one]

theorem binaryEv_hasseCompanion (hp5 : 5 ≤ p) :
    binaryEv F (binaryHasseCompanion F p hp5) = Igusa.E2 F := by
  rw [binaryHasseCompanion, binaryEv_pullback, Igusa.BF, ← ModP.map_ev,
    Igusa.ev_hasseB RamanujanODEProof.ramanujanODE, Igusa.map_E2]

theorem binaryHasse_ne_zero (hp5 : 5 ≤ p) : binaryHasse F p hp5 ≠ 0 := by
  intro h
  have he := binaryEv_hasse (F := F) hp5
  rw [h, map_zero] at he
  exact zero_ne_one he

lemma hasse_degree_even (hp5 : 5 ≤ p) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨n, hn⟩ := hp.out.even_sub_one (by omega)
  omega

/-- The companion is the actual integral Serre derivative in the level-six model. -/
theorem binarySerre_hasse (hp5 : 5 ≤ p) :
    binarySerre ((p - 1) / 2) (binaryHasse F p hp5) =
      binaryHasseCompanion F p hp5 := by
  have hd := hasse_degree_even hp5
  have hd' : 2 * ((p - 1) / 2 + 1) = p + 1 := by omega
  apply binaryEv_injective_on_homogeneous ((p - 1) / 2 + 1)
    (binarySerre_homogeneous _ _) (by rw [hd']; exact binaryHasseCompanion_homogeneous hp5)
  rw [binaryEv_binarySerre _ _ (by rw [hd]; exact binaryHasse_homogeneous hp5),
    hd, binaryEv_hasse, binaryEv_hasseCompanion, serreSeries, Igusa.theta_one,
    mul_zero, mul_one]
  have hc : ((p - 1 : ℕ) : PowerSeries F) = -1 := by
    have hf : ((p - 1 : ℕ) : F) = -1 := by
      rw [Nat.cast_sub (by omega), CharP.cast_eq_zero _ p, Nat.cast_one, zero_sub]
    simpa using congrArg (PowerSeries.C (R := F)) hf
  simp only [Int.cast_natCast, hc, neg_one_mul, sub_neg_eq_add, zero_add]

/-- Within one weight class, an identical expansion is exactly a Hasse multiple. -/
theorem eq_binaryHasse_pow_mul (hp5 : 5 ≤ p) {n m : ℕ}
    {P Q : MvPolynomial (Fin 2) F}
    (hP : BinaryHomogeneous P (2 * n))
    (hQ : BinaryHomogeneous Q (2 * n + m * (p - 1)))
    (he : binaryEv F P = binaryEv F Q) : Q = binaryHasse F p hp5 ^ m * P := by
  have hd : 2 * (n + m * ((p - 1) / 2)) = 2 * n + m * (p - 1) := by
    calc
      _ = 2 * n + m * (2 * ((p - 1) / 2)) := by ring
      _ = _ := by rw [hasse_degree_even hp5]
  apply binaryEv_injective_on_homogeneous (n + m * ((p - 1) / 2))
    (by rw [hd]; exact hQ)
  · rw [hd]
    have hh := ((binaryHasse_homogeneous (F := F) hp5).pow m).mul hP
    convert hh using 1
    simp only [smul_eq_mul]
    omega
  · rw [map_mul, map_pow, binaryEv_hasse, one_pow, one_mul]
    exact he.symm

theorem binaryEv_eq_iff_hasse_pow_mul (hp5 : 5 ≤ p) {n m : ℕ}
    {P Q : MvPolynomial (Fin 2) F}
    (hP : BinaryHomogeneous P (2 * n))
    (hQ : BinaryHomogeneous Q (2 * n + m * (p - 1))) :
    binaryEv F P = binaryEv F Q ↔ Q = binaryHasse F p hp5 ^ m * P := by
  constructor
  · exact eq_binaryHasse_pow_mul hp5 hP hQ
  · intro h
    rw [h, map_mul, map_pow, binaryEv_hasse, one_pow, one_mul]

end RamanujanTau.TheoremA
