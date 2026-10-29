import RamanujanTau.TheoremA.BinaryHasse

/-! Coefficient extension for the binary Eisenstein and Hasse polynomials. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

theorem map_binaryE4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    MvPolynomial.map φ (binaryE4 R) = binaryE4 S := by
  simp [binaryE4_eq]

theorem map_binaryE6 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    MvPolynomial.map φ (binaryE6 R) = binaryE6 S := by
  simp [binaryE6_eq]

theorem map_binaryPullback {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (binaryPullback R P) = binaryPullback S (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [binaryPullback]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    fin_cases i <;> simp [binaryPullback, map_binaryE4, map_binaryE6]

theorem map_binaryHasse {F K : Type*} [Field F] [Field K] {p : ℕ}
    [Fact p.Prime] [CharP F p] [CharP K p] (φ : F →+* K) (hp5 : 5 ≤ p) :
    MvPolynomial.map φ (binaryHasse F p hp5) = binaryHasse K p hp5 := by
  rw [binaryHasse, map_binaryPullback, Igusa.AF, MvPolynomial.map_map, binaryHasse, Igusa.AF]
  have hc : φ.comp (ZMod.castHom (dvd_refl p) F) = ZMod.castHom (dvd_refl p) K :=
    Subsingleton.elim _ _
  rw [hc]

theorem map_binaryHasseCompanion {F K : Type*} [Field F] [Field K] {p : ℕ}
    [Fact p.Prime] [CharP F p] [CharP K p] (φ : F →+* K) (hp5 : 5 ≤ p) :
    MvPolynomial.map φ (binaryHasseCompanion F p hp5) = binaryHasseCompanion K p hp5 := by
  rw [binaryHasseCompanion, map_binaryPullback, Igusa.BF, MvPolynomial.map_map,
    binaryHasseCompanion, Igusa.BF]
  have hc : φ.comp (ZMod.castHom (dvd_refl p) F) = ZMod.castHom (dvd_refl p) K :=
    Subsingleton.elim _ _
  rw [hc]

theorem aeval_chartT {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : MvPolynomial (Fin 2) F) (t : K) :
    Polynomial.aeval t (Igusa.chartT P) =
      eval ![t, 1] (MvPolynomial.map (algebraMap F K) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Igusa.chartT]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    fin_cases i <;> simp [Igusa.chartT]

theorem aeval_chartS {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : MvPolynomial (Fin 2) F) (t : K) :
    Polynomial.aeval t (Igusa.chartS P) =
      eval ![1, t] (MvPolynomial.map (algebraMap F K) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Igusa.chartS]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    fin_cases i <;> simp [Igusa.chartS]

end RamanujanTau.TheoremA
