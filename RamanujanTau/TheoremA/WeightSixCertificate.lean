import RamanujanTau.TheoremA.LevelSixSturm
import RamanujanTau.TheoremA.ClassicalWeightSix

/-!
# A finite certificate for the actual weight-six operator identity

Three actual cusp forms with the following first nine coefficients suffice.
The coefficient bound proves they span and identifies U₂ and U₃ from finite
data. No spanning assumption or infinite Hecke identity remains in the input.

The three forms and their coefficients are constructed in `EtaQExpansion`
and `WeightSixIdentity`. This file isolates the reusable finite-certificate
implication from that analytic construction.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open UpperHalfPlane PowerSeries

def weightSixCoefficients (i : Fin 3) (n : Fin 9) : ℤ :=
  match i.val, n.val with
  | 0, 0 => 1 | 0, 1 => -6 | 0, 2 => 9 | 0, 3 => 4 | 0, 4 => 6
  | 0, 5 => -54 | 0, 6 => -40 | 0, 7 => 168 | 0, 8 => 81
  | 1, 1 => 1 | 1, 3 => -6 | 1, 5 => 9 | 1, 7 => 4
  | 2, 0 => 1 | 2, 1 => 4 | 2, 2 => -9 | 2, 3 => 16 | 2, 4 => -66
  | 2, 5 => -36 | 2, 6 => 176 | 2, 7 => 64 | 2, 8 => 81
  | _, _ => 0

/-- A finite identification of three actual cusp forms proves the full
classical operator identity. The analytic coefficient bound is unconditional. -/
theorem weightSix_identity_of_coefficient_certificate
    (F : Fin 3 → ClassicalWeightSix)
    (hF : ∀ (i : Fin 3) (n : Fin 9),
      (qExpansion 1 (F i)).coeff (n.val + 1) = (weightSixCoefficients i n : ℂ)) :
    ∀ f : ClassicalWeightSix, classicalWeightSixAnnihilator f = 0 := by
  let E := LevelSix.firstThree
  let A := BadPrime.cuspULinear (k := 6) (p := 2) (by decide : 2 ∣ 6)
  let B := BadPrime.cuspULinear (k := 6) (p := 3) (by decide : 3 ∣ 6)
  have hE (i : Fin 3) : E (F i) =
      ![(weightSixCoefficients i 0 : ℂ), (weightSixCoefficients i 1 : ℂ),
        (weightSixCoefficients i 2 : ℂ)] := by
    ext n
    fin_cases n
    · exact hF i 0
    · exact hF i 1
    · exact hF i 2
  have hA (i : Fin 3) : E (A (F i)) =
      ![(weightSixCoefficients i 1 : ℂ), (weightSixCoefficients i 3 : ℂ),
        (weightSixCoefficients i 5 : ℂ)] := by
    ext n
    change (qExpansion 1 (BadPrime.cuspU (by decide : 2 ∣ 6) (F i))).coeff (n.val + 1) = _
    rw [BadPrime.qExpansion_cuspU, BoylanWebb.coeff_U]
    fin_cases n
    · exact hF i 1
    · exact hF i 3
    · exact hF i 5
  have hB (i : Fin 3) : E (B (F i)) =
      ![(weightSixCoefficients i 2 : ℂ), (weightSixCoefficients i 5 : ℂ),
        (weightSixCoefficients i 8 : ℂ)] := by
    ext n
    change (qExpansion 1 (BadPrime.cuspU (by decide : 3 ∣ 6) (F i))).coeff (n.val + 1) = _
    rw [BadPrime.qExpansion_cuspU, BoylanWebb.coeff_U]
    fin_cases n
    · exact hF i 2
    · exact hF i 5
    · exact hF i 8
  have heinj : Function.Injective E := LevelSix.firstThree_injective
  have ha0 : A (F 0) = (-6 : ℂ) • F 0 + (-32 : ℂ) • F 1 := by
    apply heinj
    rw [map_add, map_smul, map_smul, hA, hE, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have ha1 : A (F 1) = F 0 := by
    apply heinj
    rw [hA, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have ha2 : A (F 2) = (4 : ℂ) • F 2 := by
    apply heinj
    rw [map_smul, hA, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have hb0 : B (F 0) = (9 : ℂ) • F 0 := by
    apply heinj
    rw [map_smul, hB, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have hb1 : B (F 1) = (9 : ℂ) • F 1 := by
    apply heinj
    rw [map_smul, hB, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have hb2 : B (F 2) = (-9 : ℂ) • F 2 := by
    apply heinj
    rw [map_smul, hB, hE]
    ext n; fin_cases n <;> norm_num [weightSixCoefficients, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  have hP : ∀ i : Fin 3, classicalWeightSixAnnihilator (F i) = 0 := by
    intro i
    change B (A (A (F i)) + (6 : ℂ) • A (F i) + (32 : ℂ) • F i) +
      (9 : ℂ) • (A (A (F i)) + (6 : ℂ) • A (F i) + (32 : ℂ) • F i) = 0
    fin_cases i
    · change B (A (A (F 0)) + (6 : ℂ) • A (F 0) + (32 : ℂ) • F 0) +
        (9 : ℂ) • (A (A (F 0)) + (6 : ℂ) • A (F 0) + (32 : ℂ) • F 0) = 0
      simp only [map_add, map_smul, ha0, ha1, hb0, hb1]
      module
    · change B (A (A (F 1)) + (6 : ℂ) • A (F 1) + (32 : ℂ) • F 1) +
        (9 : ℂ) • (A (A (F 1)) + (6 : ℂ) • A (F 1) + (32 : ℂ) • F 1) = 0
      simp only [map_add, map_smul, ha0, ha1, hb0, hb1]
      module
    · change B (A (A (F 2)) + (6 : ℂ) • A (F 2) + (32 : ℂ) • F 2) +
        (9 : ℂ) • (A (A (F 2)) + (6 : ℂ) • A (F 2) + (32 : ℂ) • F 2) = 0
      simp only [map_add, map_smul, ha2, hb2]
      module
  intro f
  let a := E f 0
  let b := E f 1
  let c := E f 2
  let x := (a + c / 9) / 2
  let y := b + a + 5 * c / 9
  let z := (a - c / 9) / 2
  have hs : f = x • F 0 + y • F 1 + z • F 2 := by
    apply heinj
    rw [map_add, map_add, map_smul, map_smul, map_smul, hE, hE, hE]
    ext n
    fin_cases n <;>
      norm_num [weightSixCoefficients, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        x, y, z, a, b, c] <;> (first | rfl | ring_nf <;> rfl)
  rw [hs, map_add, map_add, map_smul, map_smul, map_smul, hP, hP, hP]
  simp

/-- The finite classical certificate also certifies the relation after
coefficient reduction, without an integral old/new splitting. -/
theorem IsReducedCuspExpansion.weightSix_annihilator_of_certificate
    {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* ℂ} {ψ : R →+* S}
    (hφ : Function.Injective φ) (F : Fin 3 → ClassicalWeightSix)
    (hF : ∀ (i : Fin 3) (n : Fin 9),
      (qExpansion 1 (F i)).coeff (n.val + 1) = (weightSixCoefficients i n : ℂ))
    {a : PowerSeries S} (ha : IsReducedCuspExpansion φ ψ 6 6 a) :
    weightSixAnnihilator a = 0 :=
  ha.weightSix_annihilator hφ (weightSix_identity_of_coefficient_certificate F hF)

end RamanujanTau.TheoremA
