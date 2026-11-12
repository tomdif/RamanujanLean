import RamanujanTau.MultiQuintupleFourPrimeIntegral

/-! Lift the finite modulo-nine generator certificates to arbitrary integers. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourPrimeResidue (m : ℤ) : Fin 9 := ⟨(m : ZMod 9).val,ZMod.val_lt _⟩

theorem fourPrimeResidue_cast9 (m : ℤ) :
    ((fourPrimeResidue m).val : ZMod 9)=(m : ZMod 9) := by
  simpa only [fourPrimeResidue] using ZMod.natCast_zmod_val (m : ZMod 9)

theorem fourPrimeResidue_cast3 (m : ℤ) :
    ((fourPrimeResidue m).val : ZMod 3)=(m : ZMod 3) := by
  have h := congrArg (ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)) (fourPrimeResidue_cast9 m)
  simpa only [map_natCast,map_intCast] using h

private theorem four_centered_eq (a b : ℤ) (h : (a : ZMod 3)=(b : ZMod 3)) :
    (a+1)%3-1=(b+1)%3-1 := by
  congr 1
  apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mp
  push_cast
  rw [h]

theorem fourPrime_base_residue (m n : ℤ) :
    fourPrimeBase m n=fourPrimeBase (fourPrimeResidue m).val (fourPrimeResidue n).val := by
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [fourPrimeBase] <;>
    apply four_centered_eq <;>
    simp only [Int.cast_sub,Int.cast_add,Int.cast_neg,Int.cast_natCast,fourPrimeResidue_cast3]

theorem fourPrime_numerator_residue (m n : ℤ) (z : Fin 4 → ℤ) (i : Fin 4) :
    fourPrimeNumerator m n z i%9=
      fourPrimeNumerator (fourPrimeResidue m).val (fourPrimeResidue n).val z i%9 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 9).mp
  fin_cases i <;> simp [fourPrimeNumerator,fourPrimeResidue_cast9]

theorem fourPrime_character_residue (m n : ℤ) (z : Fin 4 → ℤ) :
    fourPrimeCharacter m n z=
      fourPrimeCharacter (fourPrimeResidue m).val (fourPrimeResidue n).val z := by
  unfold fourPrimeCharacter
  apply Finset.prod_congr rfl
  intro i _
  simp only [fourPrimeTrit]
  rw [fourPrime_numerator_residue m n z i]

theorem fourPrime_coordinates_residue (m n : ℤ) (z : Fin 4 → ℤ) :
    fourPrimeCoordinates m n z=
      fourPrimeCoordinates (fourPrimeResidue m).val (fourPrimeResidue n).val z := by
  simp only [fourPrimeCoordinates]
  rw [fourPrime_base_residue m n]

theorem fourPrime_residue_norm_unit (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) :
    ((fourPrimeResidue m).val*(fourPrimeResidue m).val+
      (fourPrimeResidue n).val*(fourPrimeResidue n).val)%3 ≠ 0 := by
  intro hz
  have he : (((fourPrimeResidue m).val*(fourPrimeResidue m).val+
      (fourPrimeResidue n).val*(fourPrimeResidue n).val : ℕ) : ZMod 3)=0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hz)
  apply hp3
  simpa only [Nat.cast_add,Nat.cast_mul,fourPrimeResidue_cast3,Int.cast_add,Int.cast_mul] using he

def fourPrimeData (m n : ℤ) : FourPrimeGeneratorData :=
  fourPrimeGeneratorData (fourPrimeResidue m) (fourPrimeResidue n)

/-- The same twelve certified points and integer inverse work for every
integer pair in the residue class. This is a uniform lifting statement. -/
theorem fourPrime_generator_data (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) :
    (∀ j : Fin 12, let z := (fourPrimeData m n).points j
      (z 2=1 ∧ z 3=0 ∨ z 2=0 ∧ z 3=1) ∧
      z 0*z 0+z 1*z 1 ≤ 50 ∧ fourPrimeCharacter m n z ≠ 0 ∧
      (z 0-z 2*fourPrimeBase m n 0 0-z 3*fourPrimeBase m n 1 0)%3=0 ∧
      (z 1-z 2*fourPrimeBase m n 0 1-z 3*fourPrimeBase m n 1 1)%3=0) ∧
    (∀ i k : Fin 4, ∑ j : Fin 12,
      (fourPrimeData m n).inverse i j*fourPrimeCoordinates m n ((fourPrimeData m n).points j) k=
        if i=k then 1 else 0) := by
  simpa only [fourPrimeData,fourPrime_character_residue m n,fourPrime_coordinates_residue m n,
    fourPrime_base_residue m n] using fourPrime_generators_finite
    (fourPrimeResidue m) (fourPrimeResidue n) (fourPrime_residue_norm_unit m n hp3)

end Ramanujan.MultiQuintuple
