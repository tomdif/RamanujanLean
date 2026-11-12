import RamanujanTau.MultiQuintupleFourPrimeGeometry
import RamanujanTau.MultiQuintupleFourDualLattice

/-! Integral coordinates for the prime-family projective lattice. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def FourPrimeIntegral (m n : ℤ) (z : Fin 4 → ℤ) : Prop :=
  ∀ i, (3 : ℤ) ∣ fourPrimeNumerator m n z i

def fourPrimePoint (m n : ℤ) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => fourPrimeNumerator m n z i/3

theorem fourPrime_three_point (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) (i : Fin 4) :
    3*fourPrimePoint m n z i=fourPrimeNumerator m n z i :=
  Int.mul_ediv_cancel' (hz i)

private theorem four_cast_mod_three (a : ℤ) : ((a%3 : ℤ) : ZMod 3)=(a : ZMod 3) :=
  ZMod.intCast_mod a 3

theorem fourPrimeBase_cast (m n : ℤ) (i j : Fin 2) :
    ((fourPrimeBase m n i j : ℤ) : ZMod 3)=
      ![![(m : ZMod 3)-n,-m-n],![m+n,m-n]] i j := by
  fin_cases i <;> fin_cases j <;> simp [fourPrimeBase,four_cast_mod_three]

def fourPrimeRawCoordinates (m n : ℤ) (q : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![3*q 0+q 2*fourPrimeBase m n 0 0+q 3*fourPrimeBase m n 1 0,
    3*q 1+q 2*fourPrimeBase m n 0 1+q 3*fourPrimeBase m n 1 1,q 2,q 3]

theorem fourPrime_numerator_add (m n : ℤ) (x y : Fin 4 → ℤ) :
    fourPrimeNumerator m n (x+y)=fourPrimeNumerator m n x+fourPrimeNumerator m n y := by
  ext i
  fin_cases i <;> simp [fourPrimeNumerator] <;> ring

theorem fourPrime_numerator_smul (m n c : ℤ) (x : Fin 4 → ℤ) :
    fourPrimeNumerator m n (c • x)=c • fourPrimeNumerator m n x := by
  ext i
  fin_cases i <;> simp [fourPrimeNumerator] <;> ring

theorem fourPrime_raw_add (m n : ℤ) (x y : Fin 4 → ℤ) :
    fourPrimeRawCoordinates m n (x+y)=fourPrimeRawCoordinates m n x+fourPrimeRawCoordinates m n y := by
  ext i
  fin_cases i <;> simp [fourPrimeRawCoordinates] <;> ring

theorem fourPrime_raw_smul (m n c : ℤ) (x : Fin 4 → ℤ) :
    fourPrimeRawCoordinates m n (c • x)=c • fourPrimeRawCoordinates m n x := by
  ext i
  fin_cases i <;> simp [fourPrimeRawCoordinates] <;> ring

theorem fourPrime_raw_integral (m n : ℤ) (q : Fin 4 → ℤ) :
    FourPrimeIntegral m n (fourPrimeRawCoordinates m n q) := by
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  fin_cases i <;> simp [fourPrimeNumerator,fourPrimeRawCoordinates,
    fourPrimeBase_cast,show (3 : ZMod 3)=0 by decide] <;> ring_nf <;>
    simp [show (3 : ZMod 3)=0 by decide]

/-- The actual integer map underlying the certificate coordinates. -/
def fourPrimeBasisMap (m n : ℤ) : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun q := fourPrimePoint m n (fourPrimeRawCoordinates m n q)
  map_add' x y := by
    funext i
    apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
    change 3*fourPrimePoint m n (fourPrimeRawCoordinates m n (x+y)) i=
      3*(fourPrimePoint m n (fourPrimeRawCoordinates m n x) i+
        fourPrimePoint m n (fourPrimeRawCoordinates m n y) i)
    rw [mul_add,fourPrime_three_point _ _ _ (fourPrime_raw_integral _ _ _),
      fourPrime_three_point _ _ _ (fourPrime_raw_integral _ _ _),
      fourPrime_three_point _ _ _ (fourPrime_raw_integral _ _ _),
      fourPrime_raw_add,fourPrime_numerator_add]
    rfl
  map_smul' c x := by
    funext i
    apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
    change 3*fourPrimePoint m n (fourPrimeRawCoordinates m n (c • x)) i=
      3*(c*fourPrimePoint m n (fourPrimeRawCoordinates m n x) i)
    rw [fourPrime_three_point _ _ _ (fourPrime_raw_integral _ _ _),
      fourPrime_raw_smul,fourPrime_numerator_smul]
    change c*fourPrimeNumerator m n (fourPrimeRawCoordinates m n x) i=_
    rw [← fourPrime_three_point _ _ _ (fourPrime_raw_integral _ _ _)]
    ring

theorem fourPrime_integral_coordinate_congruences (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) :
    (z 0-z 2*fourPrimeBase m n 0 0-z 3*fourPrimeBase m n 1 0)%3=0 ∧
    (z 1-z 2*fourPrimeBase m n 0 1-z 3*fourPrimeBase m n 1 1)%3=0 := by
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (hz 1)
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (hz 2)
  simp [fourPrimeNumerator] at h1 h2
  constructor
  all_goals
    apply Int.emod_eq_zero_of_dvd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    apply (mul_eq_zero.mp (show ((m*m+n*n : ℤ) : ZMod 3)*_=0 from ?_)).resolve_left hp3
    push_cast
    simp only [fourPrimeBase_cast,Matrix.cons_val_zero,Matrix.cons_val_one]
  · linear_combination (m : ZMod 3)*h2+(n : ZMod 3)*h1
  · linear_combination (m : ZMod 3)*h1-(n : ZMod 3)*h2

theorem fourPrime_raw_coordinates_inverse (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) :
    fourPrimeRawCoordinates m n (fourPrimeCoordinates m n z)=z := by
  obtain ⟨h0,h1⟩ := fourPrime_integral_coordinate_congruences m n hp3 z hz
  have h0' := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h0)
  have h1' := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h1)
  ext i
  fin_cases i <;> simp [fourPrimeRawCoordinates,fourPrimeCoordinates] <;> omega

theorem fourPrime_point_eq_basis (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) :
    fourPrimePoint m n z=fourPrimeBasisMap m n (fourPrimeCoordinates m n z) := by
  change _=fourPrimePoint m n (fourPrimeRawCoordinates m n (fourPrimeCoordinates m n z))
  rw [fourPrime_raw_coordinates_inverse m n hp3 z hz]


/-- Raw integer coordinates of an arbitrary projective-lattice lift. -/
def fourPrimeProjectiveCoordinates (m n a : ℤ) (r : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![3*a+m*(r 0+r 2+r 3)+n*(-r 0+r 1+r 3),
    -n*(r 0+r 2+r 3)+m*(-r 0+r 1+r 3),r 0+r 1-r 2,-r 1-r 2+r 3]

theorem fourPrime_projective_numerator {p : ℕ} (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (x : FourProjectiveLift p (fourPrimeV m n)) :
    fourPrimeNumerator m n (fourPrimeProjectiveCoordinates m n x.scalar x.remainder)=
      (3 : ℤ) • x.point := by
  rw [x.point_eq,hp]
  ext i
  fin_cases i <;> dsimp [fourPrimeNumerator,fourPrimeProjectiveCoordinates,fourPrimeV] <;> ring

/-- Every point of the projective lattice has integral coordinates in the
basis map. No rational saturation of the integer span is assumed. -/
theorem fourPrime_projective_basis_preimage {p : ℕ} (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0)
    (x : FourProjectiveLift p (fourPrimeV m n)) :
    ∃ q : Fin 4 → ℤ, fourPrimeBasisMap m n q=x.point := by
  let z := fourPrimeProjectiveCoordinates m n x.scalar x.remainder
  have he := fourPrime_projective_numerator m n hp x
  have hz : FourPrimeIntegral m n z := by
    intro i
    refine ⟨x.point i,?_⟩
    exact congrFun he i
  have hw : fourPrimePoint m n z=x.point := by
    funext i
    apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
    rw [fourPrime_three_point m n z hz]
    exact congrFun he i
  exact ⟨fourPrimeCoordinates m n z,(fourPrime_point_eq_basis m n hp3 z hz).symm.trans hw⟩

end Ramanujan.MultiQuintuple
