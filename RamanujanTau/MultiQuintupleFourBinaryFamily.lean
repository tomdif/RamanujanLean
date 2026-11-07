import RamanujanTau.MultiQuintupleFourBinary

/-! An unbounded, unconditional one-parameter subfamily of the second quadratic norm family. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fourBinaryFamilyM (t : ℕ) : ℕ := 15*t+3
def fourBinaryFamilyP (t : ℕ) : ℕ := 450*t^2+180*t+43
def fourBinaryFamilyR (t : ℕ) (r : Bool) : ℕ :=
  if r then 45*t+19 else if t=0 then 32 else 45*t-11

lemma fourBinaryFamily_coprime (t : ℕ) :
    Nat.Coprime (30*fourBinaryFamilyM t) (fourBinaryFamilyP t) := by
  have h30 : Nat.Coprime 30 (fourBinaryFamilyP t) := by
    have h := (Nat.coprime_add_mul_right_left 13 30 (15*t^2+6*t+1)).mpr (by decide)
    apply Nat.Coprime.symm
    convert h using 1
    dsimp [fourBinaryFamilyP]
    ring
  have hm5 : Nat.Coprime (fourBinaryFamilyM t) 5 := by
    have h := (Nat.coprime_add_mul_right_left 3 5 (3*t)).mpr (by decide)
    convert h using 1
    dsimp [fourBinaryFamilyM]
    ring
  have hm25 : Nat.Coprime (fourBinaryFamilyM t) 25 := by simpa using hm5.pow_right 2
  have hmp : Nat.Coprime (fourBinaryFamilyM t) (fourBinaryFamilyP t) := by
    have h := (Nat.coprime_mul_left_add_right (fourBinaryFamilyM t) 25
      (2*fourBinaryFamilyM t)).mpr hm25
    convert h using 1
    dsimp [fourBinaryFamilyM,fourBinaryFamilyP]
    ring
  exact Nat.coprime_mul_iff_left.mpr ⟨h30,hmp⟩

/-- Two permanent zero progressions for every natural parameter, without a primality assumption. -/
theorem coeff_fourBinary_family (t N : ℕ) (r : Bool) :
    coeff (fourBinaryFamilyP t*N+fourBinaryFamilyR t r)
      (quintupleSpecialized (fourBinaryFamilyP t) (2*fourBinaryFamilyM t) *
       quintupleSpecialized (fourBinaryFamilyP t) (4*fourBinaryFamilyM t) *
       quintupleSpecialized (fourBinaryFamilyP t) 5 *
       quintupleSpecialized (fourBinaryFamilyP t) 15)=0 := by
  apply coeff_fourBinary_zero (fourBinaryFamilyP t) (fourBinaryFamilyM t) 5
    (fourBinaryFamilyR t r) N r
  · dsimp [fourBinaryFamilyP,fourBinaryFamilyM]; ring
  · dsimp [fourBinaryFamilyM]; omega
  · norm_num
  · dsimp [fourBinaryFamilyM,fourBinaryFamilyP]; nlinarith
  · dsimp [fourBinaryFamilyP]; omega
  · refine ⟨5*t+1,?_⟩
    dsimp [fourBinaryFamilyM]; ring
  · norm_num
  · exact fourBinaryFamily_coprime t
  · cases r
    · by_cases ht : t=0
      · subst t
        norm_num [fourBinaryFamilyM,fourBinaryFamilyP,fourBinaryFamilyR,fourBinaryResidue]
      · have hle : 11 ≤ 45*t := by omega
        simp only [fourBinaryFamilyR,Bool.false_eq_true,ite_false,if_neg ht,
          fourBinaryResidue,fourBinaryFamilyM,Nat.cast_sub hle,Nat.cast_add,
          Nat.cast_mul,Nat.cast_ofNat]
        convert dvd_zero (fourBinaryFamilyP t : ℤ) using 1
        ring
    · simp only [fourBinaryFamilyR,ite_true,fourBinaryResidue,fourBinaryFamilyM,
        Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      convert dvd_zero (fourBinaryFamilyP t : ℤ) using 1
      ring

/-- The moduli are strictly increasing, so the theorem covers unbounded moduli. -/
theorem fourBinaryFamilyP_strictMono : StrictMono fourBinaryFamilyP := by
  intro x y h
  have hh : x^2 ≤ y^2 := Nat.pow_le_pow_left (Nat.le_of_lt h) 2
  dsimp [fourBinaryFamilyP]
  nlinarith

lemma fourBinaryFamilyR_lt (t : ℕ) (r : Bool) :
    fourBinaryFamilyR t r < fourBinaryFamilyP t := by
  cases r
  · by_cases ht : t=0
    · subst t; norm_num [fourBinaryFamilyR,fourBinaryFamilyP]
    · simp only [fourBinaryFamilyR,Bool.false_eq_true,ite_false,if_neg ht]
      have hh := Nat.sub_le (45*t) 11
      dsimp [fourBinaryFamilyP]
      nlinarith
  · simp only [fourBinaryFamilyR,ite_true,fourBinaryFamilyP]
    nlinarith

lemma fourBinaryFamilyR_injective (t : ℕ) : Function.Injective (fourBinaryFamilyR t) := by
  intro r s h
  cases r <;> cases s <;> simp [fourBinaryFamilyR] at h ⊢
  all_goals split_ifs at h <;> omega


private lemma fourBinary_no_three_mod_four : ∀ a b : ZMod 4, a^2+b^2 ≠ 3 := by
  decide +kernel

/-- Unboundedly many members of this family are outside every integer sum-of-two-squares modulus. -/
theorem fourBinaryFamily_even_not_sum_squares (t : ℕ) :
    ¬ ∃ a b : ℤ, (fourBinaryFamilyP (2*t) : ℤ)=a^2+b^2 := by
  rintro ⟨a,b,h⟩
  have hp : (fourBinaryFamilyP (2*t) : ZMod 4)=3 := by
    dsimp [fourBinaryFamilyP]
    push_cast
    ring_nf
    reduce_mod_char
  have he := congrArg (fun z : ℤ => (z : ZMod 4)) h
  simp only [Int.cast_natCast,Int.cast_add,Int.cast_pow] at he
  rw [hp] at he
  exact fourBinary_no_three_mod_four (a : ZMod 4) (b : ZMod 4) he.symm

end Ramanujan.MultiQuintuple
