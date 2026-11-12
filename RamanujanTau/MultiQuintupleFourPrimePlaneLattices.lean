import RamanujanTau.MultiQuintupleFourLatticePreservation
import RamanujanTau.MultiQuintupleFourPrimeSymmetryLift

/-! The two rank-two integer lattices singled out by norm-three rigidity. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourPrimeJ (m n : ℤ) : Fin 4 → ℤ := fourPrimeV (-n) m

theorem fourPrime_long_norm (a b : ℤ) : fourVectorNorm (fourPrimeV a b)=3*(a*a+b*b) := by
  simp [fourVectorNorm,fourDot,fourPrimeV]
  ring

theorem fourPrime_long_fixed_orthogonal (a b : ℤ) :
    fourDot fourPrimeU (fourPrimeV a b)=0 ∧ fourDot fourPrimeW (fourPrimeV a b)=0 := by
  constructor <;> simp [fourDot,fourPrimeU,fourPrimeW,fourPrimeV]

theorem fourPrime_long_combination (m n a b : ℤ) :
    a • fourPrimeV m n+b • fourPrimeJ m n=fourPrimeV (m*a-n*b) (n*a+m*b) := by
  ext i
  fin_cases i <;> simp [fourPrimeV,fourPrimeJ] <;> ring

theorem fourPrime_long_orthogonal_coordinates (x : Fin 4 → ℤ)
    (hu : fourDot fourPrimeU x=0) (hw : fourDot fourPrimeW x=0) :
    x=fourPrimeV (x 2) (x 1) := by
  simp [fourDot,fourPrimeU,fourPrimeW] at hu hw
  ext i
  fin_cases i <;> simp [fourPrimeV] <;> omega

/-- The long plane intersects the residue lattice in exactly Zv+Zj. -/
theorem fourPrime_residue_long_coordinates {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0)
    (x : Fin 4 → ℤ) (hx : x ∈ fourResidueModule p (fourPrimeV m n))
    (hu : fourDot fourPrimeU x=0) (hw : fourDot fourPrimeW x=0) :
    ∃ a b : ℤ, x=a • fourPrimeV m n+b • fourPrimeJ m n := by
  have he := fourPrime_long_orthogonal_coordinates x hu hw
  have hline : (p : ℤ) ∣ 3*(m*x 2+n*x 1) := by
    change (p : ℤ) ∣ fourDot (fourPrimeV m n) x at hx
    rw [he] at hx
    convert hx using 1
    simp [fourDot,fourPrimeV]
    ring
  have hA : (m : ZMod p)*(x 2 : ZMod p)+(n : ZMod p)*(x 1 : ZMod p)=0 := by
    apply (mul_eq_zero.mp (show (3 : ZMod p)*_=0 from ?_)).resolve_left h3
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_ofNat] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hline
  have hpp : (m : ZMod p)*(m : ZMod p)+(n : ZMod p)*(n : ZMod p)=0 := by
    have hh := congrArg (fun a : ℤ => (a : ZMod p)) hp
    simpa only [Int.cast_natCast,ZMod.natCast_self,Int.cast_mul,Int.cast_add] using hh.symm
  have hB : -(n : ZMod p)*(x 2 : ZMod p)+(m : ZMod p)*(x 1 : ZMod p)=0 := by
    apply (mul_eq_zero.mp (show (m : ZMod p)*_=0 from ?_)).resolve_left hm
    linear_combination -(n : ZMod p)*hA+(x 1 : ZMod p)*hpp
  have hdA : (p : ℤ) ∣ m*x 2+n*x 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add,Int.cast_mul] using hA
  have hdB : (p : ℤ) ∣ -n*x 2+m*x 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_neg] using hB
  obtain ⟨a,ha⟩ := hdA
  obtain ⟨b,hb⟩ := hdB
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hxa : m*a-n*b=x 2 := by
    apply mul_left_cancel₀ hpz
    linear_combination -m*ha+n*hb-x 2*hp
  have hxb : n*a+m*b=x 1 := by
    apply mul_left_cancel₀ hpz
    linear_combination -n*ha-m*hb-x 1*hp
  exact ⟨a,b,by rw [fourPrime_long_combination,hxa,hxb]; exact he⟩

theorem fourPrime_fixed_mem_residue (p : ℕ) (m n : ℤ) :
    fourPrimeU ∈ fourResidueModule p (fourPrimeV m n) ∧
      fourPrimeW ∈ fourResidueModule p (fourPrimeV m n) := by
  constructor <;> change (p : ℤ) ∣ _ <;>
    simp [fourDot,fourPrimeV,fourPrimeU,fourPrimeW]

theorem four_involution_integer_norm (T : FourOrthogonalInvolution) (x y : Fin 4 → ℤ)
    (he : T.linear (fourIntToRat x)=fourIntToRat y) : fourVectorNorm y=fourVectorNorm x := by
  have h := T.dot_preserving (fourIntToRat x) (fourIntToRat x)
  rw [he,fourDot_intToRat,fourDot_intToRat] at h
  exact_mod_cast h

theorem fourPrime_fixed_images {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp9 : 9<p) (hm : (m : ZMod p) ≠ 0)
    (T : FourOrthogonalInvolution)
    (hL : ∀ x ∈ fourResidueModule p (fourPrimeV m n),
      ∃ y ∈ fourResidueModule p (fourPrimeV m n), T.linear (fourIntToRat x)=fourIntToRat y)
    (x : Fin 4 → ℤ) (hx : x=fourPrimeU ∨ x=fourPrimeW) :
    T.linear (fourIntToRat x)=fourIntToRat fourPrimeU ∨
      T.linear (fourIntToRat x)=fourIntToRat (-fourPrimeU) ∨
      T.linear (fourIntToRat x)=fourIntToRat fourPrimeW ∨
      T.linear (fourIntToRat x)=fourIntToRat (-fourPrimeW) := by
  have hxm : x ∈ fourResidueModule p (fourPrimeV m n) := by
    rcases hx with rfl | rfl
    · exact (fourPrime_fixed_mem_residue p m n).1
    · exact (fourPrime_fixed_mem_residue p m n).2
  obtain ⟨y,hy,he⟩ := hL x hxm
  have hn := four_involution_integer_norm T x y he
  have hnorm : fourPrimeNorm y=3 := by
    have hxy : fourVectorNorm x=3 := by
      rcases hx with rfl | rfl <;> decide +kernel
    rw [hxy] at hn
    simpa [fourPrimeNorm,fourVectorNorm,fourDot,Fin.sum_univ_succ,add_assoc] using hn
  have hdiv : (p : ℤ) ∣ ∑ i, fourPrimeV m n i*y i := by
    simpa [fourResidueModule,fourDot,Fin.sum_univ_succ,add_assoc] using hy
  rcases fourPrime_norm_three_rigidity m n hp hp9 hm y hdiv hnorm with h | h | h | h
  · exact Or.inl (he.trans (congrArg fourIntToRat h))
  · exact Or.inr (Or.inl (he.trans (congrArg fourIntToRat h)))
  · exact Or.inr (Or.inr (Or.inl (he.trans (congrArg fourIntToRat h))))
  · exact Or.inr (Or.inr (Or.inr (he.trans (congrArg fourIntToRat h))))


theorem fourIntToRat_neg (x : Fin 4 → ℤ) : fourIntToRat (-x)= -fourIntToRat x := by
  ext i
  simp [fourIntToRat]

theorem fourDot_neg_right {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    fourDot x (-y)= -fourDot x y := by
  simp [fourDot]
  ring

theorem four_involution_self_adjoint (T : FourOrthogonalInvolution) (x y : FourRatPoint) :
    fourDot (T.linear x) y=fourDot x (T.linear y) := by
  simpa only [T.involutive] using T.dot_preserving x (T.linear y)

theorem fourPrime_long_orthogonality_preserved {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp9 : 9<p) (hm : (m : ZMod p) ≠ 0)
    (T : FourOrthogonalInvolution)
    (hL : ∀ x ∈ fourResidueModule p (fourPrimeV m n),
      ∃ y ∈ fourResidueModule p (fourPrimeV m n), T.linear (fourIntToRat x)=fourIntToRat y)
    (x y : Fin 4 → ℤ) (he : T.linear (fourIntToRat x)=fourIntToRat y)
    (hu : fourDot fourPrimeU x=0) (hw : fourDot fourPrimeW x=0) :
    fourDot fourPrimeU y=0 ∧ fourDot fourPrimeW y=0 := by
  have hxu : fourDot (fourIntToRat x) (fourIntToRat fourPrimeU)=0 := by
    rw [fourDot_intToRat,fourDot_comm,hu,Int.cast_zero]
  have hxw : fourDot (fourIntToRat x) (fourIntToRat fourPrimeW)=0 := by
    rw [fourDot_intToRat,fourDot_comm,hw,Int.cast_zero]
  have horth (b : Fin 4 → ℤ) (hb : b=fourPrimeU ∨ b=fourPrimeW) : fourDot b y=0 := by
    have hd := four_involution_self_adjoint T (fourIntToRat x) (fourIntToRat b)
    rw [he] at hd
    rcases fourPrime_fixed_images m n hp hp9 hm T hL b hb with h | h | h | h
    all_goals
      simp only [h,fourIntToRat_neg,fourDot_neg_right,hxu,hxw,neg_zero] at hd
      rw [fourDot_intToRat] at hd
      have hdi : fourDot y b=0 := by exact_mod_cast hd
      simpa only [fourDot_comm] using hdi
  exact ⟨horth _ (Or.inl rfl),horth _ (Or.inr rfl)⟩

theorem fourPrime_long_basis_mem_residue {p : ℕ} (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) :
    fourPrimeV m n ∈ fourResidueModule p (fourPrimeV m n) ∧
      fourPrimeJ m n ∈ fourResidueModule p (fourPrimeV m n) := by
  constructor
  · change (p : ℤ) ∣ fourVectorNorm (fourPrimeV m n)
    rw [fourPrime_long_norm,← hp]
    exact dvd_mul_left _ _
  · change (p : ℤ) ∣ fourDot (fourPrimeV m n) (fourPrimeJ m n)
    have he : fourDot (fourPrimeV m n) (fourPrimeJ m n)=0 := by
      simp [fourDot,fourPrimeV,fourPrimeJ]
      ring
    rw [he]
    exact dvd_zero _

theorem fourPrime_long_images_integral {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp9 : 9<p) (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0)
    (T : FourOrthogonalInvolution)
    (hL : ∀ x ∈ fourResidueModule p (fourPrimeV m n),
      ∃ y ∈ fourResidueModule p (fourPrimeV m n), T.linear (fourIntToRat x)=fourIntToRat y)
    (x : Fin 4 → ℤ) (hx : x=fourPrimeV m n ∨ x=fourPrimeJ m n) :
    ∃ a b : ℤ, T.linear (fourIntToRat x)=fourIntToRat (a • fourPrimeV m n+b • fourPrimeJ m n) := by
  have hxm : x ∈ fourResidueModule p (fourPrimeV m n) := by
    rcases hx with rfl | rfl
    · exact (fourPrime_long_basis_mem_residue m n hp).1
    · exact (fourPrime_long_basis_mem_residue m n hp).2
  have hxo : fourDot fourPrimeU x=0 ∧ fourDot fourPrimeW x=0 := by
    rcases hx with rfl | rfl
    · exact fourPrime_long_fixed_orthogonal m n
    · exact fourPrime_long_fixed_orthogonal (-n) m
  obtain ⟨y,hy,he⟩ := hL x hxm
  obtain ⟨hu,hw⟩ := fourPrime_long_orthogonality_preserved m n hp hp9 hm T hL x y he hxo.1 hxo.2
  obtain ⟨a,b,hab⟩ := fourPrime_residue_long_coordinates m n hp h3 hm y hy hu hw
  exact ⟨a,b,he.trans (congrArg fourIntToRat hab)⟩

end Ramanujan.MultiQuintuple
