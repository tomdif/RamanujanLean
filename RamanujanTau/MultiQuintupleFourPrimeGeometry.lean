import RamanujanTau.MultiQuintupleFourPrimeFinite

/-! Exact norm identities for the prime-family lattice argument. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 1000000

def fourPrimeNorm (x : Fin 4 → ℤ) : ℤ := ∑ i, x i*x i

def fourPrimeV (m n : ℤ) : Fin 4 → ℤ := ![m-n,n,m,m+n]

def fourPrimeU : Fin 4 → ℤ := ![1,1,-1,0]
def fourPrimeW : Fin 4 → ℤ := ![0,-1,-1,1]

theorem fourPrime_numerator_norm (m n : ℤ) (z : Fin 4 → ℤ) :
    fourPrimeNorm (fourPrimeNumerator m n z) =
      3*(m*m+n*n)*(z 0*z 0+z 1*z 1+(m*m+n*n)*(z 2*z 2+z 3*z 3)) := by
  simp [fourPrimeNorm,fourPrimeNumerator,Fin.sum_univ_succ]
  ring

/-- The certified bound 50 gives the strict short-vector threshold for p>100. -/
theorem fourPrime_supported_point_short (p a b d : ℤ) (hp : 100 < p)
    (hab : a*a+b*b ≤ 50) (hd : 3*d=p*(p+a*a+b*b)) : 2*d<p*p := by
  have h := mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ 50-(a*a+b*b) by omega)
  nlinarith

/-- The four fixed columns form a scaled orthogonal matrix. -/
theorem fourPrime_frame_norm (x : Fin 4 → ℤ) :
    (x 0+x 2+x 3)^2+(-x 0+x 1+x 3)^2+
      (x 0+x 1-x 2)^2+(-x 1-x 2+x 3)^2 = 3*fourPrimeNorm x := by
  simp [fourPrimeNorm,Fin.sum_univ_succ]
  ring

/-- Over a prime field, the isotropic orthogonal line is isotropic. -/
theorem fourPrime_orthogonal_line_isotropic {F : Type*} [Field F]
    (m n x y : F) (hm : m ≠ 0) (hp : m*m+n*n=0)
    (hxy : m*x+n*y=0) : x*x+y*y=0 := by
  have h : (m*m)*(x*x+y*y)=0 := by
    linear_combination (m*x-n*y)*hxy + y*y*hp
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hm hm)

/-- Every norm-three vector in the residue lattice is one of four fixed vectors. -/
theorem fourPrime_norm_three_rigidity {p : ℕ} [Fact p.Prime]
    (m n : ℤ) (hp : (p : ℤ)=m*m+n*n) (hp9 : 9 < p)
    (hm : (m : ZMod p) ≠ 0) (x : Fin 4 → ℤ)
    (hx : (p : ℤ) ∣ ∑ i, fourPrimeV m n i*x i)
    (hnorm : fourPrimeNorm x=3) :
    x=fourPrimeU ∨ x= -fourPrimeU ∨ x=fourPrimeW ∨ x= -fourPrimeW := by
  let X := x 0+x 2+x 3
  let Y := -x 0+x 1+x 3
  have hline : (p : ℤ) ∣ m*X+n*Y := by
    convert hx using 1
    simp [X,Y,fourPrimeV,Fin.sum_univ_succ]
    ring
  have hlinep : (m : ZMod p)*(X : ZMod p)+(n : ZMod p)*(Y : ZMod p)=0 := by
    simpa only [Int.cast_add,Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hline
  have hpp : (m : ZMod p)*(m : ZMod p)+(n : ZMod p)*(n : ZMod p)=0 := by
    have h := congrArg (fun a : ℤ => (a : ZMod p)) hp
    simpa only [Int.cast_natCast,ZMod.natCast_self,Int.cast_add,Int.cast_mul] using h.symm
  have hfield := fourPrime_orthogonal_line_isotropic (m : ZMod p) (n : ZMod p)
    (X : ZMod p) (Y : ZMod p) hm hpp hlinep
  have hdiv : (p : ℤ) ∣ X*X+Y*Y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add,Int.cast_mul] using hfield
  have hframe := fourPrime_frame_norm x
  have hb : 0 ≤ X*X+Y*Y ∧ X*X+Y*Y ≤ 9 := by
    dsimp [X,Y]
    rw [hnorm] at hframe
    constructor <;> nlinarith [sq_nonneg (x 0+x 2+x 3),sq_nonneg (-x 0+x 1+x 3),
      sq_nonneg (x 0+x 1-x 2),sq_nonneg (-x 1-x 2+x 3)]
  have hzero : X*X+Y*Y=0 := by
    have hmod := Int.emod_eq_zero_of_dvd hdiv
    rwa [Int.emod_eq_of_lt hb.1 (by exact_mod_cast (show X*X+Y*Y < (p : ℤ) by omega))] at hmod
  have hX : X=0 := by nlinarith [sq_nonneg X,sq_nonneg Y]
  have hY : Y=0 := by nlinarith [sq_nonneg X,sq_nonneg Y]
  have h1 : x 1=x 0-x 3 := by dsimp [Y] at hY; omega
  have h2 : x 2= -x 0-x 3 := by dsimp [X] at hX; omega
  have hsmall : x 0*x 0+x 3*x 3=1 := by
    simp [fourPrimeNorm,Fin.sum_univ_succ] at hnorm
    rw [h1,h2] at hnorm
    nlinarith
  have hbound0 : -1 ≤ x 0 ∧ x 0 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (x 3),sq_nonneg (x 0+1),sq_nonneg (x 0-1)]
  have hbound3 : -1 ≤ x 3 ∧ x 3 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 3+1),sq_nonneg (x 3-1)]
  rcases hbound0 with ⟨hl0,hu0⟩
  rcases hbound3 with ⟨hl3,hu3⟩
  interval_cases h0 : x 0 <;> interval_cases h3 : x 3 <;>
    norm_num [h0,h3] at hsmall
  all_goals first
    | solve | left; ext i; fin_cases i <;> simp_all [fourPrimeU]
    | solve | right; left; ext i; fin_cases i <;> simp_all [fourPrimeU]
    | solve | right; right; left; ext i; fin_cases i <;> simp_all [fourPrimeW]
    | solve | right; right; right; ext i; fin_cases i <;> simp_all [fourPrimeW]

end Ramanujan.MultiQuintuple
