/-
# A universal spanning certificate for the Poisson-dual Watson support

The fixed-first-four-shell and fixed-first-five-shell rigidity conjectures are
false: supported vectors can remain collinear or coplanar across several early
norm shells.  The natural replacement stops at the first complete shell
whose cumulative supported vectors span `Q^3`.

This file proves that this adaptive stopping shell always exists.  For every
nonzero modulus `p`, the three scalar-zero dual vectors

  (p,p,p), (p,p,-p), (p,-p,p)

all carry nonzero Watson character, all have norm `3*p^2`, and have determinant
`-4*p^3`.  Thus the supported dual vectors span three-space by norm `3*p^2`.
No primality, isotropy, or inverse hypothesis is needed for this certificate.
-/
import RamanujanTau.MultiQuintupleRootReflection

namespace Ramanujan.MultiQuintuple

/-- One of the three affine phase differences in the factored dual Watson
amplitude.  Here `q` represents the chosen inverse of `3*k` modulo `p` and
`a` is the corresponding component of `(i,j,k)`. -/
def dualWatsonDelta (q a w3 ws : ℤ) : ℤ :=
  2 * ws - 6 * w3 * q * a

/-- A dual vector carries the Watson character exactly when none of its three
affine phase differences vanishes modulo `6*p`. -/
def DualWatsonSupported
    (p q i j k w1 w2 w3 : ℤ) : Prop :=
  ¬(6 * p ∣ dualWatsonDelta q i w3 w1) ∧
  ¬(6 * p ∣ dualWatsonDelta q j w3 w2) ∧
  ¬(6 * p ∣ dualWatsonDelta q k w3 w3)

/-- The scalar-zero sector of the integral projective dual lattice. -/
def IsScalarZeroDualVector (p w1 w2 w3 : ℤ) : Prop :=
  p ∣ w1 ∧ p ∣ w2 ∧ p ∣ w3

/-- A determinant written directly in ternary coordinates. -/
def ternaryDet
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℤ) : ℤ :=
  a1 * (b2 * c3 - b3 * c2) -
    a2 * (b1 * c3 - b3 * c1) +
    a3 * (b1 * c2 - b2 * c1)

/-- A number congruent to `+2` or `-2` modulo six cannot be divisible by six. -/
private theorem six_not_dvd_two_mul_sign_sub_six_mul
    (z t : ℤ) (hz : z = 1 ∨ z = -1) :
    ¬(6 ∣ 2 * z - 6 * t) := by
  rcases hz with rfl | rfl <;> omega

/-- Every coordinate phase of a scalar-zero sign vector `p*z` is nonzero
modulo `6*p`. -/
theorem six_mul_p_not_dvd_dualWatsonDelta_sign
    (p q a z3 zs : ℤ) (hp : p ≠ 0)
    (hzs : zs = 1 ∨ zs = -1) :
    ¬(6 * p ∣ dualWatsonDelta q a (p * z3) (p * zs)) := by
  intro hdvd
  rcases hdvd with ⟨c, hc⟩
  have hfactor :
      p * (2 * zs - 6 * z3 * q * a) = p * (6 * c) := by
    rw [dualWatsonDelta] at hc
    nlinarith
  have hcancel : 2 * zs - 6 * z3 * q * a = 6 * c :=
    mul_left_cancel₀ hp hfactor
  apply six_not_dvd_two_mul_sign_sub_six_mul zs (z3 * q * a) hzs
  refine ⟨c, ?_⟩
  nlinarith

/-- Any vector `p*(z1,z2,z3)` with sign coordinates has nonzero Watson
character. -/
theorem dualWatsonSupported_signCube
    (p q i j k z1 z2 z3 : ℤ) (hp : p ≠ 0)
    (hz1 : z1 = 1 ∨ z1 = -1)
    (hz2 : z2 = 1 ∨ z2 = -1)
    (hz3 : z3 = 1 ∨ z3 = -1) :
    DualWatsonSupported p q i j k
      (p * z1) (p * z2) (p * z3) := by
  constructor
  · exact six_mul_p_not_dvd_dualWatsonDelta_sign p q i z3 z1 hp hz1
  constructor
  · exact six_mul_p_not_dvd_dualWatsonDelta_sign p q j z3 z2 hp hz2
  · exact six_mul_p_not_dvd_dualWatsonDelta_sign p q k z3 z3 hp hz3

/-- Every sign-cube vector used below lies in the scalar-zero dual sector. -/
theorem isScalarZeroDualVector_signCube (p z1 z2 z3 : ℤ) :
    IsScalarZeroDualVector p (p * z1) (p * z2) (p * z3) := by
  exact ⟨dvd_mul_right p z1, dvd_mul_right p z2, dvd_mul_right p z3⟩

/-- The three displayed vectors really are integral projective dual vectors. -/
theorem dualSpanningVectors_scalarZero (p : ℤ) :
    IsScalarZeroDualVector p p p p ∧
    IsScalarZeroDualVector p p p (-p) ∧
    IsScalarZeroDualVector p p (-p) p := by
  constructor
  · simpa using isScalarZeroDualVector_signCube p 1 1 1
  constructor
  · simpa using isScalarZeroDualVector_signCube p 1 1 (-1)
  · simpa using isScalarZeroDualVector_signCube p 1 (-1) 1

/-- The first explicit spanning vector is supported. -/
theorem dualWatsonSupported_ppp
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p p p := by
  simpa using dualWatsonSupported_signCube p q i j k 1 1 1 hp
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)

/-- The second explicit spanning vector is supported. -/
theorem dualWatsonSupported_ppn
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p p (-p) := by
  simpa using dualWatsonSupported_signCube p q i j k 1 1 (-1) hp
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)

/-- The third explicit spanning vector is supported. -/
theorem dualWatsonSupported_pnp
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p (-p) p := by
  simpa using dualWatsonSupported_signCube p q i j k 1 (-1) 1 hp
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)

/-- Every explicit spanning vector has squared norm `3*p^2`. -/
theorem dualSpanningVector_norms (p : ℤ) :
    ternaryNorm p p p = 3 * p ^ 2 ∧
    ternaryNorm p p (-p) = 3 * p ^ 2 ∧
    ternaryNorm p (-p) p = 3 * p ^ 2 := by
  simp only [ternaryNorm]
  constructor
  · ring
  constructor <;> ring

/-- Their determinant is `-4*p^3`. -/
theorem dualSpanningVectors_det (p : ℤ) :
    ternaryDet p p p p p (-p) p (-p) p = -4 * p ^ 3 := by
  simp only [ternaryDet]
  ring

/-- **Universal supported-spanning certificate.**

For every nonzero `p` and every dual Watson datum, three supported vectors of
norm `3*p^2` have nonzero determinant.  Consequently the adaptive first
spanning shell exists no later than squared norm `3*p^2`. -/
theorem dualWatson_supported_spanning_certificate
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p p p ∧
    DualWatsonSupported p q i j k p p (-p) ∧
    DualWatsonSupported p q i j k p (-p) p ∧
    ternaryNorm p p p = 3 * p ^ 2 ∧
    ternaryNorm p p (-p) = 3 * p ^ 2 ∧
    ternaryNorm p (-p) p = 3 * p ^ 2 ∧
    ternaryDet p p p p p (-p) p (-p) p ≠ 0 := by
  refine ⟨dualWatsonSupported_ppp p q i j k hp,
    dualWatsonSupported_ppn p q i j k hp,
    dualWatsonSupported_pnp p q i j k hp, ?_⟩
  rcases dualSpanningVector_norms p with ⟨h1, h2, h3⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [dualSpanningVectors_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hp)

end Ramanujan.MultiQuintuple
