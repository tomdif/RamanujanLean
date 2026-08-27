/-
# Projective and reflective-lattice structure for sparse triple products

For an isotropic triple `i^2+j^2+k^2=0`, the symmetric projective invariant

  J = (i^2*j^2+j^2*k^2+k^2*i^2)^3 / (i^2*j^2*k^2)^2

is, up to the factor `-256`, the classical Legendre elliptic-curve `j`-invariant at
`lambda = -(j/i)^2`.  This identifies the signed-permutation/projective quotient of the
isotropic conic with a familiar modular invariant.

The second part records the exact nontrivial reflection and the four affine branch pairings
found for the new candidate `p=71`, `(i,j,k)=(1,11,34)`, residue `61`.  Each pairing preserves
the doubled exponent of the three bilateral quintuple sums and reverses branch parity.  These
are the algebraic identities consumed by a coefficient-cancellation proof; no numerical
approximation and no `sorry` are used.
-/
import RamanujanTau.MultiQuintupleVanishing
import Mathlib.Tactic.FieldSimp

namespace Ramanujan.MultiQuintuple

section ProjectiveInvariant

variable {K : Type*} [Field K]

/-- The second elementary symmetric function of the squared triple. -/
def ternarySquareSigma2 (i j k : K) : K :=
  i ^ 2 * j ^ 2 + j ^ 2 * k ^ 2 + k ^ 2 * i ^ 2

/-- The product of the three squared coordinates. -/
def ternarySquareSigma3 (i j k : K) : K :=
  i ^ 2 * j ^ 2 * k ^ 2

/-- The symmetric projective invariant of a nonzero ternary triple. -/
def octahedralJ (i j k : K) : K :=
  ternarySquareSigma2 i j k ^ 3 / ternarySquareSigma3 i j k ^ 2

/-- The standard `j`-invariant of the Legendre curve with parameter `lambda`. -/
def legendreJ (lambda : K) : K :=
  256 * (1 - lambda + lambda ^ 2) ^ 3 / (lambda ^ 2 * (1 - lambda) ^ 2)

/-- **Octahedral/elliptic bridge.** On the isotropic conic, `-256 J` is the Legendre
elliptic `j`-invariant at `lambda = -(j/i)^2`. -/
theorem neg_256_octahedralJ_eq_legendreJ {i j k : K}
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hisotropic : i ^ 2 + j ^ 2 + k ^ 2 = 0) :
    -256 * octahedralJ i j k = legendreJ (-(j / i) ^ 2) := by
  have hi2 : i ^ 2 ≠ 0 := pow_ne_zero _ hi
  have hj2 : j ^ 2 ≠ 0 := pow_ne_zero _ hj
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero _ hk
  have hij : i ^ 2 + j ^ 2 ≠ 0 := by
    intro hij
    have : k ^ 2 = 0 := by linear_combination hisotropic - hij
    exact hk2 this
  have hkrel : k ^ 2 = -(i ^ 2 + j ^ 2) := by linear_combination hisotropic
  have hsigma2 :
      ternarySquareSigma2 i j k = -(i ^ 4 + i ^ 2 * j ^ 2 + j ^ 4) := by
    rw [ternarySquareSigma2,
      show i ^ 2 * j ^ 2 + j ^ 2 * k ^ 2 + k ^ 2 * i ^ 2
          = (i ^ 2 + j ^ 2) * (i ^ 2 + j ^ 2 + k ^ 2)
              - (i ^ 4 + i ^ 2 * j ^ 2 + j ^ 4) by ring,
      hisotropic, mul_zero, zero_sub]
  rw [octahedralJ, hsigma2, ternarySquareSigma3, hkrel, legendreJ]
  field_simp [hi, hj, hi2, hj2, hij]
  ring

end ProjectiveInvariant

/-- The new reflective triple is isotropic modulo `71`. -/
theorem reflective71_isotropic : (71 : ℤ) ∣ 1 ^ 2 + 11 ^ 2 + 34 ^ 2 := by norm_num

local instance prime71 : Fact (Nat.Prime 71) := ⟨by norm_num⟩

/-- Its projective invariant is the class `J=37`. -/
theorem reflective71_octahedralJ :
    octahedralJ (1 : ZMod 71) 11 34 = 37 := by
  native_decide

section Reflective71

/-- The residue-restricted ternary lattice norm for the normalized `p=71` class
`(1,11,34)`.  Its lattice basis has third coordinate `48x+31y+71z`. -/
def reflectiveNorm71 (x y z : ℤ) : ℤ :=
  x ^ 2 + y ^ 2 + (48 * x + 31 * y + 71 * z) ^ 2

/-- Coordinates of the nontrivial integral reflection of the `p=71` lattice. -/
def reflect71X (x y z : ℤ) : ℤ := 37 * x + 24 * y + 54 * z
def reflect71Y (x y z : ℤ) : ℤ := -30 * x - 19 * y - 45 * z
def reflect71Z (x y z : ℤ) : ℤ := -12 * x - 8 * y - 17 * z

/-- The discovered reflection is an isometry of the exact integral ternary lattice. -/
theorem reflect71_preserves_norm (x y z : ℤ) :
    reflectiveNorm71 (reflect71X x y z) (reflect71Y x y z) (reflect71Z x y z)
      = reflectiveNorm71 x y z := by
  simp [reflectiveNorm71, reflect71X, reflect71Y, reflect71Z]
  ring

/-- The reflection squares to the identity, first coordinate. -/
theorem reflect71_involutive_x (x y z : ℤ) :
    reflect71X (reflect71X x y z) (reflect71Y x y z) (reflect71Z x y z) = x := by
  simp [reflect71X, reflect71Y, reflect71Z]
  ring

/-- The reflection squares to the identity, second coordinate. -/
theorem reflect71_involutive_y (x y z : ℤ) :
    reflect71Y (reflect71X x y z) (reflect71Y x y z) (reflect71Z x y z) = y := by
  simp [reflect71X, reflect71Y, reflect71Z]
  ring

/-- The reflection squares to the identity, third coordinate. -/
theorem reflect71_involutive_z (x y z : ℤ) :
    reflect71Z (reflect71X x y z) (reflect71Y x y z) (reflect71Z x y z) = z := by
  simp [reflect71X, reflect71Y, reflect71Z]
  ring

/-- The residue-restricted doubled exponent for the `(1,11,34)` triple.  The constant
`c0` selects one bilateral branch above the target residue `61 mod 71`. -/
def restrictedTripleExp2_71
    (negative1 negative2 negative3 : Bool) (c0 x y z : ℤ) : ℤ :=
  quintExp2 negative1 71 1 x
    + quintExp2 negative2 71 11 y
    + quintExp2 negative3 71 34 (48 * x + 31 * y + c0 + 71 * z)

/-- The linear residue expression `sum i_s*(3*n_s+b_s)` after the `p=71` substitution. -/
def restrictedLinearResidue71 (b1 b2 b3 c0 x y z : ℤ) : ℤ :=
  3 * x + b1 + 11 * (3 * y + b2)
    + 34 * (3 * (48 * x + 31 * y + c0 + 71 * z) + b3)

/-- Once the branch constant has the displayed form, the substitution lands in residue `61`
modulo `71`. -/
theorem restrictedLinearResidue71_eq
    (b1 b2 b3 c0 q x y z : ℤ)
    (hconstant : b1 + 11 * b2 + 34 * b3 + 102 * c0 = 61 + 71 * q) :
    restrictedLinearResidue71 b1 b2 b3 c0 x y z
      = 61 + 71 * (69 * x + 45 * y + 102 * z + q) := by
  rw [restrictedLinearResidue71]
  linear_combination hconstant

/-- The eight branch constants used by the certificate all solve the residue-`61` constraint. -/
theorem p71_branch_residue_constants :
    (0 + 11 * 0 + 34 * 0 + 102 * 18 = 61 + 71 * 25)
    ∧ (0 + 11 * 0 + 34 * 1 + 102 * 65 = 61 + 71 * 93)
    ∧ (0 + 11 * 1 + 34 * 0 + 102 * 52 = 61 + 71 * 74)
    ∧ (0 + 11 * 1 + 34 * 1 + 102 * 28 = 61 + 71 * 40)
    ∧ (1 + 11 * 0 + 34 * 0 + 102 * 34 = 61 + 71 * 48)
    ∧ (1 + 11 * 0 + 34 * 1 + 102 * 10 = 61 + 71 * 14)
    ∧ (1 + 11 * 1 + 34 * 0 + 102 * 68 = 61 + 71 * 97)
    ∧ (1 + 11 * 1 + 34 * 1 + 102 * 44 = 61 + 71 * 63) := by
  norm_num

/-- Affine application of the reflection, with a branch-dependent translation. -/
def reflect71AffineX (cx x y z : ℤ) : ℤ := reflect71X x y z + cx
def reflect71AffineY (cy x y z : ℤ) : ℤ := reflect71Y x y z + cy
def reflect71AffineZ (cz x y z : ℤ) : ℤ := reflect71Z x y z + cz

/-- Branch `000` pairs with branch `010`, reversing sign and preserving exponent. -/
theorem p71_branch_pair_000_010 (x y z : ℤ) :
    restrictedTripleExp2_71 false false false 18 x y z
      = restrictedTripleExp2_71 false true false 52
          (reflect71AffineX 14 x y z) (reflect71AffineY (-12) x y z)
          (reflect71AffineZ (-5) x y z) := by
  simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY, reflect71AffineZ,
    reflect71X, reflect71Y, reflect71Z, quintExp2, quintExpA2, quintExpB2]
  ring

/-- Branch `011` pairs with branch `001`, reversing sign and preserving exponent. -/
theorem p71_branch_pair_011_001 (x y z : ℤ) :
    restrictedTripleExp2_71 false true true 28 x y z
      = restrictedTripleExp2_71 false false true 65
          (reflect71AffineX 22 x y z) (reflect71AffineY (-18) x y z)
          (reflect71AffineZ (-8) x y z) := by
  simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY, reflect71AffineZ,
    reflect71X, reflect71Y, reflect71Z, quintExp2, quintExpA2, quintExpB2]
  ring

/-- Branch `101` pairs with branch `111`, reversing sign and preserving exponent. -/
theorem p71_branch_pair_101_111 (x y z : ℤ) :
    restrictedTripleExp2_71 true false true 10 x y z
      = restrictedTripleExp2_71 true true true 44
          (reflect71AffineX 8 x y z) (reflect71AffineY (-7) x y z)
          (reflect71AffineZ (-3) x y z) := by
  simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY, reflect71AffineZ,
    reflect71X, reflect71Y, reflect71Z, quintExp2, quintExpA2, quintExpB2]
  ring

/-- Branch `110` pairs with branch `100`, reversing sign and preserving exponent. -/
theorem p71_branch_pair_110_100 (x y z : ℤ) :
    restrictedTripleExp2_71 true true false 68 x y z
      = restrictedTripleExp2_71 true false false 34
          (reflect71AffineX 52 x y z) (reflect71AffineY (-43) x y z)
          (reflect71AffineZ (-17) x y z) := by
  simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY, reflect71AffineZ,
    reflect71X, reflect71Y, reflect71Z, quintExp2, quintExpA2, quintExpB2]
  ring

/-- The four exact equalities packaged as one reflective branch certificate. -/
theorem p71_reflective_branch_certificate :
    (∀ x y z, restrictedTripleExp2_71 false false false 18 x y z
      = restrictedTripleExp2_71 false true false 52
          (reflect71AffineX 14 x y z) (reflect71AffineY (-12) x y z)
          (reflect71AffineZ (-5) x y z))
    ∧ (∀ x y z, restrictedTripleExp2_71 false true true 28 x y z
      = restrictedTripleExp2_71 false false true 65
          (reflect71AffineX 22 x y z) (reflect71AffineY (-18) x y z)
          (reflect71AffineZ (-8) x y z))
    ∧ (∀ x y z, restrictedTripleExp2_71 true false true 10 x y z
      = restrictedTripleExp2_71 true true true 44
          (reflect71AffineX 8 x y z) (reflect71AffineY (-7) x y z)
          (reflect71AffineZ (-3) x y z))
    ∧ (∀ x y z, restrictedTripleExp2_71 true true false 68 x y z
      = restrictedTripleExp2_71 true false false 34
          (reflect71AffineX 52 x y z) (reflect71AffineY (-43) x y z)
          (reflect71AffineZ (-17) x y z)) := by
  exact ⟨p71_branch_pair_000_010, p71_branch_pair_011_001,
    p71_branch_pair_101_111, p71_branch_pair_110_100⟩

end Reflective71

end Ramanujan.MultiQuintuple
