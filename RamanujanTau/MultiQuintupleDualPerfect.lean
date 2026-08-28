/-
# A universal perfect-set certificate for Poisson-dual Watson support

Vector spanning is the first adaptive replacement for false fixed-shell
cutoffs.  For reconstructing an orthogonal cancellation map, the natural
stronger notion is perfection: the rank-one quadratic tensors `w*w^T` span
the six-dimensional space of ternary quadratic forms.

This file exhibits six universally supported scalar-zero dual vectors with
that property.  Four have norm `3*p^2` and two have norm `6*p^2`, so the first
perfect supported cutoff always exists by norm `6*p^2`.
-/
import RamanujanTau.MultiQuintupleDualPhase

namespace Ramanujan.MultiQuintuple

/-- Evaluation of a general ternary quadratic form, with the six independent
coefficients written explicitly. -/
def ternaryQuadraticEval
    (A B C D E F x y z : ℚ) : ℚ :=
  A * x ^ 2 + B * y ^ 2 + C * z ^ 2 +
    D * x * y + E * x * z + F * y * z

/-- Scaling a vector by `p` scales every ternary quadratic form by `p^2`. -/
theorem ternaryQuadraticEval_scale
    (A B C D E F p x y z : ℚ) :
    ternaryQuadraticEval A B C D E F (p * x) (p * y) (p * z) =
      p ^ 2 * ternaryQuadraticEval A B C D E F x y z := by
  simp only [ternaryQuadraticEval]
  ring

/-- **Perfect-set theorem.**

A rational ternary quadratic form vanishing on the six displayed directions
is the zero form.  Equivalently, their rank-one symmetric tensors span
`Sym^2(ℚ^3)`.  The associated six-by-six determinant is `144`. -/
theorem six_dual_directions_are_perfect
    (A B C D E F : ℚ)
    (h1 : ternaryQuadraticEval A B C D E F 1 1 1 = 0)
    (h2 : ternaryQuadraticEval A B C D E F (-1) 1 1 = 0)
    (h3 : ternaryQuadraticEval A B C D E F 1 (-1) 1 = 0)
    (h4 : ternaryQuadraticEval A B C D E F 1 1 (-1) = 0)
    (h5 : ternaryQuadraticEval A B C D E F 2 1 1 = 0)
    (h6 : ternaryQuadraticEval A B C D E F 1 2 1 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 ∧ F = 0 := by
  simp only [ternaryQuadraticEval] at h1 h2 h3 h4 h5 h6
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Scaling the six perfect directions by a nonzero rational `p` preserves
perfection. -/
theorem six_scaled_dual_directions_are_perfect
    (p A B C D E F : ℚ) (hp : p ≠ 0)
    (h1 : ternaryQuadraticEval A B C D E F p p p = 0)
    (h2 : ternaryQuadraticEval A B C D E F (-p) p p = 0)
    (h3 : ternaryQuadraticEval A B C D E F p (-p) p = 0)
    (h4 : ternaryQuadraticEval A B C D E F p p (-p) = 0)
    (h5 : ternaryQuadraticEval A B C D E F (2 * p) p p = 0)
    (h6 : ternaryQuadraticEval A B C D E F p (2 * p) p = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 ∧ F = 0 := by
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hunscale : ∀ x y z : ℚ,
      ternaryQuadraticEval A B C D E F (p * x) (p * y) (p * z) = 0 →
        ternaryQuadraticEval A B C D E F x y z = 0 := by
    intro x y z hscaled
    rw [ternaryQuadraticEval_scale] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left hp2
  apply six_dual_directions_are_perfect A B C D E F
  · exact hunscale 1 1 1 (by simpa using h1)
  · exact hunscale (-1) 1 1 (by simpa using h2)
  · exact hunscale 1 (-1) 1 (by simpa using h3)
  · exact hunscale 1 1 (-1) (by simpa using h4)
  · exact hunscale 2 1 1 (by simpa [mul_comm] using h5)
  · exact hunscale 1 2 1 (by simpa [mul_comm] using h6)

/-- Squared norm after applying a rational three-by-three matrix. -/
def ternaryMatrixImageNorm
    (a11 a12 a13 a21 a22 a23 a31 a32 a33 x y z : ℚ) : ℚ :=
  (a11 * x + a12 * y + a13 * z) ^ 2 +
    (a21 * x + a22 * y + a23 * z) ^ 2 +
    (a31 * x + a32 * y + a33 * z) ^ 2

/-- **Six-vector orthogonality certificate.**

If a rational linear map preserves the norms of the six scaled perfect
directions, then it preserves the norm of every rational ternary vector. -/
theorem ternaryMatrix_norm_preserving_of_six_vectors
    (p a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℚ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm
      a11 a12 a13 a21 a22 a23 a31 a32 a33 p (2 * p) p = 6 * p ^ 2) :
    ∀ x y z : ℚ,
      ternaryMatrixImageNorm
        a11 a12 a13 a21 a22 a23 a31 a32 a33 x y z =
          x ^ 2 + y ^ 2 + z ^ 2 := by
  let A := a11 ^ 2 + a21 ^ 2 + a31 ^ 2 - 1
  let B := a12 ^ 2 + a22 ^ 2 + a32 ^ 2 - 1
  let C := a13 ^ 2 + a23 ^ 2 + a33 ^ 2 - 1
  let D := 2 * (a11 * a12 + a21 * a22 + a31 * a32)
  let E := 2 * (a11 * a13 + a21 * a23 + a31 * a33)
  let F := 2 * (a12 * a13 + a22 * a23 + a32 * a33)
  have hdiff : ∀ x y z : ℚ,
      ternaryMatrixImageNorm
          a11 a12 a13 a21 a22 a23 a31 a32 a33 x y z -
        (x ^ 2 + y ^ 2 + z ^ 2) =
          ternaryQuadraticEval A B C D E F x y z := by
    intro x y z
    simp only [ternaryMatrixImageNorm, ternaryQuadraticEval, A, B, C, D, E, F]
    ring
  have q1 : ternaryQuadraticEval A B C D E F p p p = 0 := by
    rw [← hdiff]
    nlinarith
  have q2 : ternaryQuadraticEval A B C D E F (-p) p p = 0 := by
    rw [← hdiff]
    nlinarith
  have q3 : ternaryQuadraticEval A B C D E F p (-p) p = 0 := by
    rw [← hdiff]
    nlinarith
  have q4 : ternaryQuadraticEval A B C D E F p p (-p) = 0 := by
    rw [← hdiff]
    nlinarith
  have q5 : ternaryQuadraticEval A B C D E F (2 * p) p p = 0 := by
    rw [← hdiff]
    nlinarith
  have q6 : ternaryQuadraticEval A B C D E F p (2 * p) p = 0 := by
    rw [← hdiff]
    nlinarith
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ :=
    six_scaled_dual_directions_are_perfect
      p A B C D E F hp q1 q2 q3 q4 q5 q6
  intro x y z
  apply sub_eq_zero.mp
  rw [hdiff, hA, hB, hC, hD, hE, hF]
  simp [ternaryQuadraticEval]

/-- The two additional directions needed for perfection are universally
Watson-supported. -/
theorem dualWatsonSupported_twoOneOne
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k (2 * p) p p := by
  simpa [mul_comm] using dualWatsonSupported_notThreeCube
    p q i j k 2 1 1 hp (by norm_num) (by norm_num) (by norm_num)

theorem dualWatsonSupported_oneTwoOne
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p (2 * p) p := by
  simpa [mul_comm] using dualWatsonSupported_notThreeCube
    p q i j k 1 2 1 hp (by norm_num) (by norm_num) (by norm_num)

/-- All six directions in the perfect certificate are universally
Watson-supported. -/
theorem dualPerfectVectors_supported
    (p q i j k : ℤ) (hp : p ≠ 0) :
    DualWatsonSupported p q i j k p p p ∧
    DualWatsonSupported p q i j k (-p) p p ∧
    DualWatsonSupported p q i j k p (-p) p ∧
    DualWatsonSupported p q i j k p p (-p) ∧
    DualWatsonSupported p q i j k (2 * p) p p ∧
    DualWatsonSupported p q i j k p (2 * p) p := by
  constructor
  · exact dualWatsonSupported_ppp p q i j k hp
  constructor
  · simpa using dualWatsonSupported_notThreeCube
      p q i j k (-1) 1 1 hp (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact dualWatsonSupported_pnp p q i j k hp
  constructor
  · exact dualWatsonSupported_ppn p q i j k hp
  constructor
  · exact dualWatsonSupported_twoOneOne p q i j k hp
  · exact dualWatsonSupported_oneTwoOne p q i j k hp

/-- The six perfect supported vectors occur by norm `6*p^2`. -/
theorem dualPerfectVector_norms (p : ℤ) :
    ternaryNorm p p p = 3 * p ^ 2 ∧
    ternaryNorm (-p) p p = 3 * p ^ 2 ∧
    ternaryNorm p (-p) p = 3 * p ^ 2 ∧
    ternaryNorm p p (-p) = 3 * p ^ 2 ∧
    ternaryNorm (2 * p) p p = 6 * p ^ 2 ∧
    ternaryNorm p (2 * p) p = 6 * p ^ 2 := by
  simp only [ternaryNorm]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Three vectors in the perfect certificate already form a unimodular basis
after removing their common factor `p`. -/
theorem dualPerfectGenerators_det (p : ℤ) :
    ternaryDet p p p (2 * p) p p p (2 * p) p = p ^ 3 := by
  simp only [ternaryDet]
  ring

/-- Consequently those three vectors generate the entire scalar-zero lattice
`p * ℤ^3`, not merely its rational span. -/
theorem dualPerfectVectors_generate_scalarZero
    (p x y z : ℤ) :
    ∃ alpha beta gamma : ℤ,
      p * x = alpha * p + beta * (2 * p) + gamma * p ∧
      p * y = alpha * p + beta * p + gamma * (2 * p) ∧
      p * z = alpha * p + beta * p + gamma * p := by
  refine ⟨3 * z - x - y, x - z, y - z, ?_⟩
  constructor
  · ring
  constructor <;> ring

/-- Adding any scalar-one projective lift to the three unimodular scalar-zero
generators produces the entire integral projective dual lattice. -/
theorem projectiveDual_generated_by_unitLift_and_perfectVectors
    (p lambda i j k w1 w2 w3 z1 z2 z3 t1 t2 t3 : ℤ)
    (hw1 : w1 = lambda * i + p * z1)
    (hw2 : w2 = lambda * j + p * z2)
    (hw3 : w3 = lambda * k + p * z3) :
    ∃ alpha beta gamma : ℤ,
      w1 = lambda * (i + p * t1) +
        alpha * p + beta * (2 * p) + gamma * p ∧
      w2 = lambda * (j + p * t2) +
        alpha * p + beta * p + gamma * (2 * p) ∧
      w3 = lambda * (k + p * t3) +
        alpha * p + beta * p + gamma * p := by
  obtain ⟨alpha, beta, gamma, h1, h2, h3⟩ :=
    dualPerfectVectors_generate_scalarZero
      p (z1 - lambda * t1) (z2 - lambda * t2) (z3 - lambda * t3)
  refine ⟨alpha, beta, gamma, ?_⟩
  constructor
  · rw [hw1]
    linear_combination h1
  constructor
  · rw [hw2]
    linear_combination h2
  · rw [hw3]
    linear_combination h3

end Ramanujan.MultiQuintuple
