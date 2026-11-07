import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Algebraic certificates for seed survival

These lemmas certify finite matrices and the projector lifting step. An
identification with the partition operator is a separate arithmetic obligation.
-/
namespace RamanujanTau.FiniteArithmetic

/-- The standard cubic correction lifts an idempotent when its error squares to zero.
This also applies to matrix rings modulo p². -/
theorem cubic_idempotent_lift {R : Type*} [Ring R] (a : R)
    (h : (a*a-a)*(a*a-a)=0) :
    (3*a*a-2*a*a*a)*(3*a*a-2*a*a*a) = 3*a*a-2*a*a*a := by
  apply sub_eq_zero.mp
  calc
    _ = (a*a-a)*(a*a-a)*(4*a*a-4*a-3) := by noncomm_ring
    _ = 0 := by rw [h]; simp

/-- A checked left inverse and a nonzero seed certify every iterate, over any
commutative ring. No finite numerical orbit is assumed to continue by extrapolation. -/
theorem matrix_seed_survives {R : Type*} [CommRing R] {d : ℕ}
    (T B : Matrix (Fin d) (Fin d) R) (h : B*T=1)
    (v : Fin d → R) (hv : v ≠ 0) (n : ℕ) : (T^n).mulVec v ≠ 0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    intro hz
    apply ih
    have hz' := congrArg B.mulVec hz
    simpa only [pow_succ',Matrix.mulVec_mulVec,← Matrix.mul_assoc,h,
      one_mul,Matrix.mulVec_zero] using hz'

end RamanujanTau.FiniteArithmetic
