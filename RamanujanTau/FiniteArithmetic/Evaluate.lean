import RamanujanTau.FiniteArithmetic.Orbit
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Vector.Basic

/-!
# Evaluation by repeated squaring

The finite matrix is materialized after each product. This matters because
`Matrix` is a function type: composing unevaluated matrix-entry functions would
recompute entries when subsequently queried. `Vector.ofFn` stores each entry.
`matrixPower_eq` proves that the evaluator returns the exact matrix power.
-/

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic
open Matrix

variable {R : Type*} {d : ℕ}

/-- A data type, rather than a function returning entries. Keeping this type
throughout exponentiation prevents compiler eta expansion from deferring the
construction of the stored intermediate matrices. -/
abbrev StoredMatrix (R : Type*) (d : ℕ) := Vector (Vector R d) d

def storeMatrix (A : Matrix (Fin d) (Fin d) R) : StoredMatrix R d :=
  Vector.ofFn fun i => Vector.ofFn (A i)

def readMatrix (A : StoredMatrix R d) : Matrix (Fin d) (Fin d) R :=
  fun i j => A[i][j]

@[simp] theorem read_store (A : Matrix (Fin d) (Fin d) R) :
    readMatrix (storeMatrix A) = A := by
  ext i j
  simp [readMatrix, storeMatrix]

variable [CommRing R]

def storedMul (A B : StoredMatrix R d) : StoredMatrix R d :=
  storeMatrix (readMatrix A * readMatrix B)

/-- Binary matrix exponentiation, storing every intermediate product. -/
def storedPower (A : StoredMatrix R d) (n : ℕ) : StoredMatrix R d :=
  if hn : n = 0 then storeMatrix 1 else
    let B := storedPower A (n / 2)
    let C := storedMul B B
    if n % 2 = 0 then C else storedMul C A
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem storedPower_eq (A : StoredMatrix R d) (n : ℕ) :
    readMatrix (storedPower A n) = readMatrix A ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [storedPower]
    split_ifs with hn he
    · simp [hn]
    · dsimp only
      rw [storedMul, read_store, ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),
        ← pow_add]
      congr 1
      omega
    · dsimp only
      rw [storedMul, read_store, storedMul, read_store,
        ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)), ← pow_add, ← pow_succ]
      congr 1
      omega

def matrixPower (A : Matrix (Fin d) (Fin d) R) (n : ℕ) : Matrix (Fin d) (Fin d) R :=
  readMatrix (storedPower (storeMatrix A) n)

theorem matrixPower_eq (A : Matrix (Fin d) (Fin d) R) (n : ℕ) :
    matrixPower A n = A ^ n := by
  rw [matrixPower, storedPower_eq, read_store]

/-- The computed finite state is the actual linear-operator iterate. -/
theorem evaluate_eq (A : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (n : ℕ) :
    (matrixPower A n) *ᵥ v = (A.toLin' ^ n) v := by
  rw [matrixPower_eq, ← Matrix.toLin'_apply, Matrix.toLin'_pow]

/-- A proved arithmetic model turns binary matrix evaluation into a certified
answer in its target space. -/
theorem OrbitModel.evaluate {M : Type*} [AddCommGroup M] [Module R M]
    {T : Module.End R M} {f : M} (C : OrbitModel T f)
    (A : Matrix (Fin C.dimension) (Fin C.dimension) R)
    (hA : A.toLin' = C.transition) (n : ℕ) :
    C.synthesize ((matrixPower A n) *ᵥ C.initial) = (T ^ n) f := by
  rw [evaluate_eq, hA, ← C.realizes]

end RamanujanTau.FiniteArithmetic
