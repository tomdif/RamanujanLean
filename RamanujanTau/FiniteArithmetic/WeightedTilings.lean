import RamanujanTau.FiniteArithmetic.Orbit
import RamanujanTau.FiniteArithmetic.Evaluate
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A second arithmetic family: exact weighted tiling counts

A strip is tiled by monomers (length one) and dominoes (length two). The sum
type records the first tile, so it enumerates each tiling once. Summing products
of tile weights gives a two-state representation over any commutative ring.
This includes integer counts, rational weights, and composite residue rings.

The representation is proved from the combinatorial sum. It is not inferred
from a finite sample of that sum. No claim about arbitrary probabilistic models
or planning problems is needed.
-/

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.WeightedTilings

/-- Tilings of a strip of length `n`. At length at least two, `inl` begins with
a monomer and `inr` with a domino. -/
def Tiling : ℕ → Type
  | 0 => Unit
  | 1 => Unit
  | n + 2 => Tiling (n + 1) ⊕ Tiling n

instance tilingFintype : (n : ℕ) → Fintype (Tiling n)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype Unit)
  | n + 2 => by
    letI := tilingFintype (n + 1)
    letI := tilingFintype n
    exact inferInstanceAs (Fintype (Tiling (n + 1) ⊕ Tiling n))

variable {R : Type*} [CommRing R]

/-- Product of monomer weights `a` and domino weights `b`. -/
def weight (a b : R) : (n : ℕ) → Tiling n → R
  | 0, _ => 1
  | 1, _ => a
  | n + 2, Sum.inl t => a * weight a b (n + 1) t
  | n + 2, Sum.inr t => b * weight a b n t

/-- The exact weighted sum over all tilings. -/
def count (a b : R) (n : ℕ) : R := ∑ t : Tiling n, weight a b n t

@[simp] theorem count_zero (a b : R) : count a b 0 = 1 := by
  simp [count, Tiling, weight]

@[simp] theorem count_one (a b : R) : count a b 1 = a := by
  simp [count, Tiling, weight]

/-- Splitting by the first tile proves the recurrence for the actual sum. -/
theorem count_succ_succ (a b : R) (n : ℕ) :
    count a b (n + 2) = a * count a b (n + 1) + b * count a b n := by
  change (∑ t : Tiling (n + 1) ⊕ Tiling n, weight a b (n + 2) t) = _
  rw [Fintype.sum_sum_type]
  simp only [weight, count, Finset.mul_sum]

theorem weight_one : ∀ (n : ℕ) (t : Tiling n), weight (1 : R) 1 n t = 1
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, Sum.inl t => by simp only [weight, weight_one (n + 1) t, mul_one]
  | n + 2, Sum.inr t => by simp only [weight, weight_one n t, mul_one]

/-- With unit weights this is the ordinary number of tilings. -/
theorem count_one_one (n : ℕ) :
    count (1 : R) 1 n = (Fintype.card (Tiling n) : R) := by
  simp [count, weight_one]

/-- The companion transition on `[next count, current count]`. -/
def step (a b : R) : Module.End R (Fin 2 → R) where
  toFun v := ![a * v 0 + b * v 1, v 0]
  map_add' := by intros; ext i; fin_cases i <;> simp; ring
  map_smul' := by intros; ext i; fin_cases i <;> simp; ring

def initial (a : R) : Fin 2 → R := ![a, 1]

/-- Every iterate is identified with the combinatorial weighted counts. -/
theorem iterate_count (a b : R) (n : ℕ) :
    (step a b ^ n) (initial a) = ![count a b (n + 1), count a b n] := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    ext i
    fin_cases i <;> simp [step, count_succ_succ]

/-- Shift on the space of entire arithmetic sequences. -/
def shift : Module.End R (ℕ → R) where
  toFun f := fun n => f (n + 1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Synthesize a whole sequence from two finite coordinates. -/
def synthesize (a b : R) : (Fin 2 → R) →ₗ[R] (ℕ → R) where
  toFun v := fun n => ((step a b ^ n) v) 1
  map_add' := by intros; ext n; simp
  map_smul' := by intros; ext n; simp

/-- The same interface used by the partition example, now instantiated with
exact weighted combinatorial sums. -/
def model (a b : R) : OrbitModel shift (count a b) where
  dimension := 2
  transition := step a b
  initial := initial a
  synthesize := synthesize a b
  seed := by
    ext n
    change ((step a b ^ n) (initial a)) 1 = count a b n
    rw [iterate_count]
    rfl
  intertwines := by
    apply LinearMap.ext
    intro v
    ext n
    change ((step a b ^ (n + 1)) v) 1 = ((step a b ^ n) (step a b v)) 1
    rw [pow_succ, Module.End.mul_apply]

/-- A finite vector relation that can be checked independently of the size of
the strips subsequently queried. -/
theorem certificate (a b : R) :
    (step a b ^ 2) (initial a) =
      ∑ i : Fin 2, (![b, a] : Fin 2 → R) i • (step a b ^ (i : ℕ)) (initial a) := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_two, pow_succ, Module.End.mul_apply, step, initial] <;> ring

/-- The common orbit theorem transports this finite certificate to all shifts
of the entire weighted-count sequence. -/
theorem certified_recurrence (a b : R) (n : ℕ) :
    (shift ^ (n + 2)) (count a b) =
      ∑ i : Fin 2, (![b, a] : Fin 2 → R) i • (shift ^ (n + (i : ℕ))) (count a b) :=
  (model a b).recurrence 2 ![b, a] (certificate a b) n

/-- A stored two-by-two matrix for executable evaluation. -/
def matrix (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, b; 1, 0]

theorem matrix_toLin (a b : R) : (matrix a b).toLin' = step a b := by
  apply LinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, matrix, step]

/-- Exact evaluation using repeated squaring, without enumerating tilings. -/
def evaluate (a b : R) (n : ℕ) : R :=
  ((matrixPower (matrix a b) n).mulVec (initial a)) 1

theorem evaluate_correct (a b : R) (n : ℕ) : evaluate a b n = count a b n := by
  unfold evaluate
  rw [evaluate_eq, matrix_toLin, iterate_count]
  rfl

end RamanujanTau.FiniteArithmetic.WeightedTilings
