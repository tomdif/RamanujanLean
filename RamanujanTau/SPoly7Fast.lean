/-
# Run-based normalization for the certificate checker

Inputs that are already sorted (normalized partial sums, or a sorted polynomial shifted by a monomial) are
merged as runs instead of being re-sorted from single terms. Soundness is again just preservation of the
evaluated sum.
-/
import RamanujanTau.SPoly7

set_option autoImplicit false

namespace SPoly7

/-- normal form of a list of runs. -/
def normRuns (runs : List Poly) : Poly := collapse (sortRuns 64 runs)

/-- `p · q` as `|q|` runs (each sorted when `p` is): `p` shifted by each term of `q`. -/
def mulRuns (p q : Poly) : List Poly := q.map fun s => p.map fun t => (t.1 + s.1, t.2 * s.2)

def noCarryR (p q : Poly) : Bool := q.all fun s => p.all fun t => dec (t.1 + s.1) == ladd (dec t.1) (dec s.1)

/-- `target = Σ aᵢ gᵢ`, run-based. -/
def certifyR (pairs : List (Poly × Poly)) (target : Poly) : Bool :=
  (pairs.all fun ag => noCarryR ag.1 ag.2) &&
    normRuns ((pairs.flatMap fun ag => mulRuns ag.1 ag.2) ++ [negP target]) == []

/-- `Σ runs = target`. -/
def eqRuns (runs : List Poly) (target : Poly) : Bool := normRuns (runs ++ [negP target]) == []

section Eval
variable {R : Type*} [CommRing R]

lemma evalP_normRuns (x : List R) (runs : List Poly) : evalP x (normRuns runs) = (runs.map (evalP x)).sum := by
  rw [normRuns, evalP_collapse, evalP_sortRuns]

lemma evalP_shift (x : List R) (p : Poly) (s : Mono × ℤ) (h : (p.all fun t => dec (t.1 + s.1) == ladd (dec t.1) (dec s.1)) = true) :
    evalP x (p.map fun t => (t.1 + s.1, t.2 * s.2)) = evalP x p * ((s.2 : R) * evalM x s.1) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons]
    rw [evalP_cons, evalP_cons, ih h.2, evalM, evalM, evalM, h.1, evalL_ladd]; push_cast; ring

lemma sum_mulRuns (x : List R) (p q : Poly) (h : noCarryR p q = true) :
    ((mulRuns p q).map (evalP x)).sum = evalP x p * evalP x q := by
  induction q with
  | nil => simp [mulRuns]
  | cons s q ih =>
    simp only [noCarryR, List.all_cons, Bool.and_eq_true] at h
    simp only [mulRuns, List.map_cons, List.sum_cons] at ih ⊢
    rw [evalP_shift x p s h.1, ih (by simpa [noCarryR] using h.2), evalP_cons]; ring

lemma sum_flatMap_mulRuns (x : List R) (pairs : List (Poly × Poly)) (h1 : (pairs.all fun ag => noCarryR ag.1 ag.2) = true) :
    ((pairs.flatMap fun ag => mulRuns ag.1 ag.2).map (evalP x)).sum
      = (pairs.map fun ag => evalP x ag.1 * evalP x ag.2).sum := by
  induction pairs with
  | nil => simp
  | cons ag rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h1
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_mulRuns x _ _ h1.1, ih h1.2, List.map_cons,
      List.sum_cons]

theorem certifyR_sound (x : List R) (pairs : List (Poly × Poly)) (target : Poly) (h : certifyR pairs target = true) :
    evalP x target = (pairs.map fun ag => evalP x ag.1 * evalP x ag.2).sum := by
  simp only [certifyR, Bool.and_eq_true, beq_iff_eq] at h
  have := congrArg (evalP x) h.2
  rw [evalP_normRuns, evalP_nil, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, evalP_negP] at this
  rw [sum_flatMap_mulRuns x pairs h.1] at this
  linear_combination -this

theorem eqRuns_sound (x : List R) (runs : List Poly) (target : Poly) (h : eqRuns runs target = true) :
    evalP x target = (runs.map (evalP x)).sum := by
  have h0 : normRuns (runs ++ [negP target]) = [] := by simpa [eqRuns] using h
  have := congrArg (evalP x) h0
  rw [evalP_normRuns, evalP_nil, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, evalP_negP] at this
  linear_combination -this

end Eval

end SPoly7
