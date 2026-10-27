/-
# Run-based normalization of polynomial expressions

`PE.toPolyR` normalizes an expression by merging sorted runs (`normRuns`, `mulRuns`) instead of re-sorting
single terms. `eqCheckPER p e` checks `p = e`. Soundness is again preservation of the evaluated sum.
-/
import RamanujanTau.SPolyFast

set_option autoImplicit false

namespace SPoly

def powR (p : Poly) : ℕ → Poly
  | 0 => [(0, 1)]
  | n + 1 => normRuns (mulRuns (powR p n) p)

def powOkR (p : Poly) : ℕ → Bool
  | 0 => true
  | n + 1 => powOkR p n && noCarryR (powR p n) p

def PE.toPolyR : PE → Poly
  | .lit p => p
  | .add a b => normRuns [a.toPolyR, b.toPolyR]
  | .sub a b => normRuns [a.toPolyR, negP b.toPolyR]
  | .mul a b => normRuns (mulRuns a.toPolyR b.toPolyR)
  | .smul c a => smulP c a.toPolyR
  | .pow a n => powR a.toPolyR n

def PE.okR : PE → Bool
  | .lit _ => true
  | .add a b => a.okR && b.okR
  | .sub a b => a.okR && b.okR
  | .mul a b => a.okR && b.okR && noCarryR a.toPolyR b.toPolyR
  | .smul _ a => a.okR
  | .pow a n => a.okR && powOkR a.toPolyR n

/-- `p = e`, run-based. -/
def eqCheckPER (p : Poly) (e : PE) : Bool := e.okR && normRuns [e.toPolyR, negP p] == []

section Eval
variable {R : Type*} [CommRing R]

lemma evalP_powR (x : List R) (p : Poly) : ∀ n, powOkR p n = true → evalP x (powR p n) = evalP x p ^ n
  | 0, _ => by
    simp only [powR, evalP, evalM, List.map, List.sum_cons, List.sum_nil, pow_zero, add_zero, Int.cast_one, one_mul]
    exact evalL_zeros x 5
  | n + 1, h => by
    simp only [powOkR, Bool.and_eq_true] at h
    rw [powR, evalP_normRuns, sum_mulRuns x _ _ h.2, evalP_powR x p n h.1, pow_succ]

lemma PE.eval_toPolyR (x : List R) : ∀ e : PE, e.okR = true → evalP x e.toPolyR = e.eval x
  | .lit p, _ => rfl
  | .add a b, h => by
    simp only [PE.okR, Bool.and_eq_true] at h
    simp only [PE.toPolyR, evalP_normRuns, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      PE.eval_toPolyR x a h.1, PE.eval_toPolyR x b h.2, PE.eval]
  | .sub a b, h => by
    simp only [PE.okR, Bool.and_eq_true] at h
    simp only [PE.toPolyR, evalP_normRuns, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      evalP_negP, PE.eval_toPolyR x a h.1, PE.eval_toPolyR x b h.2, PE.eval, ← sub_eq_add_neg]
  | .mul a b, h => by
    simp only [PE.okR, Bool.and_eq_true] at h
    rw [PE.toPolyR, evalP_normRuns, sum_mulRuns x _ _ h.2, PE.eval_toPolyR x a h.1.1, PE.eval_toPolyR x b h.1.2]
    rfl
  | .smul c a, h => by
    rw [PE.toPolyR, evalP_smulP, PE.eval_toPolyR x a h]; rfl
  | .pow a n, h => by
    simp only [PE.okR, Bool.and_eq_true] at h
    rw [PE.toPolyR, evalP_powR x _ n h.2, PE.eval_toPolyR x a h.1]; rfl

theorem eqCheckPER_sound (x : List R) (p : Poly) (e : PE) (h : eqCheckPER p e = true) : evalP x p = e.eval x := by
  simp only [eqCheckPER, Bool.and_eq_true, beq_iff_eq] at h
  have := congrArg (evalP x) h.2
  simp only [evalP_normRuns, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_negP,
    evalP_nil] at this
  rw [← PE.eval_toPolyR x e h.1]
  linear_combination -this

end Eval

end SPoly
