/-
# A kernel-checked sparse-polynomial certificate checker

Polynomials are lists of terms `(exponent list, integer coefficient)`; their meaning in a commutative ring `R`
at a point `x : List R` is `evalP x p = Σ c · ∏ xᵢ^{eᵢ}`. To certify an ideal-membership identity
`target = Σᵢ aᵢ·gᵢ` we form all products, append `−target`, sort by monomial (bottom-up merge sort), collapse
equal neighbours and check that nothing is left — a closed computation for `decide +kernel`.

Every step preserves the evaluated sum, even when the fuel runs out or the input is unsorted, so soundness
(`certify_sound`) needs no sortedness argument: sorting only makes the check succeed.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace SPoly6

/-- a monomial, packed in base `1024` (six exponents). -/
abbrev Mono := ℕ
abbrev Poly := List (Mono × ℤ)

/-- the six exponents of a packed monomial. -/
def dec (e : Mono) : List ℕ := [e % 1024, e / 1024 % 1024, e / 1048576 % 1024, e / 1073741824 % 1024, e / 1099511627776 % 1024,
  e / 1125899906842624 % 1024]

/-- exponent-wise sum of exponent lists. -/
def ladd : List ℕ → List ℕ → List ℕ
  | [], n => n
  | m, [] => m
  | a :: m, b :: n => (a + b) :: ladd m n

/-- packed terms: `N = e·2⁴⁸ + 2|c| + [c < 0]`. -/
def decTerm (N : ℕ) : Mono × ℤ :=
  let m := N % 281474976710656
  (N / 281474976710656, if m % 2 = 1 then -((m / 2 : ℕ) : ℤ) else ((m / 2 : ℕ) : ℤ))

def ofPacked (l : List ℕ) : Poly := l.map decTerm

/-! ### the operations (structural recursion only) -/

def mulTerm (m : Mono) (c : ℤ) (p : Poly) : Poly := p.map fun t => (m + t.1, c * t.2)

/-- no carries in the packed products `m + t.1`. -/
def noCarry (m : Mono) (p : Poly) : Bool := p.all fun t => dec (m + t.1) == ladd (dec m) (dec t.1)

def noCarryP (p q : Poly) : Bool := p.all fun t => noCarry t.1 q

/-- the (unsorted) product. -/
def mulP (p q : Poly) : Poly := p.flatMap fun t => mulTerm t.1 t.2 q

def negP (p : Poly) : Poly := p.map fun t => (t.1, -t.2)

/-- merge of two sorted lists (fuel; falls back to concatenation). -/
def merge : ℕ → Poly → Poly → Poly
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, x :: a, [] => x :: a
  | n + 1, x :: a, y :: b => if y.1 < x.1 then y :: merge n (x :: a) b else x :: merge n a (y :: b)

def mergePairs : List Poly → List Poly
  | a :: b :: rest => merge (a.length + b.length) a b :: mergePairs rest
  | l => l

def sortRuns : ℕ → List Poly → Poly
  | 0, l => l.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | n + 1, a :: b :: rest => sortRuns n (mergePairs (a :: b :: rest))

/-- bottom-up merge sort. -/
def sortP (p : Poly) : Poly := sortRuns 64 (p.map fun t => [t])

/-- combine adjacent equal monomials, dropping zeros. -/
def collapseAux (m : Mono) (c : ℤ) : Poly → Poly
  | [] => if c = 0 then [] else [(m, c)]
  | (m', c') :: rest =>
    if m = m' then collapseAux m (c + c') rest
    else if c = 0 then collapseAux m' c' rest else (m, c) :: collapseAux m' c' rest

def collapse : Poly → Poly
  | [] => []
  | (m, c) :: rest => collapseAux m c rest

/-- normal form. -/
def norm (p : Poly) : Poly := collapse (sortP p)

/-- the certificate check: `target = Σ aᵢ gᵢ`. -/
def certify (pairs : List (Poly × Poly)) (target : Poly) : Bool :=
  (pairs.all fun ag => noCarryP ag.1 ag.2) && norm ((pairs.flatMap fun ag => mulP ag.1 ag.2) ++ negP target) == []

/-! ### the semantics -/

section Eval
variable {R : Type*} [CommRing R]

def evalL : List R → List ℕ → R
  | [], _ => 1
  | _ :: _, [] => 1
  | x :: xs, e :: es => x ^ e * evalL xs es

def evalM (x : List R) (e : Mono) : R := evalL x (dec e)

def evalP (x : List R) (p : Poly) : R := (p.map fun t => (t.2 : R) * evalM x t.1).sum

lemma evalL_ladd (x : List R) (m n : List ℕ) : evalL x (ladd m n) = evalL x m * evalL x n := by
  induction x generalizing m n with
  | nil => simp [evalL]
  | cons y ys ih =>
    cases m with
    | nil => cases n <;> simp [ladd, evalL]
    | cons a m =>
      cases n with
      | nil => simp [ladd, evalL]
      | cons b n => simp only [ladd, evalL, ih, pow_add]; ring

@[simp] lemma evalP_nil (x : List R) : evalP x [] = 0 := by simp [evalP]

lemma evalP_cons (x : List R) (t : Mono × ℤ) (p : Poly) :
    evalP x (t :: p) = (t.2 : R) * evalM x t.1 + evalP x p := by simp [evalP]

lemma evalP_append (x : List R) (p q : Poly) : evalP x (p ++ q) = evalP x p + evalP x q := by
  simp [evalP]

lemma evalP_mulTerm (x : List R) (m : Mono) (c : ℤ) (p : Poly) (h : noCarry m p = true) :
    evalP x (mulTerm m c p) = (c : R) * evalM x m * evalP x p := by
  induction p with
  | nil => simp [mulTerm]
  | cons t p ih =>
    simp only [noCarry, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [mulTerm, List.map_cons] at ih ⊢
    rw [evalP_cons, evalP_cons, ih (by simpa [noCarry] using h.2), evalM, evalM, evalM, h.1, evalL_ladd]
    push_cast; ring

lemma evalP_mulP (x : List R) (p q : Poly) (h : noCarryP p q = true) :
    evalP x (mulP p q) = evalP x p * evalP x q := by
  induction p with
  | nil => simp [mulP]
  | cons t p ih =>
    simp only [noCarryP, List.all_cons, Bool.and_eq_true] at h
    simp only [mulP, List.flatMap_cons] at ih ⊢
    rw [evalP_append, evalP_mulTerm x _ _ _ h.1, ih (by simpa [noCarryP] using h.2), evalP_cons]; ring

lemma evalP_negP (x : List R) (p : Poly) : evalP x (negP p) = -evalP x p := by
  induction p with
  | nil => simp [negP]
  | cons t p ih =>
    simp only [negP, List.map_cons] at ih ⊢
    rw [evalP_cons, evalP_cons, ih]; push_cast; ring

lemma evalP_merge (x : List R) : ∀ (n : ℕ) (a b : Poly), evalP x (merge n a b) = evalP x a + evalP x b
  | 0, a, b => by rw [merge, evalP_append]
  | _ + 1, [], b => by simp [merge]
  | _ + 1, _ :: _, [] => by simp [merge]
  | n + 1, s :: a, t :: b => by
    rw [merge]
    split_ifs
    · simp only [evalP_cons, evalP_merge x n]; ring
    · simp only [evalP_cons, evalP_merge x n]; ring

lemma evalP_mergePairs (x : List R) : ∀ l : List Poly,
    ((mergePairs l).map (evalP x)).sum = (l.map (evalP x)).sum
  | a :: b :: rest => by
    rw [mergePairs, List.map_cons, List.sum_cons, evalP_merge, evalP_mergePairs x rest]
    simp only [List.map_cons, List.sum_cons]; ring
  | [] => by simp [mergePairs]
  | [a] => by simp [mergePairs]

lemma evalP_flatten (x : List R) (l : List Poly) : evalP x l.flatten = (l.map (evalP x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatten_cons, evalP_append, ih, List.map_cons, List.sum_cons]

lemma evalP_sortRuns (x : List R) : ∀ (n : ℕ) (l : List Poly), evalP x (sortRuns n l) = (l.map (evalP x)).sum
  | 0, l => by rw [sortRuns, evalP_flatten]
  | _ + 1, [] => by simp [sortRuns]
  | _ + 1, [a] => by simp [sortRuns]
  | n + 1, a :: b :: rest => by rw [sortRuns, evalP_sortRuns x n, evalP_mergePairs]

lemma evalP_sortP (x : List R) (p : Poly) : evalP x (sortP p) = evalP x p := by
  rw [sortP, evalP_sortRuns]
  induction p with
  | nil => simp
  | cons t p ih => simp only [List.map_cons, List.sum_cons, ih, evalP_cons, evalP_nil, add_zero]

lemma evalP_collapseAux (x : List R) (m : Mono) (c : ℤ) (p : Poly) :
    evalP x (collapseAux m c p) = (c : R) * evalM x m + evalP x p := by
  induction p generalizing m c with
  | nil => simp only [collapseAux]; split_ifs with h <;> simp [h, evalP]
  | cons t p ih =>
    obtain ⟨m', c'⟩ := t
    simp only [collapseAux]
    split_ifs with h1 h2
    · subst h1; rw [ih, evalP_cons]; push_cast; ring
    · rw [ih, evalP_cons, h2]; simp
    · rw [evalP_cons, ih, evalP_cons]

lemma evalP_collapse (x : List R) (p : Poly) : evalP x (collapse p) = evalP x p := by
  cases p with
  | nil => rfl
  | cons t p => obtain ⟨m, c⟩ := t; rw [collapse, evalP_collapseAux, evalP_cons]

lemma evalP_norm (x : List R) (p : Poly) : evalP x (norm p) = evalP x p := by
  rw [norm, evalP_collapse, evalP_sortP]

lemma evalP_flatMap_mul (x : List R) (pairs : List (Poly × Poly)) (h : (pairs.all fun ag => noCarryP ag.1 ag.2) = true) :
    evalP x (pairs.flatMap fun ag => mulP ag.1 ag.2) = (pairs.map fun ag => evalP x ag.1 * evalP x ag.2).sum := by
  induction pairs with
  | nil => simp
  | cons ag rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, evalP_append, evalP_mulP x _ _ h.1, ih h.2, List.map_cons, List.sum_cons]

/-- **soundness**: a successful check proves `target(x) = Σ aᵢ(x) gᵢ(x)` at every point. -/
theorem certify_sound (x : List R) (pairs : List (Poly × Poly)) (target : Poly) (h : certify pairs target = true) :
    evalP x target = (pairs.map fun ag => evalP x ag.1 * evalP x ag.2).sum := by
  simp only [certify, Bool.and_eq_true, beq_iff_eq] at h
  have := congrArg (evalP x) h.2
  rw [evalP_norm, evalP_append, evalP_negP, evalP_nil] at this
  rw [evalP_flatMap_mul x pairs h.1] at this
  linear_combination -this

/-- a check that a polynomial identity `p = q` holds identically. -/
def eqCheck (p q : Poly) : Bool := norm (p ++ negP q) == []

theorem eqCheck_sound (x : List R) (p q : Poly) (h : eqCheck p q = true) : evalP x p = evalP x q := by
  have h0 : norm (p ++ negP q) = [] := by simpa [eqCheck] using h
  have := congrArg (evalP x) h0
  rw [evalP_norm, evalP_append, evalP_negP, evalP_nil] at this
  linear_combination this

end Eval

/-! ### polynomial expressions (normalized products) -/

inductive PE
  | lit (p : Poly)
  | add (a b : PE)
  | sub (a b : PE)
  | mul (a b : PE)
  | smul (c : ℤ) (a : PE)
  | pow (a : PE) (n : ℕ)

def smulP (c : ℤ) (p : Poly) : Poly := p.map fun t => (t.1, c * t.2)

def powP (p : Poly) : ℕ → Poly
  | 0 => [(0, 1)]
  | n + 1 => norm (mulP (powP p n) p)

def powOk (p : Poly) : ℕ → Bool
  | 0 => true
  | n + 1 => powOk p n && noCarryP (powP p n) p

def PE.toPoly : PE → Poly
  | .lit p => p
  | .add a b => norm (a.toPoly ++ b.toPoly)
  | .sub a b => norm (a.toPoly ++ negP b.toPoly)
  | .mul a b => norm (mulP a.toPoly b.toPoly)
  | .smul c a => smulP c a.toPoly
  | .pow a n => powP a.toPoly n

def PE.ok : PE → Bool
  | .lit _ => true
  | .add a b => a.ok && b.ok
  | .sub a b => a.ok && b.ok
  | .mul a b => a.ok && b.ok && noCarryP a.toPoly b.toPoly
  | .smul _ a => a.ok
  | .pow a n => a.ok && powOk a.toPoly n

section EvalPE
variable {R : Type*} [CommRing R]

def PE.eval (x : List R) : PE → R
  | .lit p => evalP x p
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .mul a b => a.eval x * b.eval x
  | .smul c a => (c : R) * a.eval x
  | .pow a n => a.eval x ^ n

lemma evalP_smulP (x : List R) (c : ℤ) (p : Poly) : evalP x (smulP c p) = (c : R) * evalP x p := by
  induction p with
  | nil => simp [smulP]
  | cons t p ih =>
    simp only [smulP, List.map_cons] at ih ⊢
    rw [evalP_cons, evalP_cons, ih]; push_cast; ring

lemma evalL_zeros : ∀ (x : List R) (n : ℕ), evalL x (List.replicate n 0) = 1
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => by rw [List.replicate_succ, evalL, pow_zero, one_mul, evalL_zeros xs n]

lemma evalP_powP (x : List R) (p : Poly) : ∀ n, powOk p n = true → evalP x (powP p n) = evalP x p ^ n
  | 0, _ => by
    simp only [powP, evalP, evalM, List.map, List.sum_cons, List.sum_nil, pow_zero, add_zero, Int.cast_one, one_mul]
    exact evalL_zeros x 6
  | n + 1, h => by
    simp only [powOk, Bool.and_eq_true] at h
    rw [powP, evalP_norm, evalP_mulP x _ _ h.2, evalP_powP x p n h.1, pow_succ]

lemma PE.eval_toPoly (x : List R) : ∀ e : PE, e.ok = true → evalP x e.toPoly = e.eval x
  | .lit p, _ => rfl
  | .add a b, h => by
    simp only [PE.ok, Bool.and_eq_true] at h
    rw [PE.toPoly, evalP_norm, evalP_append, PE.eval_toPoly x a h.1, PE.eval_toPoly x b h.2]; rfl
  | .sub a b, h => by
    simp only [PE.ok, Bool.and_eq_true] at h
    rw [PE.toPoly, evalP_norm, evalP_append, evalP_negP, PE.eval_toPoly x a h.1, PE.eval_toPoly x b h.2,
      ← sub_eq_add_neg]; rfl
  | .mul a b, h => by
    simp only [PE.ok, Bool.and_eq_true] at h
    rw [PE.toPoly, evalP_norm, evalP_mulP x _ _ h.2, PE.eval_toPoly x a h.1.1, PE.eval_toPoly x b h.1.2]; rfl
  | .smul c a, h => by
    rw [PE.toPoly, evalP_smulP, PE.eval_toPoly x a h]; rfl
  | .pow a n, h => by
    simp only [PE.ok, Bool.and_eq_true] at h
    rw [PE.toPoly, evalP_powP x _ n h.2, PE.eval_toPoly x a h.1]; rfl

/-- `p = e` for a polynomial and an expression. -/
def eqCheckPE (p : Poly) (e : PE) : Bool := e.ok && eqCheck p e.toPoly

theorem eqCheckPE_sound (x : List R) (p : Poly) (e : PE) (h : eqCheckPE p e = true) : evalP x p = e.eval x := by
  simp only [eqCheckPE, Bool.and_eq_true] at h
  rw [eqCheck_sound x p e.toPoly h.2, PE.eval_toPoly x e h.1]

end EvalPE

end SPoly6
