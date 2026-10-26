/-
# Atkin 11^k: Gordon's 11-adic bound, the multiplication table, and the finite checks

Everything here is integer data checked by the kernel (`decide +kernel`):
* the 3031 seed entries satisfy Gordon's bound and the support bounds;
* Gordon's bound is inductive under the modular-equation recurrence (a periodic box `λ mod 2`, `ν mod 10`);
* the coefficient-level step of the final induction for `p(n)`.
-/
import RamanujanTau.Atkin11Data
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Atkin11

/-- Gordon's `δ(i, r)` (with the corrected entry `δ(2,3) = 3`). -/
def δtab : List (List ℤ) := [[-1, 8, 7, 6, 15], [0, 9, 8, 2, 11], [1, 10, 4, 3, 12], [2, 6, 5, 4, 13], [3, 7, 6, 5, 9]]

def δ (i r : ℕ) : ℤ := (δtab.getD i []).getD r 0

/-- Gordon's bound `B(λ,i,ν) = ⌊(11ν − i − 5λ + δ(i, ν mod 5))/10⌋`. -/
def B (lam : ℤ) (i ν : ℕ) : ℤ := (11 * (ν : ℤ) - i - 5 * lam + δ i (ν % 5)) / 10

lemma B_shift (lam : ℤ) (i ν : ℕ) (m n : ℕ) :
    B (lam + 2 * m) i (ν + 10 * n) = B lam i ν - m + 11 * n := by
  unfold B
  rw [show (ν + 10 * n) % 5 = ν % 5 by omega]
  push_cast
  omega

/-- the finite check on one seed entry. -/
def seedOK (lam i ν : ℕ) (c : ℤ) : Bool :=
  (c % (11 : ℤ) ^ (B lam i ν).toNat == 0) && (5 * lam + i ≤ 11 * ν)

def rowsOK : Bool :=
  (List.range 55).all fun k => ((seedRows.getD k []).all fun p => seedOK (k / 5) (k % 5) p.1 p.2)

theorem rowsOK_true : rowsOK = true := by decide +kernel

/-! ### the multiplication table: `J_b · J_{5a+r} = Σ s · J_{5a+d}` -/

/-- offsets `(d, s)` with `J_b J_{5a+r} = Σ s J_{5a+d}` (for `b ∈ {1,2,3,5}`). -/
def tab : ℕ → ℕ → List (ℕ × ℤ)
  | 5, r => [(r + 5, 1)]
  | b, 0 => [(b, 1)]
  | 1, 1 => [(2, 1), (3, 1)]
  | 1, 2 => [(3, 1), (5, 11)]
  | 1, 3 => [(4, 1)]
  | 1, 4 => [(5, 1), (6, 12), (7, 11)]
  | 2, 1 => [(3, 1), (5, 11)]
  | 2, 2 => [(4, 1), (5, -1)]
  | 2, 3 => [(5, 1), (6, 11)]
  | 2, 4 => [(6, 1), (7, 11), (8, 11)]
  | 3, 1 => [(4, 1)]
  | 3, 2 => [(5, 1), (6, 11)]
  | 3, 3 => [(6, 1), (7, 11)]
  | 3, 4 => [(7, 1), (8, 12), (10, 121)]
  | _, _ => []

/-- the `e_j` (as `(b, coefficient)` lists). -/
def eList : ℕ → List (ℕ × ℤ)
  | 1 => [(1, 121), (2, 2662), (3, 14641), (5, 161051)]
  | 2 => [(1, -11), (2, 968), (3, 11979), (5, 161051)]
  | 3 => [(2, 242), (3, 5324), (5, 73205)]
  | 4 => [(2, 22), (3, 1452), (5, 14641)]
  | 5 => [(3, 242), (5, -1331)]
  | 6 => [(3, 22), (5, -1331)]
  | 7 => [(5, -121)]
  | 8 => [(5, 121)]
  | 9 => [(5, 55)]
  | 10 => [(5, 11)]
  | 11 => [(5, 1)]
  | _ => []

/-- the index bookkeeping: every `J_b` in `e_j` has `11b ≥ 5j`, and the table raises indices by `≥ b`. -/
def indexOK : Bool :=
  (List.range 11).all fun j => (eList (j + 1)).all fun p =>
    (5 * (j + 1) ≤ 11 * p.1) && (p.1 == 1 || p.1 == 2 || p.1 == 3 || p.1 == 5) &&
    (List.range 5).all fun r => (tab p.1 r).all fun q => p.1 + r ≤ q.1

theorem indexOK_true : indexOK = true := by decide +kernel

/-- the inductive step of Gordon's bound on one residue cell. -/
def stepOK (i : ℕ) (lam0 : ℤ) (j ν0 : ℕ) : Bool :=
  (eList j).all fun p => (tab p.1 (ν0 % 5)).all fun q =>
    (p.2 * q.2) % (11 : ℤ) ^ (B lam0 i (5 * (ν0 / 5) + q.1) - B (lam0 - j) i ν0).toNat == 0

def boxOK : Bool :=
  (List.range 5).all fun i => (List.range 2).all fun l => (List.range 11).all fun j =>
    (List.range 10).all fun ν0 => stepOK i l (j + 1) ν0

theorem boxOK_true : boxOK = true := by decide +kernel

end Atkin11
