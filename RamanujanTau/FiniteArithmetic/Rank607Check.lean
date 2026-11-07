import RamanujanTau.FiniteArithmetic.Rank607Program
import RamanujanTau.FiniteArithmetic.Rank607Coords

/-! # The finite check for the prime-607 minor

`finalCheck` is evaluated once by the kernel in `Rank607Final`. -/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank607Program
open Packed

abbrev mulS (a b : ℕ) : Option ℕ := mulR Q 102 mu a b
abbrev addS (a b : ℕ) : Option ℕ := addR Q 102 mu a b

/-- `Σ d_t row_t`, with every coordinate checked to be small. -/
def comboL : List ℕ → List ℕ → Option ℕ
  | [], _ => some 0
  | _ :: _, [] => none
  | d :: ds, r :: rs =>
    if d < 2 ^ 22 then do
      let t ← mulS d r
      let s ← comboL ds rs
      addS t s
    else none

/-- Canonical lanes. -/
def canon (a : ℕ) : ℕ := laneMap (fun _ v => v % Q) 7 0 a % x ^ 102

def coordAt (b : ℕ) : List ℕ := coordTable.getD (b - 1) []

def entryAt (i j : ℕ) : ℕ := (matrixTable.getD i []).getD j 0

/-- Coordinates of `L(1)` reproduce the row of `Φ`. -/
def baseOk (rs : Rows) (phiRow : ℕ) : Bool :=
  match comboL (coordAt 1) rs.ls with
  | some B => canon phiRow == canon B
  | none => false

/-- Applying the operator to `L(b)` gives the claimed prefix of `L(b+1)`. -/
def stepOk (rs : Rows) (b : ℕ) : Bool :=
  match comboL (coordAt b) (if b % 2 = 1 then rs.us else rs.ds), comboL (coordAt (b + 1)) rs.ls with
  | some A, some B => canon A == canon B
  | _, _ => false

/-- Column `j` of the minor is read from the prefix of `L(2j+3)`. -/
def columnOk (rs : Rows) (j : ℕ) : Bool :=
  match comboL (coordAt (2 * j + 3)) rs.ls with
  | some B => (List.range 25).all fun i => lane (canon B) (i + 26) == entryAt i j
  | none => false

/-- The whole finite check. -/
def finalCheck : Bool :=
  match rows with
  | none => false
  | some (rs, phiRow) =>
    (List.range 54).all (fun b => decide ((coordAt b).length ≤ 102)) &&
    baseOk rs phiRow &&
    (List.range 52).all (fun b => stepOk rs (b + 1)) &&
    (List.range 25).all (fun j => columnOk rs j)

end RamanujanTau.FiniteArithmetic.Rank607Program
