import RamanujanTau.FiniteArithmetic.WeightedTilings
import RamanujanTau.FiniteArithmetic.Partition29
import Mathlib.Algebra.Field.ZMod

/-! Executable examples. Their algorithms are connected to actual counting
problems by `WeightedTilings.evaluate_correct` and `Partition29.residue_correct`.
These printed runs are demonstrations; the correctness theorems cover every input. -/

open RamanujanTau.FiniteArithmetic

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 1000000000000
  IO.println s!"Partition family p((19*29^(1+2*t)+1)/24) mod 29, t={n}: {(Partition29.residue n).val}"
  IO.println s!"Strip length: {n}"
  IO.println s!"Unweighted tilings mod 29: {(WeightedTilings.evaluate (1 : ZMod 29) 1 n).val}"
  IO.println s!"Weighted tilings (monomer 2, domino 3) mod 841: {(WeightedTilings.evaluate (2 : ZMod 841) 3 n).val}"
  IO.println s!"Exact weighted tilings of length 40: {WeightedTilings.evaluate (2 : ℤ) 3 40}"
  IO.println s!"Rational weighted tilings of length 12 (weights 1/2, 1/3): {WeightedTilings.evaluate (1/2 : ℚ) (1/3) 12}"
