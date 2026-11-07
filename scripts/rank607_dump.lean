import RamanujanTau.FiniteArithmetic.Rank607Program
open RamanujanTau.FiniteArithmetic.Rank607Program RamanujanTau.FiniteArithmetic.Packed

/-! Prints the rows used to regenerate the untrusted coordinate table. -/
def lanes (a n : Nat) : List Nat := (List.range n).map fun i => (a >>> (64 * i)) % 2 ^ 64

#eval do
  match rows with
  | none => IO.println "ROWS FAILED"
  | some (rs, phiRow) =>
    IO.println s!"PHI {lanes phiRow 102}"
    for l in rs.ls, u in rs.us, d in rs.ds do
      IO.println s!"R {lanes l 102} | {lanes u 102} | {lanes d 102}"
