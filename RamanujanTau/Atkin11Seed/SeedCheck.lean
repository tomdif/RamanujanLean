/-
# The 55 seed checks

For `S ∈ {P', S₂, S₃, S₄, S₆}` (the numerators of `1, g₂, g₃, g₄, g₆`), `iterF` lists
`Y^λ S(Y) mod P` for `λ ≤ 10`. Each has degree `≤ 10`, and its `Y¹⁰` coefficient is `11 ×` the seed row
`C^λ_{i,·}` of `Atkin11Data`.
-/
import RamanujanTau.Atkin11Seed.SData
import RamanujanTau.Atkin11Data

set_option maxRecDepth 100000

namespace Atkin11Seed

def seedOK (i : Nat) : Bool :=
  let Fs := iterF 10 (redP (Snum i))
  (List.range 11).all fun lam =>
    let F := Fs.getD lam []
    decide (F.length ≤ 11) &&
      JE.isZero (JE.add (F.getD 10 JE.zero) (JE.smul (-11) (ofPairs (Atkin11.seedRows.getD (5 * lam + i) []))))

theorem seedOK_0 : seedOK 0 = true := by decide +kernel
theorem seedOK_1 : seedOK 1 = true := by decide +kernel
theorem seedOK_2 : seedOK 2 = true := by decide +kernel
theorem seedOK_3 : seedOK 3 = true := by decide +kernel
theorem seedOK_4 : seedOK 4 = true := by decide +kernel

end Atkin11Seed
