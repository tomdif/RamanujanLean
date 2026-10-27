/-
# H2 kernel checks, part D: `S₂³` in two halves
-/
import RamanujanTau.Atkin11Seed.H2Data

set_option maxRecDepth 100000

namespace Atkin11Seed

theorem chkD0 : ckEq (mulY (PA.take 10) S2) PD0 = true := by decide +kernel

theorem chkD1 : ckEq (mulY (PA.drop 10) S2) PD1 = true := by decide +kernel

end Atkin11Seed
