/-
# H2 kernel checks, part A: `S₂·S₂`, `S₂·S₃`
-/
import RamanujanTau.Atkin11Seed.H2Data

set_option maxRecDepth 100000

namespace Atkin11Seed

theorem chkA : ckEq (mulY S2 S2) PA = true := by decide +kernel

theorem chkB : ckEq (mulY S2 S3) PB = true := by decide +kernel

end Atkin11Seed
