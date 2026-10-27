/-
# H2 kernel checks, part C: `S₃·S₃`
-/
import RamanujanTau.Atkin11Seed.H2Data

set_option maxRecDepth 100000

namespace Atkin11Seed

theorem chkC : ckEq (mulY S3 S3) PC3 = true := by decide +kernel

end Atkin11Seed
