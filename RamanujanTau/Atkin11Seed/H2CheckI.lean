/-
# H2 kernel checks, part I: the four identities modulo `P`

* `I1`: `V(z)·(S₂² − S₂S₃ − S₃P') + 11·Y¹²·P'² ≡ 0` (R1 for `(S₂, S₃)/P'`);
* `I2`: `V(z)·(S₃²P' − S₂³ + S₂S₃P') + Y¹²·P'³ ≡ 0` (R2);
* `I3`: `P'·S₄ ≡ S₂² − P'·S₃` (`g₄ = g₂² − g₃`);
* `I4`: `P'·S₆ ≡ S₂·S₄` (`g₆ = g₂g₄`).
-/
import RamanujanTau.Atkin11Seed.H2Data

set_option maxRecDepth 100000

namespace Atkin11Seed

theorem chkI1 : isZeroY (redP (addY (jmulY zJ (subY (subY PA PB) (mulY S3 dP)))
    (smulY 11 (mulY y12 (mulY dP dP))))) = true := by decide +kernel

theorem chkI2 : isZeroY (redP (addY (jmulY zJ (addY (subY (mulY PC3 dP) (addY PD0 (shiftY 10 PD1))) (mulY PB dP)))
    (mulY y12 (mulY dP (mulY dP dP))))) = true := by decide +kernel

theorem chkI3 : isZeroY (redP (addY (subY (mulY dP S4) PA) (mulY dP S3))) = true := by decide +kernel

theorem chkI4 : isZeroY (redP (subY (mulY dP S6) (mulY S2 S4))) = true := by decide +kernel

end Atkin11Seed
