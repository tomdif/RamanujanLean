/-
# `SCS2/`: the two-sided shifted-convolution bound — milestone

Build: `nice -n 10 lake build RamanujanTau.SCS2.Main`. See `docs/SCS2.md`.

Proved (level 1): `scs2_trivial` (`SCS2 0 0`), `shiftSum2_mul_left` (gcd reduction),
`shiftSum2_eq_zero_of_not_dvd`, `shiftSum2_diag` (`a = b` is the one-sided sum), and
`scs2_diag`: `|S(a,a;ℓ)| ≤ C N^{1−1/21} |ℓ|^{1/21}`.
Open: coprime `a ≠ b` (needs `Γ₀(ab)` unfolding/Bruhat; see the doc, §2–§4).
-/
import RamanujanTau.SCS2.Basic

#print axioms RamanujanTau.SCS2.abs_shiftSum2_le
#print axioms RamanujanTau.SCS2.scs2_trivial
#print axioms RamanujanTau.SCS2.shiftSum2_mul_left
#print axioms RamanujanTau.SCS2.shiftSum2_eq_zero_of_not_dvd
#print axioms RamanujanTau.SCS2.shiftSum2_diag
#print axioms RamanujanTau.SCS2.scs2_diag
