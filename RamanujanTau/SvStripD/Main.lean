/-
# `SvStripD/` — S4 of `docs/SKQF_PROOF.md` §4: complex local masses and the twisted Euler sum.

Build: `nice -n 10 lake build RamanujanTau.SvStripD.Main`.

* `Generic`: `TC_le_gen`, `TC_zero_split`, `TC_one_split` (generic complex local masses, level 1).
* `Local`: `γz_010`, `γz_001` (exact first-order cancellation), `Tz_zero_le`, `Tz_one_le`, `Tz_le`
  (L1z–L3z), `norm_W1_le`, `norm_We_le` (level 2, `[DeligneBound]`).
* `Euler`: `euler_fZ`, `euler_strip` (level 2).
* `Bridge`: `γz_bridge` (= `SvStripC.γz`), `MassZ_le_prod`, `s4_mass` (level 2).
* `Final`: **`s4Bound_deligne : S4Bound 4`** (level 2).
-/
import RamanujanTau.SvStripD.Final

#print axioms RamanujanTau.SvStripD.TC_le_gen
#print axioms RamanujanTau.SvStripD.TC_zero_split
#print axioms RamanujanTau.SvStripD.TC_one_split
#print axioms RamanujanTau.SvStripD.γz_010
#print axioms RamanujanTau.SvStripD.γz_001
#print axioms RamanujanTau.SvStripD.Tz_zero_le
#print axioms RamanujanTau.SvStripD.Tz_one_le
#print axioms RamanujanTau.SvStripD.Tz_le
#print axioms RamanujanTau.SvStripD.norm_W1_le
#print axioms RamanujanTau.SvStripD.norm_We_le
#print axioms RamanujanTau.SvStripD.euler_fZ
#print axioms RamanujanTau.SvStripD.euler_strip
#print axioms RamanujanTau.SvStripD.γz_bridge
#print axioms RamanujanTau.SvStripD.MassZ_le_prod
#print axioms RamanujanTau.SvStripD.s4_mass
#print axioms RamanujanTau.SvStripD.s4Bound_deligne
