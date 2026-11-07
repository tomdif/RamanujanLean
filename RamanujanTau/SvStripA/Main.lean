/-
# `SvStripA/` — `docs/SKQF_PROOF.md` §4 steps 1–2 (complex local closed forms, holomorphy,
complex Cholesky of the `s`-twisted kernel).  All level 1 (unconditional; no Deligne).

Build: `nice -n 10 lake build RamanujanTau.SvStripA.Main`.

* `Chol`: `cholK` — the local LDLᵀ over any field.
* `Local`: `Nx_succ`, `Dx_mul_P` (`D(x)P(x) = 1 + x`), `Dx_ne_zero`, `Nx_eq_rhoPx_mul`,
  `NpC_div_DpC`, `rhoC_eq_rhoCF` (closed forms for `Re s > 11/20`), `norm_rhoPx_le`, `norm_WcK_le`.
* `Decomp`: `loc_cholC`, `KqC_prod`, `qDecompC` (`K^{[s]} = Σ_{d|(h,k)} W U U`, `Re s > 0`).
* `Holo`: `diff_rhoCF`, `diff_WdC`, `diff_UdC`, `diff_KqC`, `SvC_ofReal`, `diff_SvC`,
  `svStripHyp_of_bound : SvCBound c' → SKQFProof.SvStripHyp c'`.
-/
import RamanujanTau.SvStripA.Holo

#print axioms RamanujanTau.SvStripA.cholK
#print axioms RamanujanTau.SvStripA.Nx_succ
#print axioms RamanujanTau.SvStripA.Dx_mul_P
#print axioms RamanujanTau.SvStripA.Dx_ne_zero
#print axioms RamanujanTau.SvStripA.Nx_eq_rhoPx_mul
#print axioms RamanujanTau.SvStripA.NpC_div_DpC
#print axioms RamanujanTau.SvStripA.rhoC_eq_rhoCF
#print axioms RamanujanTau.SvStripA.norm_rhoPx_le
#print axioms RamanujanTau.SvStripA.norm_WcK_le
#print axioms RamanujanTau.SvStripA.loc_cholC
#print axioms RamanujanTau.SvStripA.KqC_prod
#print axioms RamanujanTau.SvStripA.qDecompC
#print axioms RamanujanTau.SvStripA.diff_rhoCF
#print axioms RamanujanTau.SvStripA.diff_WdC
#print axioms RamanujanTau.SvStripA.diff_UdC
#print axioms RamanujanTau.SvStripA.diff_KqC
#print axioms RamanujanTau.SvStripA.SvC_ofReal
#print axioms RamanujanTau.SvStripA.diff_SvC
#print axioms RamanujanTau.SvStripA.svStripHyp_of_bound
