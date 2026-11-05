/-
# Zero-free region for `L(Δ,s)` (de la Vallée-Poussin type; unconditional, Deligne-free)

Build: `nice -n 10 lake build RamanujanTau.ZeroFreeRegion.Main`. See `docs/ZERO_FREE_REGION.md`.

* `tauL_zero_free_region`: `∃ c > 0, ∃ t₀, tauL s = 0 → t₀ ≤ |Im s| → Re s ≤ 13/2 − c/log|Im s|`;
* `tauL_zero_free_region_left`: the mirror `11/2 + c/log|Im s| ≤ Re s`;
* `tauL_zero_free_region_uniform`: for every non-trivial zero,
  `11/2 + c/log(|Im s|+2) ≤ Re s ≤ 13/2 − c/log(|Im s|+2)`.
-/
import RamanujanTau.ZeroFreeRegion.Uniform

#print axioms RamanujanTau.ZeroFreeRegion.landau
#print axioms RamanujanTau.ZeroFreeRegion.differentiableAt_abelI
#print axioms RamanujanTau.ZeroFreeRegion.LSeries_eq_abel
#print axioms RamanujanTau.ZeroFreeRegion.norm_Fval_antitone
#print axioms RamanujanTau.ZeroFreeRegion.RS_ne_zero
#print axioms RamanujanTau.ZeroFreeRegion.Psi_real
#print axioms RamanujanTau.ZeroFreeRegion.four_le_order
#print axioms RamanujanTau.ZeroFreeRegion.norm_Psi_le
#print axioms RamanujanTau.ZeroFreeRegion.re_logDeriv_Psi_le
#print axioms RamanujanTau.ZeroFreeRegion.core
#print axioms RamanujanTau.ZeroFreeRegion.tauL_zero_free_region
#print axioms RamanujanTau.ZeroFreeRegion.tauL_zero_free_region_left
#print axioms RamanujanTau.ZeroFreeRegion.tauL_zero_free_region_uniform
