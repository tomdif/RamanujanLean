/-
# `SCS2Coprime/`: `Γ₀(q)` infrastructure for the two-sided shifted-convolution bound (checkpoint)

Build: `nice -n 10 lake build RamanujanTau.SCS2Coprime.Main`. See `docs/SCS2.md` §6.

Stage 1 (done): restricted Bruhat/Kloosterman with gcd-Weil, uniform in `q` (`Bruhat0`, `Gamma0`);
unfolding over any subgroup `H ≤ SL₂(ℤ)` via coset representatives (`Unfold`).
Stage 2 (started): `Ψ_{a,b}` invariance under `Γ₀(ab)` and its size (`TwoPointAB`).
-/
import RamanujanTau.SCS2Coprime.TwoPointAB

#print axioms RamanujanTau.SCS2Coprime.tsum_IγQ_eq
#print axioms RamanujanTau.SCS2Coprime.norm_tsum_IγQ_le_gK
#print axioms RamanujanTau.SCS2Coprime.norm_tsum_IγQ_le_gcd
#print axioms RamanujanTau.SCS2Coprime.mem_Gamma0_iff
#print axioms RamanujanTau.SCS2Coprime.tsum_Gamma0_Iγ
#print axioms RamanujanTau.SCS2Coprime.norm_tsum_Gamma0_Iγ_le
#print axioms RamanujanTau.SCS2Coprime.cosetEquiv
#print axioms RamanujanTau.SCS2Coprime.lintegral_unfold_sub
#print axioms RamanujanTau.SCS2Coprime.lintegral_unfold_inv
#print axioms RamanujanTau.SCS2Coprime.scl_smul
#print axioms RamanujanTau.SCS2Coprime.PsiAB_smul
#print axioms RamanujanTau.SCS2Coprime.PsiAB_smul_Gamma0
#print axioms RamanujanTau.SCS2Coprime.norm_PsiAB_le
