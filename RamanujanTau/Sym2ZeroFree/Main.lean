/-
# Zero-free region for `ζ(s)L(Sym²Δ,s) = ζ(2s)R(s)` and for `R(s) = Σ λ(n)² n^{−s}`
(de la Vallée-Poussin type; unconditional, Deligne-free, no GL(3)/Sym⁴ input)

Build: `nice -n 10 lake build RamanujanTau.Sym2ZeroFree.Main`. See `docs/SYM2_ZERO_FREE.md`.

`HH = R*/γ` is `ζ(2s)R(s) = L(Δ×Δ,s)` continued (`TauPNTUncond.Edge`), `KK = (s−1)HH`,
`Rcont = HH/ζ(2s)`, `Lsym2 = HH/ζ`.

* `HH_zero_free_region`: `∃ c > 0, ∃ t₀, HH s = 0 → t₀ ≤ |Im s| → Re s ≤ 1 − c/log|Im s|`
  (`c = 1/18144`);
* `KK_zero_free_region_uniform`: `∃ c > 0, KK s = 0 → Re s ≤ 1 − c/log(|Im s|+3)` (all heights,
  so no exceptional real zero; ineffective);
* `HH_ne_zero_region`, `Rcont_ne_zero_region`: `HH s ≠ 0`, `R(s) ≠ 0` for
  `Re s > 1 − c/log(|Im s|+3)`, `s ≠ 1`;
* `Lsym2_ne_zero_region`: the same for `Lsym2` where `ζ(s) ≠ 0`.

Positivity: the 3–4–1 product `HH(σ)³HH(σ+iγ)⁴HH(σ+2iγ)` (`L(Π×Π̃)` for
`Π = Δ ⊞ Δ|·|^{iγ} ⊞ Δ|·|^{2iγ}`, up to the Fejér weights) has `log`-coefficients
`cR(n) n^{−σ} Re(3+4n^{−iγ}+n^{−2iγ}) ≥ 0`.
-/
import RamanujanTau.Sym2ZeroFree.Region

#print axioms RamanujanTau.Sym2ZeroFree.KK_eq_zeta_R1
#print axioms RamanujanTau.Sym2ZeroFree.HH_eq_zeta_Rt
#print axioms RamanujanTau.Sym2ZeroFree.norm_HH_le
#print axioms RamanujanTau.Sym2ZeroFree.norm_FS_antitone
#print axioms RamanujanTau.Sym2ZeroFree.one_le_norm_FS
#print axioms RamanujanTau.Sym2ZeroFree.PsiS_real
#print axioms RamanujanTau.Sym2ZeroFree.four_le_order_PsiS
#print axioms RamanujanTau.Sym2ZeroFree.norm_PsiS_le
#print axioms RamanujanTau.Sym2ZeroFree.re_logDeriv_PsiS_le
#print axioms RamanujanTau.Sym2ZeroFree.coreS
#print axioms RamanujanTau.Sym2ZeroFree.HH_zero_free_region
#print axioms RamanujanTau.Sym2ZeroFree.KK_ne_zero_near_edge
#print axioms RamanujanTau.Sym2ZeroFree.KK_zero_free_region_uniform
#print axioms RamanujanTau.Sym2ZeroFree.HH_ne_zero_region
#print axioms RamanujanTau.Sym2ZeroFree.Rcont_ne_zero_region
#print axioms RamanujanTau.Sym2ZeroFree.Lsym2_ne_zero_region
