/-
# Deligne-free results for the Rankin–Selberg L-function of `Δ` and the signs of `τ(p)`

Build: `nice -n 10 lake build RamanujanTau.TauPNTUncond.Main`.  See `docs/TAU_PNT_UNCOND.md`.

All unconditional (no `DeligneBound`, no named hypotheses):

* `HH_ne_zero_edge`: `ζ(2s)R(s) ≠ 0` at `s = 1+it`, `t ≠ 0` (continued; `R(s) = ∑ τ(n)²n^{−11−s}`);
* `Rcont_ne_zero_edge`: `R(1+it) ≠ 0`, i.e. `L(Δ×Δ, 1+it) ≠ 0`, `t ≠ 0`;
* `Lsym2_ne_zero_edge`, `Lsym2_tendsto_one`: `L(Sym²Δ, 1+it) ≠ 0` for all real `t`;
* `KK_ne_zero`: `(s−1)ζ(2s)R(s)` has no zero on `Re s ≥ 1`;
* `exp_LSeries_cR`: `log(ζ(2s)R(s)) = ∑ cR(n) n^{−s}`, `cR(p^k) = A_k(p)²/k ≥ 0`, on `Re s > 1`;
* `landau_abscissa`: Landau's theorem for logarithmic derivatives (general);
* `not_summable_lam_sq`: `∑_p λ(p)²/p = ∞`;
* `tau_prime_sign_changes_uncond`: `τ(p) > 0` and `τ(p) < 0` each for infinitely many primes;
* `rs_PNT`, `rs_prime_PNT`: `∑_{n<N} Λ_{Δ×Δ}(n) ~ N`, `∑_{p<N} λ(p)² log p ~ N`;
* `theta_PNT`, `sym2_prime_PNT`: `∑_{p<N} log p ~ N`, `∑_{p<N} λ(p²) log p = o(N)`.
-/
import RamanujanTau.TauPNTUncond.RSPNT

#print axioms RamanujanTau.TauPNTUncond.exp_LSeries_cR
#print axioms RamanujanTau.TauPNTUncond.one_le_norm_comb
#print axioms RamanujanTau.TauPNTUncond.HH_ne_zero_edge
#print axioms RamanujanTau.TauPNTUncond.Rcont_ne_zero_edge
#print axioms RamanujanTau.TauPNTUncond.Lsym2_ne_zero_edge
#print axioms RamanujanTau.TauPNTUncond.Lsym2_tendsto_one
#print axioms RamanujanTau.TauPNTUncond.KK_ne_zero
#print axioms RamanujanTau.TauPNTUncond.continuousOn_negLogDerivK
#print axioms RamanujanTau.TauPNTUncond.negLogDerivK_eq
#print axioms RamanujanTau.TauPNTUncond.landau_abscissa
#print axioms RamanujanTau.TauPNTUncond.weil_AA
#print axioms RamanujanTau.TauPNTUncond.not_summable_lam_sq
#print axioms RamanujanTau.TauPNTUncond.summable_vH_58
#print axioms RamanujanTau.TauPNTUncond.not_eventually_signed_uncond
#print axioms RamanujanTau.TauPNTUncond.tau_prime_sign_changes_uncond
#print axioms RamanujanTau.TauPNTUncond.rs_PNT
#print axioms RamanujanTau.TauPNTUncond.rs_prime_PNT
#print axioms RamanujanTau.TauPNTUncond.theta_PNT
#print axioms RamanujanTau.TauPNTUncond.sym2_prime_PNT
