/-
# Quantitative sign changes of `τ(p)` over primes

Build: `nice -n 10 lake build RamanujanTau.TauSignsQuant.Main`.  See `docs/TAU_SIGNS_QUANT.md`.

Unconditional (no `DeligneBound`, no named hypotheses):
* `not_summable_signed_part`: `∑_{p : ελ(p)<0} |λ(p)| log p · p^{−σ} = ∞` for every `σ < 29/40`;
* `not_summable_tau_pos`, `not_summable_tau_neg`: `∑_{p : ±τ(p)>0} p^{−β} = ∞`, every `β < 9/20`;
* `tau_pos_count_frequently`, `tau_neg_count_frequently`: for every `θ < 9/20`,
  `#{p < x : ±τ(p) > 0} ≥ x^θ` for arbitrarily large `x`;
* `S1_small`: `∑_{p<N} λ(p) log p = o(N)`;
* `tau_pos_mass_of_bound_upto`, `tau_neg_mass_of_bound_upto`: if `|λ(p)| ≤ M` for all `p < N`
  (finitary hypothesis) and `N ≥ N₀(M)`, then `∑_{p<N, ±τ(p)>0} log p ≥ N/(3M²)`.
`[DeligneBound]`: `tau_pos_mass_deligne` etc.: `∑_{p<N, ±τ(p)>0} log p ≥ N/12`,
`#{p<N : ±τ(p)>0}·log N ≥ N/12` for `N ≥ N₀`.
-/
import RamanujanTau.TauSignsQuant.Proportion

#print axioms RamanujanTau.TauSignsQuant.not_summable_signed_part
#print axioms RamanujanTau.TauSignsQuant.not_summable_rpow_signed
#print axioms RamanujanTau.TauSignsQuant.not_summable_tau_pos
#print axioms RamanujanTau.TauSignsQuant.not_summable_tau_neg
#print axioms RamanujanTau.TauSignsQuant.count_frequently_of_not_summable
#print axioms RamanujanTau.TauSignsQuant.tau_pos_count_frequently
#print axioms RamanujanTau.TauSignsQuant.tau_neg_count_frequently
#print axioms RamanujanTau.TauSignsQuant.S1_small
#print axioms RamanujanTau.TauSignsQuant.signed_mass_of_bound_upto
#print axioms RamanujanTau.TauSignsQuant.tau_pos_mass_of_bound_upto
#print axioms RamanujanTau.TauSignsQuant.tau_neg_mass_of_bound_upto
#print axioms RamanujanTau.TauSignsQuant.tau_pos_mass_deligne
#print axioms RamanujanTau.TauSignsQuant.tau_neg_mass_deligne
#print axioms RamanujanTau.TauSignsQuant.tau_pos_count_deligne
#print axioms RamanujanTau.TauSignsQuant.tau_neg_count_deligne
