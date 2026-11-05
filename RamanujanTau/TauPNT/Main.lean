/-
# The prime number theorem for Ramanujan's `τ`

Build: `nice -n 10 lake build RamanujanTau.TauPNT.Main`.  See `docs/TAU_PNT.md`.

Normalization: `λ(p) = τ(p) p^{−11/2}` (`EdgeNonvanishing.lam`), `L(s) = L(Δ, s + 11/2)`.

**Unconditional** (evidence level 1):
* `negLogDeriv_eq_LSeries`: `−L'/L(s) = ∑ Λ_Δ(n) n^{−s}` on `Re s > 1`,
  `Λ_Δ(p^k) = (α_p^k + β_p^k) log p` (via `exp (∑ cc(n) n^{−s}) = L(s)`, `exp_LSeries_cc`);
* `continuousOn_negLogDeriv`: `−L'/L` is continuous on `Re s ≥ 1` (edge non-vanishing);
* `primeSum_tendsto`: `∑_p τ(p) p^{−11/2} log p · p^{−σ}` has a finite limit as `σ → 1⁺`
  (smoothed PNT; in particular it is `O(1)`, so `o(1/(σ−1))`).

**Conditional on `[DeligneBound]`** (evidence level 2):
* `tendsto_sum_lam_sq`: `∑_p λ(p)² p^{−σ} → ∞` as `σ → 1⁺`;
* `tau_prime_sign_changes`: `τ(p) > 0` for infinitely many primes, `τ(p) < 0` for infinitely many.

**Conditional on `[DeligneBound]` and `WienerIkeharaHyp`** (evidence level 2):
* `tau_PNT`: `∑_{p<N} τ(p) p^{−11/2} log p = o(N)`;
* `tau_PNT_tau`: `∑_{p<N} τ(p) log p = o(N^{13/2})` (partial summation).
-/
import RamanujanTau.TauPNT.TauForm

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Filter Topology
open RamanujanTau.EdgeNonvanishing

/-- Headline (unconditional): the smoothed prime sum converges as `σ → 1⁺`. -/
theorem tau_PNT_smoothed : ∃ C : ℝ,
    Tendsto (fun σ : ℝ => ∑' p : Nat.Primes, lam p * Real.log p * (p : ℝ) ^ (-σ)) (𝓝[>] 1) (𝓝 C) :=
  ⟨_, primeSum_tendsto⟩

end RamanujanTau.TauPNT

#print axioms RamanujanTau.TauPNT.exp_LSeries_cc
#print axioms RamanujanTau.TauPNT.negLogDeriv_eq_LSeries
#print axioms RamanujanTau.TauPNT.continuousOn_negLogDeriv
#print axioms RamanujanTau.TauPNT.primeSum_tendsto
#print axioms RamanujanTau.TauPNT.tau_PNT_smoothed
#print axioms RamanujanTau.TauPNT.tendsto_sum_lam_sq
#print axioms RamanujanTau.TauPNT.tau_prime_sign_changes
#print axioms RamanujanTau.TauPNT.psiDelta_littleO
#print axioms RamanujanTau.TauPNT.tau_PNT
#print axioms RamanujanTau.TauPNT.tau_PNT_tau
