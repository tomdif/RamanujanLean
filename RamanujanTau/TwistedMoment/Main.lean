/-
# `TwistedMoment/`: the symmetrised twisted second moment of `L(Δ, s)`

Headlines (namespace `RamanujanTau.TwistedMoment`):

* `twisted_moment` — **unconditional**: for `h, k ≥ 1`, `X ≥ 2^{300}`, `H = X^{299/300}`,
  `‖TwAv h k X H − MainTw h k X H‖ ≤ C (hk)^{33} X^{599/600}`, where
  `TwAv = (1/H)∫_X^{X+H}∫_{16}^u |L(Δ,6+it)|² ((h/k)^{it} + (k/h)^{it}) dt du` and
  `MainTw = 2√(hk) Σ_m ι_k(m+1)ι_h(m+1)(m+1)^{−1} P̃(2log(m+1) − log hk, 0, X, H)` (smoothed diagonal).
* `gavgOff_le` — the off-diagonal bound of `GoodSecondTerm2` for an arbitrary `GoodSeq`
  (normalised Rankin + SCS input, `V`-shift `c`), uniform: `≤ C e^{8c} X^{599/600}`.
* `prefix_eq`, `iota_scs` — prefix sums of `ι_a(x)ι_b(x+ℓ)` are `HeckeAFE.shiftSum2 b a ℓ N_t`,
  bounded by `SCS2Coprime.scs2_general`.
* `goodSeq_gS` — `r(ι_k ± ι_h)` is a `GoodSeq` with `c = log hk`.
* `twist_reindex`, `polarise`, `twist_pointwise` — the AFE twisted by `(h/k)^{it}` and polarised.
* `gavg_eq` — the `u`-averaged identity for a `GoodSeq` (diagonal included).
-/
import RamanujanTau.TwistedMoment.TwMain

#print axioms RamanujanTau.TwistedMoment.twisted_moment
#print axioms RamanujanTau.TwistedMoment.gavgOff_le
#print axioms RamanujanTau.TwistedMoment.off_avg_bound
#print axioms RamanujanTau.TwistedMoment.prefix_eq
#print axioms RamanujanTau.TwistedMoment.iota_scs
#print axioms RamanujanTau.TwistedMoment.goodSeq_gS
#print axioms RamanujanTau.TwistedMoment.twist_reindex
#print axioms RamanujanTau.TwistedMoment.twist_pointwise
#print axioms RamanujanTau.TwistedMoment.gavg_eq
