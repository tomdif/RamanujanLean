/-
# `HafnerMV2/`: Hafner's (MV2) from the twisted second moment

Headlines (namespace `RamanujanTau.HafnerMV2`):

* `mv2_of_diag` — for `0 < θ`, `136θ ≤ 1/600`, **conditional on `DiagHyp θ`**:
  `∫_T^{3T} |L(Δ,6+iu) M(6+iu)²|² du ≤ B T` for Selberg's mollifier `M = Mc (bSel ⌊T^θ⌋) ⌊T^θ⌋`.
* `DiagHyp θ` — the smoothed diagonal `Σ_{p,q} κ(p,q) MainTw(h_p, h_q, X, X^{299/300}) = O(T)`,
  `X ∈ [T/2, 3T]` (no `L`-values; `MainTw` is `TwistedMoment.MainTw`).
* `normSq_Mc_sq`, `Av_LM2` — `|M²|²` expanded into symmetrised twists; the average of `|LM²|²` is
  `Σ κ · TwAv`.
* `sharp_le` — the sharp `∫_T^{3T}` is bounded by a difference of two `u`-averages (`|·|² ≥ 0`).
* `avg_err` — summing `TwistedMoment.twisted_moment` over the `y⁴` index pairs: error `≤ (C/2) y^{136} X^{599/600}`.
-/
import RamanujanTau.HafnerMV2.MV2

#print axioms RamanujanTau.HafnerMV2.mv2_of_diag
#print axioms RamanujanTau.HafnerMV2.normSq_Mc_sq
#print axioms RamanujanTau.HafnerMV2.Av_LM2
#print axioms RamanujanTau.HafnerMV2.sharp_le
#print axioms RamanujanTau.HafnerMV2.avg_err
