/-
# `HafnerBridge2/`: `DiagHyp θ ⇐ QFHyp`, hence Hafner's (MV2) `⇐ QFHyp`

* `Twisted.twisted_asymp` — items (a)+(b): uniformly for coprime `h, k`,
  `Σ_{r≤N} λ(hr)λ(kr)/r = r₀ρ(h)ρ(k) log N + γ_Δρ(h)ρ(k) + r₀(ρ₁(h)ρ(k) + ρ(h)ρ₁(k)) + O(Z (hk)⁴ N^{−1/5})`.
* `Smooth.abs_Dsum_sub_le`, `Wint`, `Pair`, `PairBound.pair_eval` — item (c): `MainTw(h,k) = 2√(hk)·W`,
  `W = (2r₀/[h,k])(q₀ I₁ + q₁ I₀) + O(Z (hk)⁵ X^{9/10})`.
* `Assemble.diag_of_QF` — `QFHyp → DiagHyp θ` for `0 < θ ≤ 1/260`.
* `Assemble.mv2_of_QF` — `QFHyp →` (MV2) for `0 < θ ≤ 1/81600`.
-/
import RamanujanTau.HafnerBridge2.Assemble

#print axioms RamanujanTau.HafnerBridge2.Dps_mul_P
#print axioms RamanujanTau.HafnerBridge2.peel_asymp
#print axioms RamanujanTau.HafnerBridge2.log_mul_ev_θgps
#print axioms RamanujanTau.HafnerBridge2.T_peel
#print axioms RamanujanTau.HafnerBridge2.twisted_asymp
#print axioms RamanujanTau.HafnerBridge2.abs_Dsum_sub_le
#print axioms RamanujanTau.HafnerBridge2.hasSum_Wint
#print axioms RamanujanTau.HafnerBridge2.MainTw_eq
#print axioms RamanujanTau.HafnerBridge2.pair_eval
#print axioms RamanujanTau.HafnerBridge2.diag_decomp
#print axioms RamanujanTau.HafnerBridge2.diag_of_QF
#print axioms RamanujanTau.HafnerBridge2.mv2_of_QF
