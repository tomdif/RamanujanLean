/-
# `GoodSecondTerm2/`: Good's second-term asymptotic for `L(Δ,s)`, unconditionally

Headlines (namespace `RamanujanTau.GoodSecondTerm2`):

* `good_second_term` — **unconditional**, for all `T ≥ 16`:
  `|∫₀ᵀ |L(Δ,6+it)|² dt − (2c₀ T log(T/2π) + (2γ_Δ − 2c₀) T)| ≤ C T^{599/600}`.
* `offDiagHyp_unconditional : OffDiagHyp (1/600)` — discharges the hypothesis of
  `GoodSecondTerm.good_second_term_of_offdiag`.
* `avgOff_eq` — the `u`-average of `Off(u)` over `[T, T+H]` is `Σ_p zz T H p`
  (per-pair weight `P̃` with one integration by parts in `u`).
* `norm_Ptil_le` — per-pair first-derivative test with the `1/H` gain.
* `scs_partial` — Abel summation of the SCS bound
  `SCSSharp2.shiftedConvolutionBound_sharp2 : ShiftedConvolutionBound (1/21) (1/21)` against the
  weight `rr t h x`.
* `off_avg_bound`, `avgOff_le` — `‖Σ_p zz T₁ H p‖ ≤ C T^{599/600}` with `H = T^{299/300}`,
  `M₀ = ⌊H⌋`, `h₂ = ⌊T^{1/150}⌋`, `ε = 1/600`, `T ≥ 2^{300}`.
-/
import RamanujanTau.GoodSecondTerm2.Final

#print axioms RamanujanTau.GoodSecondTerm2.good_second_term
#print axioms RamanujanTau.GoodSecondTerm2.offDiagHyp_unconditional
#print axioms RamanujanTau.GoodSecondTerm2.good_second_term_large
#print axioms RamanujanTau.GoodSecondTerm2.avgOff_eq
#print axioms RamanujanTau.GoodSecondTerm2.avgOff_le
#print axioms RamanujanTau.GoodSecondTerm2.off_avg_bound
#print axioms RamanujanTau.GoodSecondTerm2.norm_Ptil_le
#print axioms RamanujanTau.GoodSecondTerm2.scs_partial
