/-
# `SCSProof`: an unconditional shifted-convolution bound and t-aspect subconvexity for `L(Δ,s)`

* `shiftedConvolutionBound_of : ShiftedConvolutionBound (1/2^22) 8`:
  `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−2^{−22}} h⁸` for all `h ≥ 1`, `N`.
* `tauL_subconvex : ∃ δ > 0, ∃ C, ∀ t, ‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2−δ}`.

Route (docs/SCS_PROOF.md): the two-point invariant `Ψ(z,w) = (z − w̄)¹² Δ(z) conj Δ(w)` on
`Γ\(ℍ×ℍ)` gives the Laplace transform `G_h(W) = Σ τ(n)τ(n+h) e^{−nW}` at *complex* `W` as a
horocycle coefficient; Cauchy–Schwarz against an incomplete Poincaré series whose `L²` norm is
computed by the Bruhat decomposition (Kloosterman sums `S(h,h;c)`, Weil's bound) gives
`‖G_h(σ+iτ)‖ ≪ h (1+|τ|/σ)³² σ^{−12+3/40}` (`pointwise_G`); an exponential-Riesz Mellin inversion
(`laplace_riesz`), Rankin short sums (`rankin_short`, exponent `ρ = 2^{−22}` from
`RankinError`) and Abel summation give the sharp-sum bound.
-/
import RamanujanTau.SCSProof.Final2
import RamanujanTau.SubconvexityCond.Final

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open RamanujanTau.SubconvexityCond Complex

/-- **Unconditional shifted-convolution bound** `SCS(2^{−22}, 8)`. -/
instance shiftedConvolutionBound_of : ShiftedConvolutionBound (1 / 2 ^ 22) 8 := by
  obtain ⟨C, hC0, hC⟩ := shiftSum_bound
  exact ⟨⟨C, hC0, fun h N hh => by simpa [ρ] using hC h N hh⟩⟩

/-- **Unconditional t-aspect subconvexity** for `L(Δ, s)` on the critical line `Re s = 6`. -/
theorem tauL_subconvex : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - δ) := by
  obtain ⟨δ, hδ, C, -, hC⟩ := exists_subconvex_of_SCS shiftedConvolutionBound_of
    (by positivity) (by norm_num)
  exact ⟨δ, hδ, C, hC⟩

end RamanujanTau.SCSProof

#print axioms RamanujanTau.SCSProof.norm_kloosterman_hh_le
#print axioms RamanujanTau.SCSProof.Psi_smul
#print axioms RamanujanTau.SCSProof.coeff_Psi
#print axioms RamanujanTau.SCSProof.integral_unfold2
#print axioms RamanujanTau.SCSProof.norm_tsum_Iγ_le
#print axioms RamanujanTau.SCSProof.norm_Q_le
#print axioms RamanujanTau.SCSProof.Q_eq
#print axioms RamanujanTau.SCSProof.pointwise_G
#print axioms RamanujanTau.SCSProof.laplace_riesz
#print axioms RamanujanTau.SCSProof.Rmean_bound
#print axioms RamanujanTau.SCSProof.Asum_bound
#print axioms RamanujanTau.SCSProof.shiftSum_bound
#print axioms RamanujanTau.SCSProof.shiftedConvolutionBound_of
#print axioms RamanujanTau.SCSProof.tauL_subconvex
