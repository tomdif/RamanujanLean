/-
# `SCSSharp`: `SCS(1/22, 1/2)` and `|L(Δ, 6+it)| ≪ (1+|t|)^{1/2 − 1/231}`

Headlines (all unconditional, axiom-clean):

* `shiftedConvolutionBound_sharp : ShiftedConvolutionBound (1/22) (1/2)`:
  `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/22} h^{1/2}` for all `h ≥ 1`, `N`
  (was `SCS(1/8000, 8)` in `SCSProof`).
* `tauL_subconvex_sharp`: `‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − 1/231}`
  (via the sharper reduction `tauL_subconvex_of_SCS'`, `δ = η/(5B+8)`; was `1/832000`).
* `tauL_subconvex_sharp_oldReduction`: `δ = 1/638` through the original reduction
  `SubconvexityCond.tauL_subconvex_of_SCS` (`δ = η/(10B+24)`), as a cross-check.

See `docs/SCS_SHARP.md` for the exponent bookkeeping.
-/
import RamanujanTau.SCSSharp.Final
import RamanujanTau.SCSSharp.Reduction

set_option autoImplicit false

namespace RamanujanTau.SCSSharp

open RamanujanTau.SubconvexityCond Complex

/-- **Unconditional shifted-convolution bound** `SCS(1/22, 1/2)`. -/
instance shiftedConvolutionBound_sharp : ShiftedConvolutionBound (1 / 22) (1 / 2) := by
  obtain ⟨C, hC0, hC⟩ := shiftSum_bound'
  refine ⟨⟨C, hC0, fun h N hh => ?_⟩⟩
  have := hC h N hh
  rwa [Real.sqrt_eq_rpow, show ηs = 1 / 22 from rfl] at this

/-- **Unconditional t-aspect subconvexity** with `δ = 1/231`:
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − 1/231}`. -/
theorem tauL_subconvex_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 231 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_of_SCS' (η := 1 / 22) (B := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta' (1 / 22) (1 / 2) = 1 / 231 := by unfold subconvexDelta'; norm_num
  have := hC t
  rwa [e] at this

/-- The same input through the original reduction (`δ = η/(10B+24) = 1/638`). -/
theorem tauL_subconvex_sharp_oldReduction : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 638 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_of_SCS (η := 1 / 22) (B := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta (1 / 22) (1 / 2) = 1 / 638 := by unfold subconvexDelta; norm_num
  have := hC t
  rwa [e] at this

end RamanujanTau.SCSSharp

#print axioms RamanujanTau.SCSSharp.lintegral_ball_le'
#print axioms RamanujanTau.SCSSharp.norm_Q_le'
#print axioms RamanujanTau.SCSSharp.norm_G0_le'
#print axioms RamanujanTau.SCSSharp.pointwise_G'
#print axioms RamanujanTau.SCSSharp.laplace_rieszK
#print axioms RamanujanTau.SCSSharp.Rmean2_bound
#print axioms RamanujanTau.SCSSharp.Asum_bound_large'
#print axioms RamanujanTau.SCSSharp.Asum_cs
#print axioms RamanujanTau.SCSSharp.shiftSum_bound'
#print axioms RamanujanTau.SCSSharp.shiftedConvolutionBound_sharp
#print axioms RamanujanTau.SCSSharp.tauL_subconvex_of_SCS'
#print axioms RamanujanTau.SCSSharp.tauL_subconvex_sharp
#print axioms RamanujanTau.SCSSharp.tauL_subconvex_sharp_oldReduction
