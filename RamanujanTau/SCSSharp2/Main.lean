/-
# `SCSSharp2`: `SCS(1/21, 1/21)` and `|L(Δ, 6+it)| ≪ (1+|t|)^{1/2 − 1/134}`

Headlines (all unconditional, axiom-clean):

* `shiftedConvolutionBound_sharp2 : ShiftedConvolutionBound (1/21) (1/21)`:
  `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/21} h^{1/21}` for all `h ≥ 1`, `N`
  (was `SCS(1/22, 1/2)` in `SCSSharp`): gcd-form Weil bound + divisor bound in the `‖P‖²` step,
  the `t < h` range of the Abel summation split as `(t+h)^{η}(N+h)^{1/2−η}`, and the Weil
  exponent `δ_W = 1/400` (was `1/100`) with re-tuned Tauberian parameters `(κ, ι, j) = (2/39, 1/273, 13)`.
* `tauL_subconvex_of_SCS2`: `SCS(η,B)` ⇒ `δ = η/((1+u)(4B+6+2η))` for every `0 < u ≤ 1`.
* `tauL_subconvex_sharp2`: `‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − 1/134}` (`u = 1/66`; was `1/231`).
* `tauL_subconvex_sharp2_family`: `δ = (1/132)/(1+u)` for every `0 < u ≤ 1`.
* intermediate stage: `shiftedConvolutionBound_22 : SCS(1/22, 1/22)`, `tauL_subconvex_140` (`δ = 1/140`),
  and `tauL_subconvex_22_oldReduction` (`δ = 1/181` through `SCSSharp`'s `η/(5B+8)`).

See `docs/SCS_SHARP2.md`.
-/
import RamanujanTau.SCSSharp2.Final
import RamanujanTau.SCSSharp2.Final21
import RamanujanTau.SCSSharp2.Reduction

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open RamanujanTau.SubconvexityCond Complex

/-- Intermediate stage: `SCS(1/22, 1/22)`. -/
instance shiftedConvolutionBound_22 : ShiftedConvolutionBound (1 / 22) (1 / 22) := by
  obtain ⟨C, hC0, hC⟩ := shiftSum_boundG
  refine ⟨⟨C, hC0, fun h N hh => ?_⟩⟩
  have := hC h N hh
  rwa [show RamanujanTau.SCSSharp.ηs = 1 / 22 from rfl] at this

/-- Intermediate stage: `δ = (1/138)/(1+u)`, `0 < u ≤ 1`, from `SCS(1/22, 1/22)`. -/
theorem tauL_subconvex_22_family {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / (138 * (1 + u))) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_of_SCS2 (η := 1 / 22) (B := 1 / 22) (by norm_num)
    (by norm_num) (by norm_num) hu0 hu1
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta2 (1 / 22) (1 / 22) u = 1 / (138 * (1 + u)) := by
    unfold subconvexDelta2
    have : (0 : ℝ) < 1 + u := by linarith
    field_simp; ring
  have := hC t
  rwa [e] at this

/-- Intermediate stage: `‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − 1/140}`. -/
theorem tauL_subconvex_140 : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 140 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_22_family (u := 1 / 69) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have := hC t
  rwa [show (1 : ℝ) / (138 * (1 + 1 / 69)) = 1 / 140 by norm_num] at this

/-- Cross-check: `SCS(1/22,1/22)` through `SCSSharp`'s reduction `η/(5B+8)` gives `δ = 1/181`. -/
theorem tauL_subconvex_22_oldReduction : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 181 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.SCSSharp.tauL_subconvex_of_SCS' (η := 1 / 22) (B := 1 / 22)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : RamanujanTau.SCSSharp.subconvexDelta' (1 / 22) (1 / 22) = 1 / 181 := by
    unfold RamanujanTau.SCSSharp.subconvexDelta'; norm_num
  have := hC t
  rwa [e] at this

/-- **Unconditional shifted-convolution bound** `SCS(1/21, 1/21)`:
`|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/21} h^{1/21}`. -/
instance shiftedConvolutionBound_sharp2 : ShiftedConvolutionBound (1 / 21) (1 / 21) := by
  obtain ⟨C, hC0, hC⟩ := shiftSum_bound21
  refine ⟨⟨C, hC0, fun h N hh => ?_⟩⟩
  have := hC h N hh
  rwa [show ηt = 1 / 21 from rfl] at this

/-- **t-aspect subconvexity, one-parameter family**: `δ = (1/132)/(1+u)`, `0 < u ≤ 1`. -/
theorem tauL_subconvex_sharp2_family {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / (132 * (1 + u))) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_of_SCS2 (η := 1 / 21) (B := 1 / 21) (by norm_num)
    (by norm_num) (by norm_num) hu0 hu1
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta2 (1 / 21) (1 / 21) u = 1 / (132 * (1 + u)) := by
    unfold subconvexDelta2
    have : (0 : ℝ) < 1 + u := by linarith
    field_simp; ring
  have := hC t
  rwa [e] at this

/-- **Unconditional t-aspect subconvexity** with `δ = 1/134`:
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − 1/134}` (`SCS(1/21,1/21)`, `u = 1/66`). -/
theorem tauL_subconvex_sharp2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖RamanujanTau.HeckeL.tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := tauL_subconvex_sharp2_family (u := 1 / 66) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have := hC t
  rwa [show (1 : ℝ) / (132 * (1 + 1 / 66)) = 1 / 134 by norm_num] at this

end RamanujanTau.SCSSharp2

#print axioms RamanujanTau.SCSSharp2.card_divisors_le_rpow
#print axioms RamanujanTau.SCSSharp2.norm_kloosterman_hh_gcd_le
#print axioms RamanujanTau.SCSSharp2.sum_gcd_le
#print axioms RamanujanTau.SCSSharp2.norm_tsum_Iγ_le_gcd
#print axioms RamanujanTau.SCSSharp2.pointwise_G2
#print axioms RamanujanTau.SCSSharp2.Rmean2_boundG
#print axioms RamanujanTau.SCSSharp2.Asum_bound_largeG
#print axioms RamanujanTau.SCSSharp2.shiftSum_boundG
#print axioms RamanujanTau.SCSSharp2.shiftedConvolutionBound_22
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_of_SCS2
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_22_family
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_140
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_22_oldReduction
#print axioms RamanujanTau.SCSSharp2.pointwise_G21
#print axioms RamanujanTau.SCSSharp2.Rmean2_bound21
#print axioms RamanujanTau.SCSSharp2.Asum_bound_large21
#print axioms RamanujanTau.SCSSharp2.shiftSum_bound21
#print axioms RamanujanTau.SCSSharp2.shiftedConvolutionBound_sharp2
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_sharp2_family
#print axioms RamanujanTau.SCSSharp2.tauL_subconvex_sharp2
