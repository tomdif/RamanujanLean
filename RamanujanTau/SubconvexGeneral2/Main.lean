/-
# `SubconvexGeneral2/`: unconditional t-aspect subconvexity for every real-coefficient
# level-one cusp form (in particular every normalized Hecke eigenform)

Build: `nice -n 10 lake build RamanujanTau.SubconvexGeneral2.Main`. See `docs/SUBCONVEX_GENERAL.md` (§6).

* `pointwise_GF` (`Geo*`): weight-`k` two-point pointwise bound
  `|G^f_h(σ+iv)| ≪ √h (|2v/σ|+3) σ^{−k+12/125}` (even `k ≥ 12`).
* `scsf_of_pointwise` (`Tau*`): Tauberian + unsmoothing + Abel ⇒ `SCS_f(1/22, 1/2)`.
* `scsf_general`: `SCS_f(1/22, 1/2)` for every `f` with real coefficients (odd `k`, `k < 12`: `f = 0`).
* `fL_subconvex_general`: `‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − 1/180}`.
* `fL_subconvex_eigenform`: the same for every normalized Hecke eigenform.
-/
import RamanujanTau.SubconvexGeneral2.GeoPoint
import RamanujanTau.SubconvexGeneral2.TauFinal
import RamanujanTau.SubconvexGeneral2.OddWeight
import RamanujanTau.SubconvexGeneral.Check

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open Complex
open RamanujanTau.SubconvexGeneral RamanujanTau.HeckeConvexGeneral RamanujanTau.EigenformEdge
open RamanujanTau.SCSSharp2
open scoped MatrixGroups

variable {k : ℕ}

/-- **Unconditional weight-`k` shifted-convolution bound** `SCS_f(1/22, 1/2)`. -/
theorem scsf_general (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    SCSf f (1 / 22) (1 / 2) := by
  rcases lt_or_ge k 12 with hk | hk
  · exact scsf_of_eq_zero (eq_zero_of_lt_twelve f hk) _ _
  rcases Nat.even_or_odd k with hev | hodd
  · exact scsf_of_pointwise f hk hreal (pointwise_GF f hk hev)
  · exact scsf_of_eq_zero (eq_zero_of_odd f hodd) _ _

/-- **Unconditional t-aspect subconvexity, every level-one cusp form with real coefficients**:
`‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − 1/180}`. -/
theorem fL_subconvex_general (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 180 : ℝ) := by
  haveI := scsf_general f hreal
  obtain ⟨C, hC0, hC⟩ := fL_subconvex_of_SCSf f hreal (η := 1 / 22) (B := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (u := 1 / 89) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta2 (1 / 22) (1 / 2) (1 / 89) = 1 / 180 := by
    unfold subconvexDelta2; norm_num
  have := hC t
  rwa [e] at this

/-- **Every normalized Hecke eigenform of level one**: `‖L(f, k/2+it)‖ ≪ (1+|t|)^{1/2−1/180}`. -/
theorem fL_subconvex_eigenform {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 180 : ℝ) :=
  fL_subconvex_general f hf.real

end RamanujanTau.SubconvexGeneral2

#print axioms RamanujanTau.SubconvexGeneral2.pointwise_GF
#print axioms RamanujanTau.SubconvexGeneral2.scsf_of_pointwise
#print axioms RamanujanTau.SubconvexGeneral2.eq_zero_of_odd
#print axioms RamanujanTau.SubconvexGeneral2.scsf_general
#print axioms RamanujanTau.SubconvexGeneral2.fL_subconvex_general
#print axioms RamanujanTau.SubconvexGeneral2.fL_subconvex_eigenform
