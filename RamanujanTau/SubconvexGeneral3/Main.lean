/-
# `SubconvexGeneral3/`: `SCS_f(1/21, 1/21)` and `δ = 1/134` for every real-coefficient
# level-one cusp form (every normalized Hecke eigenform)

Build: `nice -n 10 lake build RamanujanTau.SubconvexGeneral3.Main`. See `docs/SUBCONVEX_GENERAL.md` (§7).

Weight-`k` port of the `SCSSharp2` improvements on top of `SubconvexGeneral2`:
* `pointwise_GF21` (`GeoPoint21`): gcd-Kloosterman `norm_tsum_Iγ_le_gcd (1/400) (2/21)`,
  `‖G^f_h(σ+iv)‖ ≤ K h^{1/21} (|2v/σ|+3) σ^{−k+99/1000}`;
* `RmeanT_bound21`, `rankin_shortT21`, `AsumT_bound_large21` (`κ = 2/39`, `ι = 1/273`, `j = 13`);
* `scsf_of_pointwise21` (`TauFinal21`): Abel summation with `B = η`.
-/
import RamanujanTau.SubconvexGeneral3.GeoPoint21
import RamanujanTau.SubconvexGeneral3.TauFinal21
import RamanujanTau.SubconvexGeneral2.OddWeight
import RamanujanTau.SubconvexGeneral.Check

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral3

open Complex
open RamanujanTau.SubconvexGeneral RamanujanTau.SubconvexGeneral2 RamanujanTau.HeckeConvexGeneral
open RamanujanTau.EigenformEdge RamanujanTau.SCSSharp2
open scoped MatrixGroups

variable {k : ℕ}

/-- **Unconditional weight-`k` shifted-convolution bound** `SCS_f(1/21, 1/21)`. -/
theorem scsf_general21 (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    SCSf f (1 / 21) (1 / 21) := by
  rcases lt_or_ge k 12 with hk | hk
  · exact scsf_of_eq_zero (eq_zero_of_lt_twelve f hk) _ _
  rcases Nat.even_or_odd k with hev | hodd
  · exact scsf_of_pointwise21 f hk hreal (pointwise_GF21 f hk hev)
  · exact scsf_of_eq_zero (eq_zero_of_odd f hodd) _ _

/-- **Unconditional t-aspect subconvexity, `δ = 1/134`**, every level-one cusp form with real
coefficients: `‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − 1/134}`. -/
theorem fL_subconvex_general134 (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) := by
  haveI := scsf_general21 f hreal
  obtain ⟨C, hC0, hC⟩ := fL_subconvex_of_SCSf f hreal (η := 1 / 21) (B := 1 / 21)
    (by norm_num) (by norm_num) (by norm_num) (u := 1 / 66) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta2 (1 / 21) (1 / 21) (1 / 66) = 1 / 134 := by
    unfold subconvexDelta2; norm_num
  have := hC t
  rwa [e] at this

/-- **Every normalized Hecke eigenform of level one**: `‖L(f, k/2+it)‖ ≪ (1+|t|)^{1/2−1/134}`. -/
theorem fL_subconvex_eigenform134 {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) :=
  fL_subconvex_general134 f hf.real

end RamanujanTau.SubconvexGeneral3

#print axioms RamanujanTau.SubconvexGeneral3.pointwise_GF21
#print axioms RamanujanTau.SubconvexGeneral3.RmeanT_bound21
#print axioms RamanujanTau.SubconvexGeneral3.rankin_shortT21
#print axioms RamanujanTau.SubconvexGeneral3.AsumT_bound_large21
#print axioms RamanujanTau.SubconvexGeneral3.shS_bound21
#print axioms RamanujanTau.SubconvexGeneral3.scsf_of_pointwise21
#print axioms RamanujanTau.SubconvexGeneral3.scsf_general21
#print axioms RamanujanTau.SubconvexGeneral3.fL_subconvex_general134
#print axioms RamanujanTau.SubconvexGeneral3.fL_subconvex_eigenform134
