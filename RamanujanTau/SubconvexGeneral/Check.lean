/-
# Consistency check at `f = Δ` and the eigenform corollaries

* `nlam_discriminant`: `λ_Δ(n) = τ(n) n^{−11/2}` (the general normalization specializes to
  `SubconvexityCond.lam`), hence `SCSf Δ η B ↔ ShiftedConvolutionBound η B`.
* `fL_discriminant_subconvex`: the **general** reduction `fL_subconvex_of_SCSf`, fed with the
  unconditional `SCSSharp2.shiftedConvolutionBound_sharp2 : SCS(1/21,1/21)`, gives
  `‖L(Δ,6+it)‖ ≪ (1+|t|)^{1/2−1/134}` — the same `δ = 1/134` as `SCSSharp2.tauL_subconvex_sharp2`,
  now through `fL Δ` and the weight-`k` pipeline at `k = 12`.  So the exponents are unchanged
  by the weight-parametrization.
* `fL_subconvex_eigen_of_SCSf`, `exists_subconvex_of_SCSf`: for every normalized Hecke eigenform.
-/
import RamanujanTau.SubconvexGeneral.Reduction
import RamanujanTau.EigenformEdge.RealPoint
import RamanujanTau.SCSSharp2.Main

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Real Finset Complex
open RamanujanTau.SubconvexityCond RamanujanTau.SCSSharp2 RamanujanTau.HeckeConvexGeneral
open RamanujanTau.EigenformEdge
open scoped MatrixGroups

variable {k : ℕ}

/-- `λ_Δ(n) = τ(n) n^{−11/2}`. -/
lemma nlam_discriminant (n : ℕ) : nlam (k := 12) DeltaF n = lam n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [nlam, lam, coef_zero, tau_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (coef (k := 12) DeltaF n).re = (tau n : ℝ) := by
    rw [coef_discriminant n]; simp [RamanujanTau.tauC]
  have hs : nrm 12 n = (n : ℝ) ^ ((11 / 2 : ℝ)) := by
    rw [nrm, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  rw [nlam, hc, hs, lam, Real.rpow_neg hn0.le, div_eq_mul_inv]

lemma shS_discriminant (h N : ℕ) : shS (nlam (k := 12) DeltaF) h N = shiftSum h N := by
  unfold shS shiftSum; simp_rw [nlam_discriminant]

/-- `SCS(η,B)` for `τ` is `SCS_Δ(η,B)`. -/
instance scsf_discriminant {η B : ℝ} [h : ShiftedConvolutionBound η B] :
    SCSf (k := 12) DeltaF η B := by
  obtain ⟨C, hC0, hC⟩ := h.bound
  exact ⟨⟨C, hC0, fun j N hj => by rw [shS_discriminant]; exact hC j N hj⟩⟩

/-- **Check**: the general pipeline at `k = 12` reproduces `δ = 1/134` for `L(Δ, 6+it)`. -/
theorem fL_discriminant_subconvex : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖fL (k := 12) DeltaF (((((12 : ℕ) : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤
      C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := fL_subconvex_of_SCSf (k := 12) DeltaF
    isNormalizedEigenform_discriminant.real (η := 1 / 21) (B := 1 / 21) (by norm_num)
    (by norm_num) (by norm_num) (u := 1 / 66) (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have e : subconvexDelta2 (1 / 21) (1 / 21) (1 / 66) = 1 / 134 := by
    unfold subconvexDelta2; norm_num
  have := hC t
  rwa [e] at this

/-- **Every normalized Hecke eigenform**: `SCS_f(η,B)` ⇒ subconvexity with `δ₂(η,B,u)`. -/
theorem fL_subconvex_eigen_of_SCSf {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f)
    {η B : ℝ} [SCSf f η B] (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta2 η B u) :=
  fL_subconvex_of_SCSf f hf.real hη0 hη1 hB hu0 hu1

/-- Any power saving in the weight-`k` shifted sums gives a power saving over convexity. -/
theorem exists_subconvex_of_SCSf (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0)
    {η B : ℝ} (h : SCSf f η B) (hη0 : 0 < η) (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - δ) := by
  have hm : 0 < min η (1 / 2) := lt_min hη0 (by norm_num)
  haveI : SCSf f (min η (1 / 2)) B := h.mono (min_le_left _ _) le_rfl
  refine ⟨subconvexDelta2 (min η (1 / 2)) B 1,
    (delta2_facts hm (min_le_right _ _) hB one_pos le_rfl).1, ?_⟩
  exact fL_subconvex_of_SCSf f hreal hm (min_le_right _ _) hB one_pos le_rfl

end RamanujanTau.SubconvexGeneral
