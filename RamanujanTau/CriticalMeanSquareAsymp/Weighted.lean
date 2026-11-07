/-
# (B) The weighted critical mean square, asymptotically

    κ¹² ∫_ℝ |Λ(Δ, 6+it)|² e^{2βt} dt / log(1/κ) → 12 ‖Δ‖²,     κ = cot β,  β → π/2⁻.

`‖Δ‖²` is `EisensteinReal.petNormSq` (Petersson norm over the standard fundamental domain).
-/
import RamanujanTau.CriticalMeanSquareAsymp.RayAsymp

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCountHafner
  RamanujanTau.CriticalMeanSquare RamanujanTau.CriticalMeanSquareLower
open scoped Real

lemma integral_Ru_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ u, Ru β u = (∫ u in Ioi 0, Ru β u) + ∫ u in Ioi 0, Ru (-β) u := by
  have hi := integrable_Ru hβ0 hβ
  have habs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have h1 : ∫ u in Iic 0, Ru β u = ∫ u in Ioi 0, Ru (-β) u := by
    have e : ∀ u, Ru β u = Ru (-β) (-u) := fun u => by
      rw [← Ru_even habs, neg_neg]
    simp_rw [e]
    rw [integral_comp_neg_Iic, neg_zero]
  rw [h1, add_comm]

lemma integrable_Ru_neg {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (Ru (-β)) := by
  have habs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have e : Ru (-β) = fun u => Ru β (-u) := funext fun u => (Ru_even habs u).symm
  rw [e]
  exact (integrable_Ru hβ0 hβ).comp_neg

/-- **(B) Weighted asymptotic.** As `β → π/2⁻`, with `κ = cot β`,
`κ¹² ∫ |Λ(6+it)|² e^{2βt} dt / log(1/κ) → 12‖Δ‖²`. -/
theorem weighted_asymptotic :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ 12 *
      (∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t)) /
        Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
      (𝓝 (12 * EisensteinReal.petNormSq)) := by
  have hp : Tendsto (fun β => (Real.cos β / Real.sin β) ^ 12 * (∫ u in Ioi 0, Ru β u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 c0) :=
    ray_tendsto (σ := -1) (Or.inr rfl) (R := Ru)
      (fun β hs u => Ru_eq_gen hs (ray_point_pos β · hs) u)
      (fun β hβ0 hβ => integrable_Ru hβ0.le hβ)
  have hn : Tendsto (fun β => (Real.cos β / Real.sin β) ^ 12 * (∫ u in Ioi 0, Ru (-β) u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 c0) :=
    ray_tendsto (σ := 1) (Or.inl rfl) (R := fun β => Ru (-β))
      (fun β hs u => Ru_eq_gen hs (ray_point_neg β · hs) u)
      (fun β hβ0 hβ => integrable_Ru_neg hβ0.le hβ)
  have hsum := ((hp.add hn).const_mul (2 * π))
  have hc : 2 * π * (c0 + c0) = 12 * EisensteinReal.petNormSq := by
    unfold c0; field_simp; ring
  rw [hc] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show 0 < π / 2 by positivity)] with β hβ
  have hP := weighted_parseval hβ.1.le hβ.2
  have hRu : ∫ u, Ru β u = ∫ u : ℝ, ‖cexp (6 * ((u : ℂ) + β * I)) *
      Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2 := rfl
  rw [hP, ← hRu, integral_Ru_split hβ.1.le hβ.2]
  ring

end RamanujanTau.CriticalMeanSquareAsymp
