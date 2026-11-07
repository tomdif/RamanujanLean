/-
# Positive proportion from `DeligneBound` and the strip bound `SvStripHyp`

`SKQFProof.skqfHyp_small_of_strip` reduces `SKQFHyp θ` (all small θ) to the single analytic bound
`SvStripHyp c'` on the twisted quadratic form 𝒮 in a strip below the real axis.
-/
import RamanujanTau.HafnerFinal.Main
import RamanujanTau.SKQFProof.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerFinal

open Complex RamanujanTau.HeckeL

theorem tauL_positive_proportion_deligne_strip [DeligneBound] {c' : ℝ} (hc' : 0 ≤ c')
    (H : SKQFProof.SvStripHyp c') :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card := by
  obtain ⟨θ₀, hθ₀, h⟩ := tauL_positive_proportion_deligne_SKQF
  obtain ⟨θ₁, hθ₁, hS⟩ := SKQFProof.skqfHyp_small_of_strip hc' H
  have hm : 0 < min θ₀ θ₁ := lt_min hθ₀ hθ₁
  exact h (min θ₀ θ₁) hm (min_le_left _ _) (hS _ hm (min_le_right _ _))

end RamanujanTau.HafnerFinal

#print axioms RamanujanTau.HafnerFinal.tauL_positive_proportion_deligne_strip
