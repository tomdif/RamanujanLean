/-
# Hafner's positive proportion for `L(Δ,s)`: final assembly

`tauL_positive_proportion_deligne_SKQF`: under `[DeligneBound]` (Deligne's bound at primes) and
Selberg's arithmetic key-lemma hypothesis `SKQFHyp θ` for some small `θ > 0`, a positive proportion
of the nontrivial zeros of `L(Δ,s)` lie on the critical line `Re s = 6`.

Combines `QFProof5.qfHyp_deligne` (QFHyp under Deligne), `SelbergKey7.quadOffHyp`
(off-diagonal, unconditional) and `SelbergKeyDiag2.tauL_positive_proportion_of_SKQF'`
(diagonal evaluation, unconditional).
-/
import RamanujanTau.QFProof5.Main
import RamanujanTau.SelbergKey7.Main
import RamanujanTau.SelbergKeyDiag2.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerFinal

open Complex RamanujanTau.SelbergKey RamanujanTau.HeckeL

theorem tauL_positive_proportion_deligne_SKQF [DeligneBound] :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → SKQFHyp θ →
      ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
        (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
          c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card := by
  obtain ⟨θ₀, hθ₀, h⟩ := SelbergKeyDiag2.tauL_positive_proportion_of_SKQF'
  refine ⟨min θ₀ (1 / 81600), lt_min hθ₀ (by norm_num), fun θ hθ hθle hS => ?_⟩
  have h1 : θ ≤ θ₀ := hθle.trans (min_le_left _ _)
  have h2 : θ ≤ 1 / 81600 := hθle.trans (min_le_right _ _)
  exact h θ (1 / 300) 13 hθ h1 h2 (by norm_num) (by nlinarith)
    QFProof5.qfHyp_deligne hS SelbergKey7.quadOffHyp

end RamanujanTau.HafnerFinal

#print axioms RamanujanTau.HafnerFinal.tauL_positive_proportion_deligne_SKQF
