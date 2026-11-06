/-
# `Γ₀(q)`: membership, and the restricted Bruhat bound as a sum over the subgroup

* `mem_Gamma0_iff`: `γ ∈ Γ₀(q) ↔ q ∣ γ₁₀`;
* `tsum_Gamma0_Iγ`: `Σ_{h ∈ Γ₀(q)} I(h) = Σ_γ [q ∣ γ₁₀] I(γ)`;
* **`norm_tsum_Gamma0_Iγ_le`**: `‖Σ_{h ∈ Γ₀(q)} I(h)‖ ≤ C h^β ε³ Y^{−3/2−2δ}`, `C` independent of `q`
  (the `‖P_q‖²` input of the two-point method on `Γ₀(q)\(ℍ×ℍ)`).
-/
import RamanujanTau.SCS2Coprime.Bruhat0
import RamanujanTau.SCS2Coprime.Unfold

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open CongruenceSubgroup RamanujanTau.SCSProof
open scoped MatrixGroups

lemma mem_Gamma0_iff (q : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma0 q ↔ (q : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma tsum_Gamma0_Iγ (P : Par) (q : ℕ) :
    ∑' h : Gamma0 q, Iγ P h = ∑' γ, IγQ P q γ := by
  refine (tsum_subtype ((Gamma0 q : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) (Iγ P)).trans ?_
  refine tsum_congr fun γ => ?_
  unfold IγQ
  by_cases hγ : (q : ℤ) ∣ γ 1 0
  · rw [Set.indicator_of_mem (show γ ∈ ((Gamma0 q : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) from
      (mem_Gamma0_iff q γ).2 hγ), if_pos hγ]
  · rw [Set.indicator_of_notMem (show γ ∉ ((Gamma0 q : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) from
      fun h => hγ ((mem_Gamma0_iff q γ).1 h)), if_neg hγ]

/-- **Bruhat + gcd-Weil on `Γ₀(q)`, uniformly in `q`.** -/
theorem norm_tsum_Gamma0_Iγ_le (δ β : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Par) (q : ℕ), 1 ≤ P.h →
      ‖∑' h : Gamma0 q, Iγ P h‖ ≤ C * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
  obtain ⟨C, hC0, hC⟩ := norm_tsum_IγQ_le_gcd δ β hδ hδ2 hβ
  exact ⟨C, hC0, fun P q hh => by rw [tsum_Gamma0_Iγ]; exact hC P q hh⟩

end RamanujanTau.SCS2Coprime
