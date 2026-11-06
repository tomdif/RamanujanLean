/-
# Unfolding for an arbitrary subgroup `H ≤ SL₂(ℤ)` without a fundamental domain (reusable)

Instead of a fundamental domain `F_H = ⋃ γᵢU` we integrate over `U × ℍ` against every coset
representative: for the right cosets `x = Hγ` with chosen representatives `x.out`,

    Σ_x ∫_{U×ℍ} Σ_{h ∈ H} Ξ(h·x.out·p) dp = 2 ∫_{ℍ×ℍ} Ξ        (`lintegral_unfold_sub`)

because `H × (H\SL₂(ℤ)) ≃ SL₂(ℤ)`, `(h, x) ↦ h·x.out` (`cosetEquiv`).  For `H = Γ₀(q)` and an
`H`-invariant `Φ` this is exactly the unfolding identity on `Γ₀(q)\(ℍ×ℍ)`
(`lintegral_unfold_inv`).  No finiteness of the index is needed for these `ℝ≥0∞` statements.
-/
import RamanujanTau.SCSProof.Unfold2

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof
open scoped MatrixGroups ENNReal

variable (H : Subgroup SL(2, ℤ))

/-- Right cosets `H\SL₂(ℤ)`. -/
abbrev RCos := Quotient (QuotientGroup.rightRel H)

lemma mul_out_inv_mem (δ : SL(2, ℤ)) :
    δ * (Quotient.out (⟦δ⟧ : RCos H))⁻¹ ∈ H := by
  have h : QuotientGroup.rightRel H (Quotient.out (⟦δ⟧ : RCos H)) δ :=
    Quotient.exact (Quotient.out_eq _)
  exact QuotientGroup.rightRel_apply.1 h

lemma mk_mul_out (h : H) (x : RCos H) : (⟦(h : SL(2, ℤ)) * x.out⟧ : RCos H) = x := by
  conv_rhs => rw [← Quotient.out_eq x]
  apply Quotient.sound
  show QuotientGroup.rightRel H _ _
  rw [QuotientGroup.rightRel_apply]
  simpa [mul_inv_rev] using H.inv_mem h.2

/-- `H × (H\SL₂(ℤ)) ≃ SL₂(ℤ)`, `(h, x) ↦ h · x.out`. -/
noncomputable def cosetEquiv : H × RCos H ≃ SL(2, ℤ) where
  toFun y := (y.1 : SL(2, ℤ)) * y.2.out
  invFun δ := (⟨δ * (Quotient.out (⟦δ⟧ : RCos H))⁻¹, mul_out_inv_mem H δ⟩, ⟦δ⟧)
  left_inv y := by
    obtain ⟨h, x⟩ := y
    have e := mk_mul_out H h x
    ext
    · simp only
      rw [e]; group
    · exact e
  right_inv δ := by simp

/-- **Unfolding against all coset representatives.** -/
theorem lintegral_unfold_sub (Ξ : ℍ × ℍ → ℝ≥0∞) (hΞ : Measurable Ξ) :
    ∑' x : RCos H, ∫⁻ p, indU p * ∑' h : H, Ξ (dsmul ((h : SL(2, ℤ)) * x.out) p) =
      2 * ∫⁻ p, Ξ p := by
  rw [← lintegral_unfold2 Ξ hΞ]
  have hm : ∀ x : RCos H, Measurable fun p => indU p * ∑' h : H, Ξ (dsmul ((h : SL(2, ℤ)) * x.out) p) :=
    fun x => measurable_indU.mul (Measurable.ennreal_tsum fun h => hΞ.comp (measurable_dsmul _))
  rw [← lintegral_tsum fun x => (hm x).aemeasurable]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [← (cosetEquiv H).tsum_eq (fun γ => Ξ (dsmul γ p)), ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

/-- **Unfolding for an `H`-invariant factor**:
`Σ_x ∫_{U×ℍ} Φ(x.out p) · Σ_{h∈H} g(h x.out p) = 2 ∫ Φ g` whenever `Φ ∘ h = Φ` for `h ∈ H`. -/
theorem lintegral_unfold_inv (Φ g : ℍ × ℍ → ℝ≥0∞) (hΦ : Measurable Φ) (hg : Measurable g)
    (hinv : ∀ h : H, ∀ p, Φ (dsmul h p) = Φ p) :
    ∑' x : RCos H, ∫⁻ p, indU p * (Φ (dsmul x.out p) *
        ∑' h : H, g (dsmul ((h : SL(2, ℤ)) * x.out) p)) = 2 * ∫⁻ p, Φ p * g p := by
  rw [← lintegral_unfold_sub H (fun p => Φ p * g p) (hΦ.mul hg)]
  refine tsum_congr fun x => lintegral_congr fun p => ?_
  congr 1
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun h => ?_
  rw [dsmul_mul, hinv h]

end RamanujanTau.SCS2Coprime
