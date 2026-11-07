import RamanujanTau.ThetaLift.Unfolding
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The fundamental domain of `Γ₀(N)`

The group `SL₂(ℤ)` does not act freely on `ℍ`, since `-1` acts trivially. So it acts through its image
in the permutations of `ℍ`, for which the translates of the standard domain are a.e. disjoint.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Modular Pointwise ENNReal

noncomputable section

/-- The action of `SL₂(ℤ)` on `ℍ` as a homomorphism to permutations. -/
def pG : SL(2, ℤ) →* Equiv.Perm ℍ := MulAction.toPermHom SL(2, ℤ) ℍ

lemma pG_apply (γ : SL(2, ℤ)) (z : ℍ) : pG γ z = γ • z := rfl

/-- The image of a subgroup of `SL₂(ℤ)`. -/
abbrev pSub (S : Subgroup SL(2, ℤ)) : Subgroup (Equiv.Perm ℍ) := S.map pG

lemma smul_pSub {S : Subgroup SL(2, ℤ)} (g : pSub S) (z : ℍ) : g • z = (g : Equiv.Perm ℍ) z := rfl

instance : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})

instance (S : Subgroup SL(2, ℤ)) : Countable (pSub S) := by
  refine Function.Surjective.countable (f := fun s : S => (⟨pG s, s, s.2, rfl⟩ : pSub S)) ?_
  rintro ⟨_, s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩

lemma measurable_smul_SL (γ : SL(2, ℤ)) : Measurable fun z : ℍ => γ • z := by
  have h : Continuous fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z :=
    continuous_const_smul _
  exact h.measurable

instance (S : Subgroup SL(2, ℤ)) : MeasurableConstSMul (pSub S) ℍ where
  measurable_const_smul g := by
    obtain ⟨_, s, hs, rfl⟩ := g
    exact measurable_smul_SL s

/-- Translation by an element of `SL₂(ℤ)` preserves the measure. -/
lemma volume_preimage_SL (γ : SL(2, ℤ)) (s : Set ℍ) (hs : MeasurableSet s) :
    volume ((fun z : ℍ => γ • z) ⁻¹' s) = volume s := by
  have h := measure_preimage_smul (μ := (volume : Measure ℍ)) (Matrix.SpecialLinearGroup.mapGL ℝ γ) s
  exact h

instance (S : Subgroup SL(2, ℤ)) : SMulInvariantMeasure (pSub S) ℍ volume where
  measure_preimage_smul g s hs := by
    obtain ⟨_, γ, hγ, rfl⟩ := g
    exact volume_preimage_SL γ s hs

lemma coe_preimage_null_iff {s : Set ℍ} (h : volume ((↑) '' s : Set ℂ) = 0) : volume s = 0 := by
  rw [volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

/-- A vertical line in `ℂ` is null. -/
lemma volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
    (s := {z : ℂ | z.re = c}) (by
      exact (isClosed_eq Complex.continuous_re continuous_const).measurableSet.nullMeasurableSet)
  rw [← h]
  have e : (Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | z.re = c}) = ({c} : Set ℝ) ×ˢ univ := by
    ext ⟨x, y⟩
    simp [Complex.measurableEquivRealProd]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The boundary of the standard domain is null. -/
lemma volume_fd_diff : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply coe_preimage_null_iff
  have hsub : ((↑) '' (𝒟 \ 𝒟ᵒ) : Set ℂ) ⊆ {z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)} ∪
      Metric.sphere (0 : ℂ) 1 := by
    rintro _ ⟨z, ⟨hz, hzo⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hz
    by_cases hn : 1 < Complex.normSq (z : ℂ)
    · have hre : |z.re| = 1 / 2 := by
        refine le_antisymm h2 (not_lt.mp fun h => hzo ⟨hn, h⟩)
      left
      rcases abs_cases z.re with ⟨h, -⟩ | ⟨h, -⟩
      · left
        change z.re = 1 / 2
        rw [← h, hre]
      · right
        change z.re = -(1 / 2)
        linarith
    · right
      have h1' : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hn) h1
      have hnorm : ‖(z : ℂ)‖ = 1 := by
        have h3 : ‖(z : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, h1']
        nlinarith [norm_nonneg (z : ℂ)]
      simpa using hnorm
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) ?_)
  · exact volume_re_eq _
  · exact volume_re_eq _
  · exact Measure.addHaar_sphere _ _ _

/-- The translates of the boundary, a null set. -/
def badSet : Set ℍ := ⋃ γ : SL(2, ℤ), (fun z : ℍ => γ • z) '' (𝒟 \ 𝒟ᵒ)

lemma smul_eq_preimage_inv (γ : SL(2, ℤ)) (s : Set ℍ) :
    (fun z : ℍ => γ • z) '' s = (fun z : ℍ => γ⁻¹ • z) ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨γ⁻¹ • z, h, by simp⟩

lemma measurableSet_fd : MeasurableSet 𝒟 := ModularGroup.isClosed_fd.measurableSet

lemma measurableSet_fdo : MeasurableSet 𝒟ᵒ := ModularGroup.isOpen_fdo.measurableSet

lemma volume_badSet : volume badSet = 0 := by
  refine measure_iUnion_null fun γ => ?_
  rw [smul_eq_preimage_inv, volume_preimage_SL γ⁻¹ _ (measurableSet_fd.diff measurableSet_fdo)]
  exact volume_fd_diff

variable (S : Subgroup SL(2, ℤ))

/-- The translates of the standard domain by coset representatives. -/
def domainOf : Set ℍ :=
  ⋃ q : Quotient (QuotientGroup.rightRel S), (fun z : ℍ => q.out • z) '' 𝒟

lemma measurableSet_domainOf : MeasurableSet (domainOf S) := by
  refine MeasurableSet.iUnion fun q => ?_
  rw [smul_eq_preimage_inv]
  exact measurable_smul_SL _ measurableSet_fd

lemma pG_neg (γ : SL(2, ℤ)) : pG (-γ) = pG γ := by
  ext z
  exact congrArg UpperHalfPlane.coe (ModularGroup.SL_neg_smul γ z)

/-- Membership in a translate of the domain. -/
lemma mem_smul_domainOf {g : pSub S} {z : ℍ} (hz : z ∈ g • domainOf S) :
    ∃ γ ∈ S, ∃ q : Quotient (QuotientGroup.rightRel S), ∃ w ∈ 𝒟,
      pG γ = (g : Equiv.Perm ℍ) ∧ z = (γ * q.out) • w := by
  obtain ⟨_, γ, hγ, rfl⟩ := g
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨q, w, hw, rfl⟩ := mem_iUnion.mp hx
  refine ⟨γ, hγ, q, w, hw, rfl, ?_⟩
  rw [mul_smul]
  rfl

/-- `domainOf S` is a fundamental domain, when `-1 ∈ S`. -/
theorem isFundamentalDomain_domainOf (hneg : (-1 : SL(2, ℤ)) ∈ S) :
    IsFundamentalDomain (pSub S) (domainOf S) volume where
  nullMeasurableSet := (measurableSet_domainOf S).nullMeasurableSet
  ae_covers := by
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd z
    set q : Quotient (QuotientGroup.rightRel S) := Quotient.mk _ δ⁻¹ with hq
    have hmem : q.out * δ ∈ S := by
      have h : QuotientGroup.rightRel S q.out δ⁻¹ := by
        apply Quotient.exact
        simp [hq]
      have h3 := S.inv_mem (QuotientGroup.rightRel_apply.mp h)
      simpa using h3
    refine ⟨⟨pG (q.out * δ), _, hmem, rfl⟩, ?_⟩
    refine mem_iUnion.mpr ⟨q, δ • z, hδ, ?_⟩
    change q.out • δ • z = pG (q.out * δ) z
    rw [pG_apply, mul_smul]
  aedisjoint := by
    intro g g' hne
    refine measure_mono_null (fun z hz => ?_) volume_badSet
    by_contra hbad
    obtain ⟨γ, hγ, q, w, hw, hg, hz1⟩ := mem_smul_domainOf S hz.1
    obtain ⟨γ', hγ', q', w', hw', hg', hz2⟩ := mem_smul_domainOf S hz.2
    have hwo : w ∈ 𝒟ᵒ := by
      by_contra hno
      exact hbad (mem_iUnion.mpr ⟨γ * q.out, w, ⟨hw, hno⟩, hz1.symm⟩)
    have hδ : ((γ' * q'.out)⁻¹ * (γ * q.out)) • w ∈ 𝒟 := by
      rw [mul_smul, ← hz1, hz2, inv_smul_smul]
      exact hw'
    have hgg : g = g' := by
      apply Subtype.ext
      rw [← hg, ← hg']
      have hkey : γ * q.out = γ' * q'.out ∨ γ * q.out = -(γ' * q'.out) := by
        rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo hδ with h | h
        · left
          exact (inv_mul_eq_one.mp h).symm
        · right
          calc γ * q.out = (γ' * q'.out) * ((γ' * q'.out)⁻¹ * (γ * q.out)) :=
                (mul_inv_cancel_left _ _).symm
            _ = -(γ' * q'.out) := by rw [h, mul_neg, mul_one]
      have hq' : q = q' := by
        have hrel : QuotientGroup.rightRel S q.out q'.out := by
          rw [QuotientGroup.rightRel_apply]
          have hs : q'.out * q.out⁻¹ ∈ S := by
            rcases hkey with h | h
            · have e : q'.out = (γ'⁻¹ * γ) * q.out := by
                rw [mul_assoc, h, inv_mul_cancel_left]
              rw [e, mul_inv_cancel_right]
              exact S.mul_mem (S.inv_mem hγ') hγ
            · have e : q'.out = -(γ'⁻¹ * γ) * q.out := by
                rw [neg_mul, mul_assoc, h, mul_neg, inv_mul_cancel_left, neg_neg]
              rw [e, mul_inv_cancel_right, ← neg_one_mul]
              exact S.mul_mem hneg (S.mul_mem (S.inv_mem hγ') hγ)
          exact hs
        have := Quotient.sound (s := QuotientGroup.rightRel S) hrel
        simpa using this
      subst hq'
      rcases hkey with h | h
      · rw [mul_right_cancel h]
      · have : γ = -γ' := by
          have h' : γ * q.out = (-γ') * q.out := by
            rw [h]
            simp
          exact mul_right_cancel h'
        rw [this, pG_neg]
    exact hne hgg

/-- The vertical strip. -/
def stripSet : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

lemma measurableSet_stripSet : MeasurableSet stripSet := by
  have hc : Continuous fun z : ℍ => z.re := UpperHalfPlane.continuous_re
  exact (measurableSet_le measurable_const hc.measurable).inter
    (measurableSet_lt hc.measurable measurable_const)

variable {S}

/-- The translation in `pSub S`. -/
def tEl (hT : ModularGroup.T ∈ S) : pSub S := ⟨pG ModularGroup.T, ModularGroup.T, hT, rfl⟩

/-- The translations in `pSub S`. -/
def tSub (hT : ModularGroup.T ∈ S) : Subgroup (pSub S) := Subgroup.zpowers (tEl hT)

lemma tEl_zpow_smul (hT : ModularGroup.T ∈ S) (n : ℤ) (z : ℍ) :
    ((((tEl hT) ^ n : pSub S) • z : ℍ) : ℂ) = z + n := by
  have h : ((tEl hT) ^ n : pSub S) = ⟨pG (ModularGroup.T ^ n), ModularGroup.T ^ n, S.zpow_mem hT n, rfl⟩ := by
    apply Subtype.ext
    simp [tEl, map_zpow]
  rw [h]
  change (((ModularGroup.T ^ n) • z : ℍ) : ℂ) = z + n
  rw [UpperHalfPlane.modular_T_zpow_smul]
  simp [add_comm]

/-- The strip is an exact domain for the translations. -/
theorem exactDomain_strip (hT : ModularGroup.T ∈ S) : ExactDomain (tSub hT) stripSet := by
  intro z
  have hre : ∀ (n : ℤ), (((tEl hT) ^ (-n) : pSub S) • z).re = z.re - n := by
    intro n
    have h := congrArg Complex.re (tEl_zpow_smul hT (-n) z)
    simpa [sub_eq_add_neg] using h
  have hmem : ∀ a : tSub hT, ∃ n : ℤ, (a : pSub S)⁻¹ = (tEl hT) ^ (-n) := by
    rintro ⟨_, n, rfl⟩
    exact ⟨n, by simp⟩
  refine ⟨⟨(tEl hT) ^ ⌊z.re⌋, ⌊z.re⌋, rfl⟩, ?_, ?_⟩
  · change ((((tEl hT) ^ ⌊z.re⌋ : pSub S))⁻¹ • z) ∈ stripSet
    rw [← zpow_neg]
    refine ⟨?_, ?_⟩
    · rw [hre]
      linarith [Int.floor_le z.re]
    · rw [hre]
      linarith [Int.lt_floor_add_one z.re]
  · rintro ⟨_, n, rfl⟩ hb
    have hb' : (((tEl hT) ^ n : pSub S)⁻¹ • z) ∈ stripSet := hb
    rw [← zpow_neg, ] at hb'
    obtain ⟨h0, h1⟩ := hb'
    rw [hre] at h0 h1
    have hn : n = ⌊z.re⌋ := by
      symm
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    apply Subtype.ext
    simp [hn]

end

end RamanujanTau.ThetaLift
