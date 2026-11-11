import RamanujanTau.MultiQuintupleFourShortCoherence
import RamanujanTau.MultiQuintupleFourSpanningIsometry

/-! Assemble the actual four-factor shell partners into one rational orthogonal
involution, conditional only on the remaining spanning obligation. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators

structure FourOrthogonalInvolution where
  linear : FourRatPoint →ₗ[ℚ] FourRatPoint
  dot_preserving : ∀ x y, fourDot (linear x) (linear y)=fourDot x y
  involutive : ∀ x, linear (linear x)=x

def fourIntToRat (x : Fin 4 → ℤ) : FourRatPoint := fun i => x i

theorem fourDot_intToRat (x y : Fin 4 → ℤ) :
    fourDot (fourIntToRat x) (fourIntToRat y)=((fourDot x y : ℤ) : ℚ) := by
  simp [fourDot,fourIntToRat]

/-- A chosen short partner family has a single orthogonal involution extending
it. Preservation of dot products and involutivity follow from arithmetic. -/
theorem four_short_pairing_yields_involution {ι : Type*} {p : ℕ} [Fact p.Prime]
    {v : Fin 4 → ℤ} (x : ι → FourProjectiveLift p v) (hpodd : Odd (p : ℤ))
    (H : ℤ) (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p)
    (hshort : ∀ i, 2*fourVectorNorm (x i).point<(p : ℤ)^2)
    (hspan : Submodule.span ℚ (Set.range (fun i => fourIntToRat (x i).point))=⊤)
    (f : ι → ι)
    (hpartner : ∀ i, fourVectorNorm (x (f i)).point=fourVectorNorm (x i).point ∧
      (x (f i)).point ≠ (x i).point ∧ (x (f i)).phase c=(x i).phase c) :
    ∃ T : FourOrthogonalInvolution,
      ∀ i, T.linear (fourIntToRat (x i).point)=fourIntToRat (x (f i)).point := by
  let a := fun i => fourIntToRat (x i).point
  obtain ⟨T,hT,hdot⟩ := four_exists_linear_of_spanning_gram_family a (fun i => a (f i))
    hspan (by
      intro i j
      simp only [a,fourDot_intToRat]
      exact_mod_cast (x i).short_partners_preserve_dot (x j) (x (f i)) (x (f j))
        hpodd H hv c (hpartner i).1 (hpartner j).1 (hshort i) (hshort j)
        (hpartner i).2.1 (hpartner j).2.1 (hpartner i).2.2 (hpartner j).2.2)
  have hfi : ∀ i, (x (f (f i))).point=(x i).point := by
    intro i
    exact (x (f i)).short_partner_unique (x (f (f i))) (x i) hpodd H hv c
      (hpartner (f i)).1 (hpartner i).1.symm (hshort (f i))
      (hpartner (f i)).2.1 (hpartner i).2.1.symm
      (hpartner (f i)).2.2 (hpartner i).2.2.symm
  have hinvol : ∀ z, T (T z)=z := by
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range a) := by rw [hspan]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hT,hT]
        exact congrArg fourIntToRat (hfi i)
    | zero => simp
    | add u v hu hv iu iv => simp only [map_add,iu,iv]
    | smul r u hu iu => simp only [map_smul,iu]
  exact ⟨⟨T,hdot,hinvol⟩,hT⟩

/-- Supported, positive, strictly short Fourier indices. -/
def FourShortIndex (p : ℕ) (v : Fin 4 → ℤ) :=
  {x : ZMod p × (Fin 4 → ℤ) // fourCubicCharacter x.2 ≠ 0 ∧
    0<fourDualNorm p v x ∧ 2*fourDualNorm p v x<(p : ℤ)^2}

/-- Actual coefficient vanishing produces a rational orthogonal involution
reversing the cubic character on every supported short vector, once those
vectors are known to span. No partner coherence is assumed. -/
theorem four_persistent_vanishing_spanning_involution {p R : ℕ} [Fact p.Prime]
    {v : Fin 4 → ℕ} (hp2 : p ≠ 2) (h3 : (3 : ZMod p) ≠ 0)
    (hc : fourCanonical p v) (hR : R<p) (hz : PersistentFourVanishing p v R)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (hvi : (v 0 : ZMod p) ≠ 0)
    (hspan : Submodule.span ℚ (Set.range (fun x : FourShortIndex p (fun i => (v i : ℤ)) =>
      fourIntToRat (fourDualPoint p (fun i => (v i : ℤ)) x.val)))=⊤) :
    ∃ T : FourOrthogonalInvolution,
      ∀ x : FourShortIndex p (fun i => (v i : ℤ)),
      ∃ y : FourShortIndex p (fun i => (v i : ℤ)),
        T.linear (fourIntToRat (fourDualPoint p (fun i => (v i : ℤ)) x.val))=
          fourIntToRat (fourDualPoint p (fun i => (v i : ℤ)) y.val) ∧
        fourCanonicalPhase p (fun i => (v i : ℤ)) R y.val=
          fourCanonicalPhase p (fun i => (v i : ℤ)) R x.val+p ∧
        fourCubicCharacter y.val.2= -fourCubicCharacter x.val.2 := by
  classical
  let vi : Fin 4 → ℤ := fun i => v i
  let I := FourShortIndex p vi
  have hp : p.Prime := Fact.out
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hp.odd_of_ne_two hp2
  have hpartners : ∀ x : I, ∃ y : I,
      fourDualNorm p vi y.val=fourDualNorm p vi x.val ∧
      fourCanonicalPhase p vi R y.val=fourCanonicalPhase p vi R x.val+p ∧
      fourCubicCharacter y.val.2= -fourCubicCharacter x.val.2 := by
    intro x
    obtain ⟨y,hy,hn,hph,hch⟩ := four_persistent_vanishing_character_partner
      hp2 h3 hc hR hz H hv hvi x.val x.property.1 x.property.2.1 x.property.2.2
    exact ⟨⟨y,hy,by rw [hn]; exact x.property.2.1,
      by rw [hn]; exact x.property.2.2⟩,hn,hph,hch⟩
  choose f hf using hpartners
  let lifts : I → FourProjectiveLift p vi := fun x => fourFourierLift p vi x.val
  have hv' : fourVectorNorm vi=(p : ℤ)*H := by
    convert hv using 1
    simp [fourVectorNorm,fourDot,vi,Fin.sum_univ_succ]
    ring
  have hshort : ∀ x : I, 2*fourVectorNorm (lifts x).point<(p : ℤ)^2 := by
    intro x
    simpa only [lifts,fourFourierLift_norm] using x.property.2.2
  have hpartner : ∀ x : I,
      fourVectorNorm (lifts (f x)).point=fourVectorNorm (lifts x).point ∧
      (lifts (f x)).point ≠ (lifts x).point ∧
      (lifts (f x)).phase (((2*R-(∑ i, vi i) : ℤ) : ZMod p)/3)=
        (lifts x).phase (((2*R-(∑ i, vi i) : ℤ) : ZMod p)/3) := by
    intro x
    refine ⟨by simpa only [lifts,fourFourierLift_norm] using (hf x).1,?_,?_⟩
    · intro he
      have heq := fourDualPoint_injective vi h3 (by simpa only [vi,Int.cast_natCast] using hvi) he
      have hph := (hf x).2.1
      rw [heq] at hph
      have hzmod : (p : ZMod (2*p))=0 := by linear_combination -hph
      have hd := (ZMod.natCast_eq_zero_iff p (2*p)).mp hzmod
      exact Nat.not_dvd_of_pos_of_lt hp.pos (by have := hp.pos; omega) hd
    · change (fourFourierLift p vi (f x).val).phase _=(fourFourierLift p vi x.val).phase _
      rw [fourFourierLift_phase h3 vi R x.val x.property.1,
        fourFourierLift_phase h3 vi R (f x).val (f x).property.1]
      have he := congrArg (ZMod.castHom (dvd_mul_left p 2) (ZMod p)) (hf x).2.1
      simpa only [map_add,map_natCast,ZMod.natCast_self,add_zero] using he
  obtain ⟨T,hT⟩ := four_short_pairing_yields_involution lifts hpodd H hv' _ hshort hspan f hpartner
  exact ⟨T,fun x => ⟨f x,hT x,(hf x).2⟩⟩

end Ramanujan.MultiQuintuple
