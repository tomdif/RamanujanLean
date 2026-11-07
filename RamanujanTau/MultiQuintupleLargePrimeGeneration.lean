/-
# Supported short vectors integrally generate every large-prime dual lattice
-/
import RamanujanTau.MultiQuintupleNormalizedGram
import RamanujanTau.MultiQuintupleGramSchmidt
import RamanujanTau.MultiQuintupleSmallIsotropicBox
import RamanujanTau.MultiQuintupleShortGeneratorEstimate

namespace Ramanujan.MultiQuintuple

theorem ternaryMod_eq_zero_iff (p : ℕ) (x : TernaryIntPoint) :
    ternaryMod p x = 0 ↔ ∃ y : TernaryIntPoint, x=(p : ℤ) • y := by
  constructor
  · intro hx
    have h1 := congrArg (fun z : (ZMod p × ZMod p) × ZMod p => z.1.1) hx
    have h2 := congrArg (fun z : (ZMod p × ZMod p) × ZMod p => z.1.2) hx
    have h3 := congrArg (fun z : (ZMod p × ZMod p) × ZMod p => z.2) hx
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.1 p).mp h1
    obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.2 p).mp h2
    obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.2 p).mp h3
    exact ⟨((a,b),c),Prod.ext (Prod.ext ha hb) hc⟩
  · rintro ⟨y,rfl⟩
    ext <;> simp [ternaryMod]

theorem TernaryUnimodularBasis.map_mod_zero_iff (B : TernaryUnimodularBasis)
    (p : ℕ) (u : TernaryIntPoint) : ternaryMod p (B.map u)=0 ↔ ternaryMod p u=0 := by
  rw [ternaryMod_eq_zero_iff,ternaryMod_eq_zero_iff]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,rfl⟩ := B.map_surjective y
    refine ⟨z,B.map_injective ?_⟩
    rw [map_smul]
    exact hy
  · rintro ⟨y,rfl⟩
    exact ⟨B.map y,map_smul _ _ _⟩

theorem normalizedDualMap_mod_three_zero_iff (p j k : ℕ) (hp : (p : ZMod 3) ≠ 0)
    (u : TernaryIntPoint) :
    ternaryMod 3 (normalizedDualMap p j k u)=0 ↔ ternaryMod 3 u=0 := by
  constructor
  · intro h
    have h1 := congrArg (fun z : (ZMod 3 × ZMod 3) × ZMod 3 => z.1.1) h
    have h2 := congrArg (fun z : (ZMod 3 × ZMod 3) × ZMod 3 => z.1.2) h
    have h3 := congrArg (fun z : (ZMod 3 × ZMod 3) × ZMod 3 => z.2) h
    change (u.1.1 : ZMod 3)=0 at h1
    simp only [ternaryMod,normalizedDualMap,LinearMap.coe_mk,AddHom.coe_mk,
      Prod.fst_zero,Prod.snd_zero,Int.cast_add,Int.cast_mul,Int.cast_natCast,h1,mul_zero,zero_add] at h2 h3
    exact Prod.ext (Prod.ext h1 ((mul_eq_zero.mp h2).resolve_left hp))
      ((mul_eq_zero.mp h3).resolve_left hp)
  · intro h
    obtain ⟨y,rfl⟩ := (ternaryMod_eq_zero_iff 3 u).mp h
    rw [map_smul]
    exact (ternaryMod_eq_zero_iff 3 _).mpr ⟨normalizedDualMap p j k y,rfl⟩

private theorem isotropic_nonzero_three_supported :
    ∀ a b c : ZMod 3, a^2+b^2+c^2=0 →
      ¬(a=0 ∧ b=0 ∧ c=0) → a*b*c ≠ 0 := by decide +kernel

theorem small_box_image_supported (p j k : ℕ) (hp3 : (p : ZMod 3) ≠ 0)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) (B : TernaryUnimodularBasis)
    (u : TernaryIntPoint)
    (hu : let H := B.gram (normalizedGram p j k)
      InSmallIsotropicBox H.a H.b H.c H.d H.e H.f u) :
    ternaryCubicCharacter (normalizedDualMap p j k (B.map u)) ≠ 0 := by
  let H := B.gram (normalizedGram p j k)
  obtain ⟨hxl,hxu,hyl,hyu,hz,hne,hiso⟩ := hu
  have hnorm : (H.norm u : ZMod 3)=0 := by
    simp only [IntegralTernaryGram.norm,IntegralTernaryGram.dot,
      Int.cast_add,Int.cast_mul]
    change (H.a : ZMod 3)*u.1.1*u.1.1+(H.b : ZMod 3)*u.1.2*u.1.2+
      (H.c : ZMod 3)*u.2*u.2+(H.d : ZMod 3)*(u.1.1*u.1.2+u.1.2*u.1.1)+
      (H.e : ZMod 3)*(u.1.1*u.2+u.2*u.1.1)+(H.f : ZMod 3)*(u.1.2*u.2+u.2*u.1.2)=0
    linear_combination hiso
  let w := normalizedDualMap p j k (B.map u)
  have hnormw : ((w.1.1 : ZMod 3)^2+(w.1.2 : ZMod 3)^2+(w.2 : ZMod 3)^2)=0 := by
    have he := normalizedGram_norm p j k hi (B.map u)
    rw [← B.gram_norm] at he
    have hh := congrArg (fun n : ℤ => (n : ZMod 3)) he
    change (((B.gram (normalizedGram p j k)).norm u : ℤ) : ZMod 3)=0 at hnorm
    simpa [ternaryIntNorm,ternaryNorm,hnorm] using hh.symm
  have hnonzero : ¬((w.1.1 : ZMod 3)=0 ∧ (w.1.2 : ZMod 3)=0 ∧ (w.2 : ZMod 3)=0) := by
    rintro ⟨hw1,hw2,hw3⟩
    have hw : ternaryMod 3 w=0 := Prod.ext (Prod.ext hw1 hw2) hw3
    have hu0 := (B.map_mod_zero_iff 3 u).mp
      ((normalizedDualMap_mod_three_zero_iff p j k hp3 (B.map u)).mp hw)
    obtain ⟨z,hz⟩ := (ternaryMod_eq_zero_iff 3 u).mp hu0
    rcases hne with h | h | h
    · exact h (Int.dvd_iff_emod_eq_zero.mp ⟨z.1.1,congrArg (fun t : TernaryIntPoint => t.1.1) hz⟩)
    · exact h (Int.dvd_iff_emod_eq_zero.mp ⟨z.1.2,congrArg (fun t : TernaryIntPoint => t.1.2) hz⟩)
    · exact h (Int.dvd_iff_emod_eq_zero.mp ⟨z.2,congrArg (fun t : TernaryIntPoint => t.2) hz⟩)
  exact isotropic_nonzero_three_supported _ _ _ hnormw hnonzero

theorem small_box_image_short {p j k : ℕ} (hp : 1250 ≤ p)
    (hj : 1 < j) (hjk : j < k) (hkp : 2*k < p)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) (B : TernaryUnimodularBasis)
    (hred : (B.gram (normalizedGram p j k)).Reduced) (u : TernaryIntPoint)
    (hu : let H := B.gram (normalizedGram p j k)
      InSmallIsotropicBox H.a H.b H.c H.d H.e H.f u) :
    2*ternaryIntNorm (normalizedDualMap p j k (B.map u)) < (p : ℤ)^2 := by
  let H := B.gram (normalizedGram p j k)
  have hH : H.Positive := B.gram_positive _ (normalizedGram_positive (by omega) j k hi)
  have ha := IntegralTernaryGram.a_pos hH
  have hm := IntegralTernaryGram.minor_pos hH
  have hd : H.det = (p : ℤ) := (B.gram_det _).trans (normalizedGram_det p j k hi)
  have hminor : (H.a : ℚ)*H.secondLength = H.minor := by
    have haQ : (H.a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    unfold IntegralTernaryGram.secondLength
    field_simp
  have hdet : (H.a : ℚ)*H.secondLength*H.thirdLength = p := by
    rw [IntegralTernaryGram.determinant_identity H ha.ne' hm.ne',hd]
    simp
  have hcost := short_generator_cost_lt_half (p : ℚ) H.secondLength H.thirdLength H.a H.minor
    (by exact_mod_cast hp) (by omega) (normalizedGram_minor_ge_three hj hjk hkp hi B)
    hred.2.2.2.1 hred.2.2.2.2 hminor hdet
  obtain ⟨hxl,hxu,hyl,hyu,hz,hne,hiso⟩ := hu
  have huq : (H.norm u : ℚ) ≤ H.thirdLength+(49*(H.a : ℚ)+25*H.secondLength)/4 := by
    rw [IntegralTernaryGram.norm_gram_schmidt H ha.ne' hm.ne']
    apply reduced_ternary_box_cost _ _ _ _ _ _ _ _ _
      (by exact_mod_cast ha.le) (IntegralTernaryGram.secondLength_pos hH).le
      (IntegralTernaryGram.thirdLength_pos hH (by rw [hd]; omega)).le
      hred.1 hred.2.1 hred.2.2.1
    · rw [abs_le]
      exact ⟨by exact_mod_cast hxl,by exact_mod_cast hxu⟩
    · rw [abs_le]
      exact ⟨by exact_mod_cast hyl,by exact_mod_cast hyu⟩
    · rcases hz with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  have heZ := normalizedGram_norm p j k hi (B.map u)
  rw [← B.gram_norm] at heZ
  have heQ : (p : ℚ)*(H.norm u : ℚ) =
      (ternaryIntNorm (normalizedDualMap p j k (B.map u)) : ℚ) := by exact_mod_cast heZ
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hh := mul_lt_mul_of_pos_left (lt_of_le_of_lt huq hcost) hpQ
  have hout : 2*(ternaryIntNorm (normalizedDualMap p j k (B.map u)) : ℚ) < (p : ℚ)^2 := by
    nlinarith
  exact_mod_cast hout

/-- Above the cutoff, the actual normalized projective lattice is generated
over the integers by its supported vectors of squared norm strictly below p²/2. -/
theorem short_generation_normalized_above_1250 {p j k : ℕ} [Fact p.Prime]
    (hp : 1250 ≤ p) (hj : 1 < j) (hjk : j < k) (hkp : 2*k < p)
    (hiso : (1 : ZMod p)+(j : ZMod p)^2+(k : ZMod p)^2=0) :
    Submodule.span ℤ (shortSupportedDualSet p ((1,(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p ((1,(j : ℤ)),(k : ℤ)) := by
  have hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using hiso)
  have hp3 : (p : ZMod 3) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff p 3).not.mpr
    intro h
    have hcases := (Fact.out : p.Prime).eq_one_or_self_of_dvd 3 h
    omega
  obtain ⟨B,hB⟩ := TernaryUnimodularBasis.exists_reduced (normalizedGram p j k)
    (normalizedGram_positive (by omega) j k hi)
  let H := B.gram (normalizedGram p j k)
  have hdet : ternaryGramDetThree H.a H.b H.c H.d H.e H.f ≠ 0 := by
    have hd : H.det=(p : ℤ) := (B.gram_det _).trans (normalizedGram_det p j k hi)
    have he : ternaryGramDetThree H.a H.b H.c H.d H.e H.f=(p : ZMod 3) := by
      have hh := congrArg (fun n : ℤ => (n : ZMod 3)) hd
      simpa [IntegralTernaryGram.det,ternaryGramDetThree] using hh
    rwa [he]
  have hspan := small_isotropic_box_span_eq_top H.a H.b H.c H.d H.e H.f hdet
  let F := (normalizedDualMap p j k).comp B.map
  have hsub : Submodule.span ℤ {u | InSmallIsotropicBox H.a H.b H.c H.d H.e H.f u} ≤
      (Submodule.span ℤ (shortSupportedDualSet p ((1,(j : ℤ)),(k : ℤ)))).comap F := by
    apply Submodule.span_le.mpr
    intro u hu
    exact Submodule.subset_span ⟨normalizedDualMap_mem p j k (B.map u),
      small_box_image_short hp hj hjk hkp hi B hB u hu,
      small_box_image_supported p j k hp3 hi B u hu⟩
  apply le_antisymm (Submodule.span_le.mpr (fun x hx => hx.1))
  intro x hx
  obtain ⟨y,rfl⟩ := normalizedDualMap_surjective_on p j k x hx
  obtain ⟨u,rfl⟩ := B.map_surjective y
  exact hsub (by rw [hspan]; trivial)

theorem short_generation_above_1250 {p i j k : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hp : 1250 ≤ p) :
    Submodule.span ℤ (shortSupportedDualSet p (((i : ℤ),(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) := by
  letI : Fact p.Prime := ⟨ha.1⟩
  apply short_generation_of_normalized ha
  intro a b ha hab hbp hiso
  exact short_generation_normalized_above_1250 hp ha hab hbp hiso

end Ramanujan.MultiQuintuple
