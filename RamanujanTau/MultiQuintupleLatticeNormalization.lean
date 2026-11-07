/-
# Normalization of projective dual lattices

Integral generation is invariant under signed coordinate permutations and
rescaling the projective generator modulo p.
-/
import RamanujanTau.MultiQuintupleNormalizedGenerators

namespace Ramanujan.MultiQuintuple

def ternaryMod (p : ℕ) : TernaryIntPoint →ₗ[ℤ] ((ZMod p × ZMod p) × ZMod p) where
  toFun x := ((x.1.1,x.1.2),x.2)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp [zsmul_eq_mul]

theorem mem_projectiveDualLattice_iff_mod {p : ℕ} [NeZero p]
    (v x : TernaryIntPoint) :
    x ∈ projectiveDualLattice p v ↔
      ∃ a : ZMod p, ternaryMod p x = a • ternaryMod p v := by
  constructor
  · rintro ⟨a,z,rfl⟩
    refine ⟨a,?_⟩
    ext <;> simp [ternaryMod,zsmul_eq_mul]
  · rintro ⟨a,ha⟩
    have h1 : (p : ℤ) ∣ x.1.1-(a.val : ℤ)*v.1.1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hh := congrArg (fun z => z.1.1) ha
      simpa [ternaryMod,sub_eq_zero] using hh
    have h2 : (p : ℤ) ∣ x.1.2-(a.val : ℤ)*v.1.2 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hh := congrArg (fun z => z.1.2) ha
      simpa [ternaryMod,sub_eq_zero] using hh
    have h3 : (p : ℤ) ∣ x.2-(a.val : ℤ)*v.2 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hh := congrArg Prod.snd ha
      simpa [ternaryMod,sub_eq_zero] using hh
    obtain ⟨b,hb⟩ := h1
    obtain ⟨c,hc⟩ := h2
    obtain ⟨d,hd⟩ := h3
    refine ⟨a.val,((b,c),d),?_⟩
    apply Prod.ext
    · apply Prod.ext
      · change x.1.1 = (a.val : ℤ)*v.1.1+(p : ℤ)*b
        omega
      · change x.1.2 = (a.val : ℤ)*v.1.2+(p : ℤ)*c
        omega
    · change x.2 = (a.val : ℤ)*v.2+(p : ℤ)*d
      omega

theorem projectiveDualLattice_eq_of_mod {p : ℕ} [Fact p.Prime]
    (u v : TernaryIntPoint) (a : ZMod p) (ha : a ≠ 0)
    (huv : ternaryMod p u = a • ternaryMod p v) :
    projectiveDualLattice p u = projectiveDualLattice p v := by
  ext x
  rw [mem_projectiveDualLattice_iff_mod,mem_projectiveDualLattice_iff_mod]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b*a,by rw [hb,huv,mul_smul]⟩
  · rintro ⟨b,hb⟩
    refine ⟨b/a,?_⟩
    rw [huv,← mul_smul,div_mul_cancel₀ _ ha,hb]

theorem projectiveDualLattice_map (p : ℕ) (v : TernaryIntPoint)
    (f : TernaryIntPoint ≃ₗ[ℤ] TernaryIntPoint) :
    (projectiveDualLattice p v).map f.toLinearMap = projectiveDualLattice p (f v) := by
  ext x
  constructor
  · rintro ⟨y,⟨a,z,rfl⟩,rfl⟩
    exact ⟨a,f z,by rw [map_add,map_smul,map_smul]; rfl⟩
  · rintro ⟨a,z,rfl⟩
    refine ⟨a • v+(p : ℤ) • f.symm z,⟨a,f.symm z,rfl⟩,?_⟩
    rw [map_add,map_smul,map_smul]
    change a • f v+(p : ℤ) • f (f.symm z) = _
    rw [LinearEquiv.apply_symm_apply]

theorem short_generation_transport (p : ℕ) (v : TernaryIntPoint)
    (f : TernaryIntPoint ≃ₗ[ℤ] TernaryIntPoint)
    (hnorm : ∀ x, ternaryIntNorm (f x) = ternaryIntNorm x)
    (hsupport : ∀ x, ternaryCubicCharacter (f x) ≠ 0 ↔ ternaryCubicCharacter x ≠ 0)
    (hgen : Submodule.span ℤ (shortSupportedDualSet p (f v)) =
      projectiveDualLattice p (f v)) :
    Submodule.span ℤ (shortSupportedDualSet p v) = projectiveDualLattice p v := by
  have hset : shortSupportedDualSet p (f v) = f '' shortSupportedDualSet p v := by
    ext y
    constructor
    · rintro ⟨hy,hn,hs⟩
      refine ⟨f.symm y,⟨?_,?_,?_⟩,by simp⟩
      · rw [← projectiveDualLattice_map p v f] at hy
        obtain ⟨x,hx,hxy⟩ := hy
        simpa [← hxy] using hx
      · have h := hnorm (f.symm y)
        simp only [LinearEquiv.apply_symm_apply] at h
        rwa [← h]
      · exact (hsupport (f.symm y)).mp (by simpa using hs)
    · rintro ⟨x,⟨hx,hn,hs⟩,rfl⟩
      refine ⟨?_,by simpa [hnorm] using hn,(hsupport x).mpr hs⟩
      rw [← projectiveDualLattice_map p v f]
      exact ⟨x,hx,rfl⟩
  rw [hset] at hgen
  change Submodule.span ℤ (f.toLinearMap '' shortSupportedDualSet p v) = _ at hgen
  rw [← Submodule.map_span,← projectiveDualLattice_map p v f] at hgen
  exact (Submodule.map_injective_of_injective f.injective) hgen

def ternarySignSymmetry (s t : ℤ) (hs : s*s=1) (ht : t*t=1) :
    TernaryIntPoint ≃ₗ[ℤ] TernaryIntPoint where
  toFun x := ((x.1.1,s*x.1.2),t*x.2)
  invFun x := ((x.1.1,s*x.1.2),t*x.2)
  left_inv := by intro x; ext <;> simp [← mul_assoc,hs,ht]
  right_inv := by intro x; ext <;> simp [← mul_assoc,hs,ht]
  map_add' := by intros; ext <;> simp [mul_add]
  map_smul' := by intros; ext <;> simp [mul_left_comm]

theorem ternarySignSymmetry_norm (s t : ℤ) (hs : s*s=1) (ht : t*t=1)
    (x : TernaryIntPoint) :
    ternaryIntNorm (ternarySignSymmetry s t hs ht x) = ternaryIntNorm x := by
  change x.1.1^2+(s*x.1.2)^2+(t*x.2)^2 = x.1.1^2+x.1.2^2+x.2^2
  have hs' : s^2=1 := by nlinarith
  have ht' : t^2=1 := by nlinarith
  simp [mul_pow,hs',ht']

theorem ternarySignSymmetry_support (s t : ℤ) (hs : s*s=1) (ht : t*t=1)
    (x : TernaryIntPoint) :
    ternaryCubicCharacter (ternarySignSymmetry s t hs ht x) ≠ 0 ↔
      ternaryCubicCharacter x ≠ 0 := by
  have hs0 : (s : ZMod 3) ≠ 0 := by
    have h : (s : ZMod 3)*(s : ZMod 3)=1 := by rw [← Int.cast_mul,hs]; rfl
    intro hz; simp [hz] at h
  have ht0 : (t : ZMod 3) ≠ 0 := by
    have h : (t : ZMod 3)*(t : ZMod 3)=1 := by rw [← Int.cast_mul,ht]; rfl
    intro hz; simp [hz] at h
  simp [ternaryCubicCharacter,ternarySignSymmetry,mul_ne_zero_iff,hs0,ht0]

def ternarySwapLast : TernaryIntPoint ≃ₗ[ℤ] TernaryIntPoint where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ternarySwapLast_norm (x : TernaryIntPoint) :
    ternaryIntNorm (ternarySwapLast x) = ternaryIntNorm x := by
  simp [ternaryIntNorm,ternaryNorm,ternarySwapLast]
  ring

theorem ternarySwapLast_support (x : TernaryIntPoint) :
    ternaryCubicCharacter (ternarySwapLast x) ≠ 0 ↔ ternaryCubicCharacter x ≠ 0 := by
  simp [ternaryCubicCharacter,ternarySwapLast,mul_assoc,mul_comm,mul_left_comm]

theorem exists_signed_canonical_residue {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ s : ℤ, 0 < n ∧ 2*n < p ∧ s*s=1 ∧ (n : ZMod p) = s*a := by
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨h,hp⟩ := hpodd
  have hav := ZMod.val_lt a
  have ha0 : 0 < a.val := by
    by_contra hn
    have hz : a.val=0 := by omega
    exact ha ((ZMod.val_eq_zero a).mp hz)
  by_cases hsmall : 2*a.val < p
  · exact ⟨a.val,1,ha0,hsmall,by norm_num,by simp⟩
  · refine ⟨(-a).val,-1,?_,?_,by norm_num,by simp⟩
    all_goals rw [ZMod.neg_val,if_neg ha]; omega

theorem signed_ratio_square {p : ℕ} [Fact p.Prime]
    (i j n : ℕ) (s : ℤ) (hi0 : (i : ZMod p) ≠ 0) (hs : s*s=1)
    (hn : (n : ZMod p) = s*((j : ZMod p)/i)) :
    (i : ZMod p)^2*(n : ZMod p)^2 = (j : ZMod p)^2 := by
  have hs' : (s : ZMod p)^2=1 := by
    rw [pow_two,← Int.cast_mul,hs]
    simp
  rw [hn,mul_pow,hs',one_mul,div_pow]
  exact mul_div_cancel₀ _ (pow_ne_zero _ hi0)

/-- Normalized ordered triples suffice for integral generation at an
arbitrary admissible triple. No residue or phase is changed in this step. -/
theorem short_generation_of_normalized
    {p i j k : ℕ} (ha : AdmissibleSparseTriple p i j k)
    (hgen : ∀ a b : ℕ, 1 < a → a < b → 2*b < p →
      (1 : ZMod p)+(a : ZMod p)^2+(b : ZMod p)^2=0 →
      Submodule.span ℤ (shortSupportedDualSet p ((1,(a : ℤ)),(b : ℤ))) =
        projectiveDualLattice p ((1,(a : ℤ)),(b : ℤ))) :
    Submodule.span ℤ (shortSupportedDualSet p (((i : ℤ),(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) := by
  obtain ⟨hp,hp3,hi,hij,hjk,hkp,hiso⟩ := ha
  letI : Fact p.Prime := ⟨hp⟩
  have hi0 : (i : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff i p).not.mpr (Nat.not_dvd_of_pos_of_lt hi (by omega))
  have hj0 : (j : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff j p).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hk0 : (k : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff k p).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  obtain ⟨a,s,ha0,hap,hs,has⟩ := exists_signed_canonical_residue (by omega : p ≠ 2)
    ((j : ZMod p)/i) (div_ne_zero hj0 hi0)
  obtain ⟨b,t,hb0,hbp,ht,hbt⟩ := exists_signed_canonical_residue (by omega : p ≠ 2)
    ((k : ZMod p)/i) (div_ne_zero hk0 hi0)
  have hasq := signed_ratio_square i j a s hi0 hs has
  have hbsq := signed_ratio_square i k b t hi0 ht hbt
  have ha1 : 1 < a := by
    by_contra hn
    have he : a=1 := by omega
    have hsquare : (i : ZMod p)^2=(j : ZMod p)^2 := by simpa [he] using hasq
    have heq := canonical_square_root_unique i j hi (by omega) (by omega) hsquare
    omega
  have hb1 : 1 < b := by
    by_contra hn
    have he : b=1 := by omega
    have hsquare : (i : ZMod p)^2=(k : ZMod p)^2 := by simpa [he] using hbsq
    have heq := canonical_square_root_unique i k hi (by omega) hkp hsquare
    omega
  have hab : a ≠ b := by
    intro he
    have hsquare : (j : ZMod p)^2=(k : ZMod p)^2 := by rw [← hasq,← hbsq,he]
    have heq := canonical_square_root_unique j k (by omega) (by omega) hkp hsquare
    omega
  have hiso' : (i : ZMod p)^2+(j : ZMod p)^2+(k : ZMod p)^2=0 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (ternaryNorm i j k) p).mpr hiso
    simpa [ternaryNorm] using hz
  have hisoab : (1 : ZMod p)+(a : ZMod p)^2+(b : ZMod p)^2=0 := by
    apply (mul_eq_zero.mp (show (i : ZMod p)^2*(1+(a : ZMod p)^2+(b : ZMod p)^2)=0 from ?_)).resolve_left
      (pow_ne_zero _ hi0)
    rw [mul_add,mul_add,mul_one,hasq,hbsq]
    exact hiso'
  have hgenab : Submodule.span ℤ (shortSupportedDualSet p ((1,(a : ℤ)),(b : ℤ))) =
      projectiveDualLattice p ((1,(a : ℤ)),(b : ℤ)) := by
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact hgen a b ha1 hab hbp hisoab
    · apply short_generation_transport p ((1,(a : ℤ)),(b : ℤ)) ternarySwapLast
        ternarySwapLast_norm ternarySwapLast_support
      exact hgen b a hb1 hba hap (by linear_combination hisoab)
  let v : TernaryIntPoint := (((i : ℤ),(j : ℤ)),(k : ℤ))
  let f := ternarySignSymmetry s t hs ht
  have hmod : ternaryMod p ((1,(a : ℤ)),(b : ℤ)) = (i : ZMod p)⁻¹ • ternaryMod p (f v) := by
    ext <;> simp [ternaryMod,f,v,ternarySignSymmetry,has,hbt,hi0,
      div_eq_mul_inv,mul_comm,mul_left_comm]
  have hN := projectiveDualLattice_eq_of_mod ((1,(a : ℤ)),(b : ℤ)) (f v)
    (i : ZMod p)⁻¹ (inv_ne_zero hi0) hmod
  apply short_generation_transport p v f (ternarySignSymmetry_norm s t hs ht)
    (ternarySignSymmetry_support s t hs ht)
  simpa only [shortSupportedDualSet,hN] using hgenab

end Ramanujan.MultiQuintuple
