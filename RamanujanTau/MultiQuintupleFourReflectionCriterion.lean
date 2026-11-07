import RamanujanTau.MultiQuintupleFourReflection

/-!
# Exact congruence criterion for the sixteen specified reflection maps

This classifies branch compatibility of these maps, not coefficient vanishing
for arbitrary four-factor products. Necessity is already detected at the
all-zero Watson point; the small finite test is checked by Lean's kernel.
-/
namespace Ramanujan.MultiQuintuple
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def fourReflectionOriginCompatible (m n : ZMod 9) (a b : Fin 4) : Prop :=
  ∃ bits : Fin 4 → Bool,
    quadWeight (quadAssemble bits (fun _ => 0)) = -1 ∧
    ∀ i, fourReflectionRaw m n a b (fun _ => 0)
      ((m^2+n^2)⁻¹*fourLongNum m n b (fun _ => 0)) i =
      3*(if bits i then 1 else 0)

set_option maxHeartbeats 0 in
/-- Exhaustion of 9×9 parameter classes and 16 maps; no external evaluator is trusted. -/
private theorem fourReflection_origin_finite :
    ∀ (m n : ZMod 9) (a b : Fin 4), Nat.Coprime (m^2+n^2).val 9 →
      (fourReflectionOriginCompatible m n a b ↔ fourReflectionCondition m n a b=0) := by
  unfold fourReflectionOriginCompatible
  decide +kernel


/-- Even the origin forces the listed congruence when the modulus-nine norm is a unit. -/
theorem fourReflection_origin_iff (m n : ZMod 9) (a b : Fin 4)
    (hp : IsUnit (m^2+n^2)) :
    fourReflectionOriginCompatible m n a b ↔ fourReflectionCondition m n a b=0 := by
  apply fourReflection_origin_finite m n a b
  apply (ZMod.isUnit_iff_coprime (m^2+n^2).val 9).mp
  simpa using hp

/-- Compatibility on every signed Watson branch, for the specified rational reflection. -/
def fourReflectionNineCompatible (m n : ZMod 9) (a b : Fin 4) : Prop :=
  ∀ x : QuadQuintBranchIndex, ∃ bits : Fin 4 → Bool,
    quadWeight (quadAssemble bits (fun _ => 0)) = -quadWeight x ∧
    ∀ i, fourReflectionRaw m n a b (fun j => (quadZ x j : ZMod 9))
      ((m^2+n^2)⁻¹*fourLongNum m n b (fun j => (quadZ x j : ZMod 9))) i =
      3*(if bits i then 1 else 0)

/-- Necessary and sufficient congruence for each of the sixteen maps to respect signed branches. -/
theorem fourReflection_branch_iff (m n : ZMod 9) (a b : Fin 4)
    (hp : IsUnit (m^2+n^2)) :
    fourReflectionNineCompatible m n a b ↔ fourReflectionCondition m n a b=0 := by
  constructor
  · intro h
    apply (fourReflection_origin_iff m n a b hp).mp
    let x0 := quadAssemble (fun _ => false) (fun _ => 0)
    obtain ⟨bits,hw,hi⟩ := h x0
    have hz0 : quadZ x0=(fun _ => 0) := by
      funext i
      fin_cases i <;> rfl
    have hw0 : quadWeight x0=1 := by
      norm_num [x0,quadWeight,quadAssemble,pointBranchWeight,quadB4,
        pointB1,pointB2,pointB3,branchSign]
    refine ⟨bits,by simpa only [hw0] using hw,?_⟩
    simpa only [hz0,Int.cast_zero] using hi
  · intro hs x
    refine ⟨fourPlaneBits (fourReflectionBranch a) (quadBits x),
      fourPlane_bits_weight (fourReflectionBranch a) x _,?_⟩
    intro i
    have hk : (m^2+n^2)*((m^2+n^2)⁻¹*
        fourLongNum m n b (fun j => (quadZ x j : ZMod 9)))=
        fourLongNum m n b (fun j => (quadZ x j : ZMod 9)) := by
      rw [← mul_assoc,ZMod.mul_inv_of_unit _ hp,one_mul]
    rw [fourReflection_raw_mod_nine m n a b hp hs _ _ hk i]
    have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr
      (fourPlane_rule_branch (fourReflectionBranch a) x i)
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,fourPlaneZRule_cast] at hb
    simpa only [apply_ite,Int.cast_one,Int.cast_zero] using sub_eq_zero.mp hb


/-- Exact parameter criterion for availability of a compatible map in this collection. -/
theorem fourReflection_exists_iff (m n : ZMod 9) (hp : IsUnit (m^2+n^2)) :
    (∃ a b : Fin 4, fourReflectionNineCompatible m n a b) ↔
      m=0 ∨ n=0 ∨ m-n=0 ∨ m+n=0 := by
  constructor
  · rintro ⟨a,b,h⟩
    have hs := (fourReflection_branch_iff m n a b hp).mp h
    fin_cases a <;> fin_cases b <;> dsimp [fourReflectionCondition] at hs <;> tauto
  · intro hs
    rcases hs with h | h | h | h
    · exact ⟨2,0,(fourReflection_branch_iff m n 2 0 hp).mpr
        (by simpa [fourReflectionCondition] using h)⟩
    · exact ⟨3,0,(fourReflection_branch_iff m n 3 0 hp).mpr
        (by simpa [fourReflectionCondition] using h)⟩
    · exact ⟨1,0,(fourReflection_branch_iff m n 1 0 hp).mpr
        (by simpa [fourReflectionCondition] using h)⟩
    · exact ⟨0,0,(fourReflection_branch_iff m n 0 0 hp).mpr
        (by simpa [fourReflectionCondition] using h)⟩

end Ramanujan.MultiQuintuple
