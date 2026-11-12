import RamanujanTau.MultiQuintupleFourPrimeCertificateLift

/-! The finite block exclusions hold for arbitrary integer family parameters. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators

def FourPrimeCompatible (m n : ℤ) (a b : Fin 6) : Prop :=
  ∀ j : Fin 12,
    fourPrimeCharacter m n (fourPrimeImage a b ((fourPrimeData m n).points j))=
      -fourPrimeCharacter m n ((fourPrimeData m n).points j)

theorem fourPrime_compatible_iff_finite (m n : ℤ) (a b : Fin 6) :
    FourPrimeCompatible m n a b ↔
      FourPrimeFiniteCompatible (fourPrimeResidue m) (fourPrimeResidue n) a b := by
  simp only [FourPrimeCompatible,FourPrimeFiniteCompatible,fourPrimeData,
    fourPrime_character_residue m n]

/-- Any character-reversing block pair has one of the four long-plane
reflections, and at least one of m,n,m−n,m+n is divisible by nine. -/
theorem fourPrime_symmetry_necessary (m n : ℤ)
    (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) (a b : Fin 6)
    (hcompat : FourPrimeCompatible m n a b) :
    a.val<4 ∧ ((9 : ℤ) ∣ m ∨ (9 : ℤ) ∣ n ∨ (9 : ℤ) ∣ m-n ∨ (9 : ℤ) ∣ m+n) := by
  have hf := (fourPrime_compatible_iff_finite m n a b).mp hcompat
  obtain ⟨ha,hclasses⟩ := fourPrime_symmetry_finite (fourPrimeResidue m) (fourPrimeResidue n)
    (fourPrime_residue_norm_unit m n hp3)
  refine ⟨ha a b hf,?_⟩
  rcases hclasses.mp ⟨a,b,hf⟩ with hm | hn | heq | hsum
  · left
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    rw [← fourPrimeResidue_cast9 m,hm]
    rfl
  · right; left
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    rw [← fourPrimeResidue_cast9 n,hn]
    rfl
  · right; right; left
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    push_cast
    rw [← fourPrimeResidue_cast9 m,← fourPrimeResidue_cast9 n,heq,sub_self]
  · right; right; right
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    have hz : (((fourPrimeResidue m).val+(fourPrimeResidue n).val : ℕ) : ZMod 9)=0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hsum)
    simpa only [Nat.cast_add,fourPrimeResidue_cast9,Int.cast_add] using hz

end Ramanujan.MultiQuintuple
