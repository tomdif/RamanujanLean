import RamanujanTau.MultiQuintupleFourPrimeSmallCases
import RamanujanTau.MultiQuintupleFourPrimeSmall89
import RamanujanTau.MultiQuintupleFourFortyOneConverse
import RamanujanTau.MultiQuintupleFourFiftyThreeConverse
import RamanujanTau.MultiQuintupleFourNinetySevenConverse

/-! Complete actual-coefficient classification for the prime reflection family. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxHeartbeats 2000000

theorem fourPrime_vanishing_necessary_small {p m n R : ℕ} [Fact p.Prime]
    (hp : p=m^2+n^2) (hp100 : p≤100) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p)
    (hz : PersistentFourVanishing p (fourPrimeFamilyIndices m n) R) :
    ((9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
      (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ)) ∧
    ∃ b : Fin 4, (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b := by
  rcases fourPrime_small_cases Fact.out hp hp100 hnpos hnm hbound with
    h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl,rfl⟩; norm_num at hp; subst p
  · exact False.elim (four13_not_persistent R hR hz)
  · exact False.elim (four17_not_persistent R hR hz)
  · exact False.elim (four29_not_persistent R hR hz)
  · have hr := (four41_persistent_vanishing_iff R hR).mp hz
    rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
  · exact False.elim (four37_not_persistent R hR hz)
  · exact False.elim (four61_not_persistent R hR hz)
  · have hr := (four53_persistent_vanishing_iff R hR).mp hz
    rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
  · exact False.elim (four73_not_persistent R hR hz)
  · exact False.elim (four89_not_persistent R hR hz)
  · have hr := (four97_persistent_vanishing_iff R hR).mp hz
    rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Every canonical prime reflection-family product is classified, with no
spanning premise or remaining small-prime exceptions. -/
theorem fourPrime_vanishing_iff {p m n R : ℕ} [Fact p.Prime]
    (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p) :
    PersistentFourVanishing p (fourPrimeFamilyIndices m n) R ↔
      ((9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
        (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ)) ∧
      ∃ b : Fin 4, (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b := by
  constructor
  · intro hz
    by_cases hlarge : 100<p
    · exact fourPrime_vanishing_necessary_large hp hlarge hnpos hnm hbound hR hz
    · exact fourPrime_vanishing_necessary_small hp (by omega) hnpos hnm hbound hR hz
  · rintro ⟨h9,b,hb⟩ N
    exact coeff_fourReflection_prime_zero p m n R N b Fact.out hp hnpos hnm hbound h9 hb

/-- Expanded actual-product form of the prime-family classification. -/
theorem coeff_fourReflection_prime_iff (p m n R : ℕ)
    (hprime : p.Prime) (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p) :
    (∀ N : ℕ, coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0) ↔
    ((9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
      (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ)) ∧
    ((p : ℤ) ∣ 3*(m : ℤ)+(n : ℤ)-18-2*(R : ℤ) ∨
      (p : ℤ) ∣ 2*(R : ℤ)-3*(m : ℤ)-(n : ℤ) ∨
      (p : ℤ) ∣ (n : ℤ)*((m : ℤ)+2*(n : ℤ)-9)-((n : ℤ)-(m : ℤ))*(R : ℤ) ∨
      (p : ℤ) ∣ (n : ℤ)*(2*(m : ℤ)-(n : ℤ)-9)-((m : ℤ)+(n : ℤ))*(R : ℤ)) := by
  letI : Fact p.Prime := ⟨hprime⟩
  change PersistentFourVanishing p (fourPrimeFamilyIndices m n) R ↔ _
  rw [fourPrime_vanishing_iff hp hnpos hnm hbound hR]
  simp [Fin.exists_fin_succ,fourReflectionResidue]

end Ramanujan.MultiQuintuple
