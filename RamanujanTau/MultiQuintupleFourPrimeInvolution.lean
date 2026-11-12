import RamanujanTau.MultiQuintupleFourPrimeSpanning

/-! The actual prime reflection family has a short-vector orthogonal
involution under coefficient vanishing, without a spanning hypothesis. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourPrimeFamilyIndices (m n : ℕ) : Fin 4 → ℕ := ![m-n,n,m,m+n]

theorem fourPrime_family_cast (m n : ℕ) (hnm : n ≤ m) :
    (fun i => (fourPrimeFamilyIndices m n i : ℤ))=fourPrimeV (m : ℤ) (n : ℤ) := by
  ext i
  fin_cases i <;> simp [fourPrimeFamilyIndices,fourPrimeV,Nat.cast_sub hnm]

theorem fourPrime_family_canonical {p m n : ℕ} (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) : fourCanonical p (fourPrimeFamilyIndices m n) := by
  intro i
  fin_cases i <;> simp [fourPrimeFamilyIndices] <;> omega

/-- A uniform consequence of actual coefficient vanishing for every prime
p=m²+n²>100 in the canonical reflection family. The spanning condition is
proved from the finite integer generator certificates. -/
theorem fourPrime_vanishing_involution {p m n R : ℕ} [Fact p.Prime]
    (hp : p=m^2+n^2) (hp100 : 100<p) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p)
    (hz : PersistentFourVanishing p (fourPrimeFamilyIndices m n) R) :
    ∃ T : FourOrthogonalInvolution,
      ∀ x : FourShortIndex p (fourPrimeV (m : ℤ) (n : ℤ)),
      ∃ y : FourShortIndex p (fourPrimeV (m : ℤ) (n : ℤ)),
        T.linear (fourIntToRat (fourDualPoint p (fourPrimeV (m : ℤ) (n : ℤ)) x.val))=
          fourIntToRat (fourDualPoint p (fourPrimeV (m : ℤ) (n : ℤ)) y.val) ∧
        fourCanonicalPhase p (fourPrimeV (m : ℤ) (n : ℤ)) R y.val=
          fourCanonicalPhase p (fourPrimeV (m : ℤ) (n : ℤ)) R x.val+p ∧
        fourCubicCharacter y.val.2= -fourCubicCharacter x.val.2 := by
  have hprime : p.Prime := Fact.out
  have hpi : (p : ℤ)=(m : ℤ)*(m : ℤ)+(n : ℤ)*(n : ℤ) := by
    exact_mod_cast (show p=m*m+n*n by simpa only [pow_two] using hp)
  have hp3 : (p : ZMod 3) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff p 3).not.mpr
    intro hd
    rcases (Nat.dvd_prime hprime).mp hd with h | h <;> omega
  have h3 : (3 : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 3 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hm : ((m : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff m p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hcast := fourPrime_family_cast m n hnm.le
  have hspan : Submodule.span ℚ (Set.range
      (fun x : FourShortIndex p (fun i => (fourPrimeFamilyIndices m n i : ℤ)) =>
        fourIntToRat (fourDualPoint p (fun i => (fourPrimeFamilyIndices m n i : ℤ)) x.val)))=⊤ := by
    rw [hcast]
    exact fourPrime_short_span m n hpi hp100 hp3 h3 hm
  have hnorm : (∑ i, (fourPrimeFamilyIndices m n i : ℤ)*(fourPrimeFamilyIndices m n i : ℤ))=
      (p : ℤ)*3 := by
    simp [fourPrimeFamilyIndices,Fin.sum_univ_succ,Nat.cast_sub hnm.le,hp,pow_two]
    ring
  have hvi : (fourPrimeFamilyIndices m n 0 : ZMod p) ≠ 0 := by
    change ((m-n : ℕ) : ZMod p) ≠ 0
    exact (ZMod.natCast_eq_zero_iff (m-n) p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have h := four_persistent_vanishing_spanning_involution (by omega) h3
    (fourPrime_family_canonical hnpos hnm hbound) hR hz 3 hnorm hvi hspan
  rw [hcast] at h
  exact h

end Ramanujan.MultiQuintuple
