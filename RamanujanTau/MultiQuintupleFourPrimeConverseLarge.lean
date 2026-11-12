import RamanujanTau.MultiQuintupleFourPrimePhaseBlocks

/-! Complete necessity, and the resulting equivalence, for primes above 100. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 3000000

/-- Actual persistent coefficient vanishing forces both the modulo-nine
parameter condition and one of the four reflection residues. -/
theorem fourPrime_vanishing_necessary_large {p m n R : ℕ} [Fact p.Prime]
    (hp : p=m^2+n^2) (hp100 : 100<p) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p)
    (hz : PersistentFourVanishing p (fourPrimeFamilyIndices m n) R) :
    ((9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
      (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ)) ∧
    ∃ b : Fin 4, (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b := by
  have hprime : p.Prime := Fact.out
  have hpi : (p : ℤ)=(m : ℤ)*(m : ℤ)+(n : ℤ)*(n : ℤ) := by
    exact_mod_cast (show p=m*m+n*n by simpa only [pow_two] using hp)
  have hp3 : (p : ZMod 3) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff p 3).not.mpr
    intro hd
    rcases (Nat.dvd_prime hprime).mp hd with h | h <;> omega
  have unit (a : ℕ) (ha : 0<a) (hap : a<p) : (a : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff a p).not.mpr (Nat.not_dvd_of_pos_of_lt ha hap)
  have h2 : (2 : ZMod p) ≠ 0 := unit 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := unit 3 (by omega) (by omega)
  have hm : ((m : ℤ) : ZMod p) ≠ 0 := by simpa using unit m (by omega) (by omega)
  have hn : ((n : ℤ) : ZMod p) ≠ 0 := by simpa using unit n hnpos (by omega)
  have hvi : (((m : ℤ)-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_sub hnm.le,Int.cast_sub,Int.cast_natCast] using unit (m-n) (by omega) (by omega)
  have hd : ((m : ℤ) : ZMod p)-((n : ℤ) : ZMod p) ≠ 0 := by simpa using hvi
  have hs : ((m : ℤ) : ZMod p)+((n : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_add,Int.cast_natCast] using unit (m+n) (by omega) (by omega)
  have hpp : ((m : ℤ) : ZMod p)*((m : ℤ) : ZMod p)+((n : ℤ) : ZMod p)*((n : ℤ) : ZMod p)=0 := by
    have hh := congrArg (fun a : ℤ => (a : ZMod p)) hpi
    simpa only [Int.cast_natCast,ZMod.natCast_self,Int.cast_mul,Int.cast_add] using hh.symm
  have hp3' : (((m : ℤ)*(m : ℤ)+(n : ℤ)*(n : ℤ) : ℤ) : ZMod 3) ≠ 0 := by
    rw [← hpi]; simpa using hp3
  obtain ⟨T,_,hL,hshort⟩ := fourPrime_vanishing_lattice_involution hp hp100 hnpos hnm hbound hR hz
  obtain ⟨a,b,hv,hj,hu,hw⟩ := fourPrime_lattice_blocks m n hpi (by omega) h3 hm T hL
  have hcompat := fourPrime_blocks_compatible m n hpi hp100 hp3 h3 hm T (by
    intro x
    obtain ⟨y,he,_,hc⟩ := hshort x
    exact ⟨y,he,hc⟩) a b hv hj hu hw
  obtain ⟨ha,h9⟩ := fourPrime_symmetry_necessary m n hp3' a b hcompat
  refine ⟨h9,?_⟩
  let v := fourPrimeV (m : ℤ) (n : ℤ)
  let c : ZMod p := (((2*(R : ℤ)-(∑ i, v i) : ℤ) : ZMod p)/3)
  have hc : c=(2*((R : ℤ) : ZMod p)-3*((m : ℤ) : ZMod p)-((n : ℤ) : ZMod p))/3 := by
    dsimp [c,v,fourPrimeV]
    simp [Fin.sum_univ_succ]
    ring
  have hvdiv : (p : ℤ) ∣ fourVectorNorm v := by
    dsimp [v]; rw [fourPrime_long_norm,← hpi]; exact dvd_mul_left _ _
  have hpres : ∀ x ∈ fourProjectiveModule p v, ∃ y ∈ fourProjectiveModule p v,
      T.linear (fourIntToRat x)=fourIntToRat y ∧ fourLatticePhase p v c y=fourLatticePhase p v c x := by
    apply four_phase_preserved_of_integral_generators hprime.ne_zero hvdiv c (fourShortPointSet p v)
      (fourPrime_short_span_eq_projective m n hpi hp100 hp3 h3 hm) T.linear
    rintro x ⟨s,rfl⟩
    obtain ⟨t,he,hphase,_⟩ := hshort s
    refine ⟨fourDualPoint p v t.val,?_,he,?_⟩
    · exact ⟨(fourFourierLift p v t.val).scalar,(fourFourierLift p v t.val).remainder,
        (fourFourierLift p v t.val).point_eq⟩
    · exact four_short_phase_preservation h3 v hvi R s t hphase
  have phase_eq (x : Fin 4 → ℤ) (hx : x ∈ fourProjectiveModule p v) (y : Fin 4 → ℤ)
      (he : T.linear (fourIntToRat x)=fourIntToRat y) :
      fourLatticePhase p v c y=fourLatticePhase p v c x := by
    obtain ⟨z,_,hz,hphase⟩ := hpres x hx
    have heq : z=y := fourIntToRat_injective (hz.symm.trans he)
    rwa [heq] at hphase
  have hjmem := fourPrime_j_projective (m : ℤ) (n : ℤ) hpp hn
  have hvphase := phase_eq v (fourProjectiveModule_base p v) _ hv
  have hjphase := phase_eq _ hjmem _ hj
  change fourLatticePhase p (fourPrimeV (m : ℤ) (n : ℤ)) c _=_ at hvphase hjphase
  rw [fourPrime_phase_pair m n hpi hvi hjmem,fourPrime_phase_v m n hpi hvi,hc] at hvphase
  rw [fourPrime_phase_pair m n hpi hvi hjmem,fourPrime_phase_j,hc] at hjphase
  apply fourPrime_phase_blocks_residue (m : ℤ) (n : ℤ) (R : ℤ) h2 h3 hm hn hd hs hpp a ha
  · simpa only [neg_div] using hvphase
  · simpa only [neg_div] using hjphase

/-- The uniform prime-family classification above the finite cutoff. -/
theorem fourPrime_vanishing_iff_large {p m n R : ℕ} [Fact p.Prime]
    (hp : p=m^2+n^2) (hp100 : 100<p) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (hR : R<p) :
    PersistentFourVanishing p (fourPrimeFamilyIndices m n) R ↔
      ((9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
        (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ)) ∧
      ∃ b : Fin 4, (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b := by
  constructor
  · exact fourPrime_vanishing_necessary_large hp hp100 hnpos hnm hbound hR
  · rintro ⟨h9,b,hb⟩ N
    exact coeff_fourReflection_prime_zero p m n R N b Fact.out hp hnpos hnm hbound h9 hb

end Ramanujan.MultiQuintuple
