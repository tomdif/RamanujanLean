import RamanujanTau.MultiQuintupleFourLatticePhase
import RamanujanTau.MultiQuintupleFourReflection

/-! The four surviving long-plane blocks force the four reflection residues. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem fourPrime_j_projective {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hpp : (m : ZMod p)*(m : ZMod p)+(n : ZMod p)*(n : ZMod p)=0)
    (hn : (n : ZMod p) ≠ 0) : fourPrimeJ m n ∈ fourProjectiveModule p (fourPrimeV m n) := by
  have hc : ∀ i, (fourPrimeJ m n i : ZMod p)=(m : ZMod p)/(n : ZMod p)*(fourPrimeV m n i : ZMod p) := by
    intro i
    fin_cases i <;> simp [fourPrimeJ,fourPrimeV] <;> field_simp <;>
      linear_combination -hpp
  let x := fourProjectiveLiftOfCast (fourPrimeV m n) (fourPrimeJ m n) ((m : ZMod p)/(n : ZMod p)) hc
  exact ⟨x.scalar,x.remainder,x.point_eq⟩

theorem fourPrime_phase_v {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hvi : ((m-n : ℤ) : ZMod p) ≠ 0) (c : ZMod p) :
    fourLatticePhase p (fourPrimeV m n) c (fourPrimeV m n)=6+c := by
  have hd : fourDot (fourPrimeV m n) (fourPrimeV m n)=(p : ℤ)*3 := by
    change fourVectorNorm (fourPrimeV m n)=_
    rw [fourPrime_long_norm,hp]; ring
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [fourLatticePhase,hd,Int.mul_ediv_cancel_left _ hpz]
  norm_num only [Int.cast_ofNat]
  change (6 : ZMod p)+c*((m-n : ℤ) : ZMod p)/((m-n : ℤ) : ZMod p)=6+c
  field_simp

theorem fourPrime_phase_j {p : ℕ} [Fact p.Prime] (m n : ℤ) (c : ZMod p) :
    fourLatticePhase p (fourPrimeV m n) c (fourPrimeJ m n)=
      -c*((m : ZMod p)+(n : ZMod p))/((m : ZMod p)-(n : ZMod p)) := by
  have hd : fourDot (fourPrimeV m n) (fourPrimeJ m n)=0 := by
    simp [fourDot,fourPrimeJ,fourPrimeV]; ring
  simp only [fourLatticePhase,hd,Int.zero_ediv,Int.cast_zero,mul_zero,zero_add]
  simp [fourPrimeJ,fourPrimeV]
  ring

theorem fourPrime_phase_pair {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hvi : ((m-n : ℤ) : ZMod p) ≠ 0)
    (hj : fourPrimeJ m n ∈ fourProjectiveModule p (fourPrimeV m n))
    (c : ZMod p) (z : Fin 2 → ℤ) :
    fourLatticePhase p (fourPrimeV m n) c (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) z)=
      (z 0 : ZMod p)*(6+c)+(z 1 : ZMod p)*(-c*((m : ZMod p)+(n : ZMod p))/((m : ZMod p)-(n : ZMod p))) := by
  have hv := fourProjectiveModule_base p (fourPrimeV m n)
  have hd : (p : ℤ) ∣ fourVectorNorm (fourPrimeV m n) := by
    rw [fourPrime_long_norm,← hp]; exact dvd_mul_left _ _
  rw [fourPairVector,fourLatticePhase_add (Fact.out : p.Prime).ne_zero hd c _ _
    ((fourProjectiveModule p _).smul_mem _ hv) ((fourProjectiveModule p _).smul_mem _ hj),
    fourLatticePhase_smul (Fact.out : p.Prime).ne_zero hd c _ _ hv,
    fourLatticePhase_smul (Fact.out : p.Prime).ne_zero hd c _ _ hj,
    fourPrime_phase_v m n hp hvi,fourPrime_phase_j]

/-- Pure field algebra after the lattice and character exclusions. -/
theorem fourPrime_phase_blocks_residue {p : ℕ} [Fact p.Prime] (m n R : ℤ)
    (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0)
    (hm : (m : ZMod p) ≠ 0) (hn : (n : ZMod p) ≠ 0)
    (hd : (m : ZMod p)-(n : ZMod p) ≠ 0) (hs : (m : ZMod p)+(n : ZMod p) ≠ 0)
    (hpp : (m : ZMod p)*(m : ZMod p)+(n : ZMod p)*(n : ZMod p)=0)
    (a : Fin 6) (ha : a.val<4)
    (hv : ((fourPrimePlaneInvolution a 1 0) 0 : ZMod p)*(6+(2*(R : ZMod p)-3*m-n)/3)+
      ((fourPrimePlaneInvolution a 1 0) 1 : ZMod p)*
        (-(2*(R : ZMod p)-3*m-n)/3*((m : ZMod p)+n)/((m : ZMod p)-n))=
      6+(2*(R : ZMod p)-3*m-n)/3)
    (hj : ((fourPrimePlaneInvolution a 0 1) 0 : ZMod p)*(6+(2*(R : ZMod p)-3*m-n)/3)+
      ((fourPrimePlaneInvolution a 0 1) 1 : ZMod p)*
        (-(2*(R : ZMod p)-3*m-n)/3*((m : ZMod p)+n)/((m : ZMod p)-n))=
      -(2*(R : ZMod p)-3*m-n)/3*((m : ZMod p)+n)/((m : ZMod p)-n)) :
    ∃ b : Fin 4, (p : ℤ) ∣ fourReflectionResidue m n R b := by
  have residue_cast (b : Fin 4) :
      ((fourReflectionResidue m n R b : ℤ) : ZMod p)=fourReflectionResidue (m : ZMod p) (n : ZMod p) (R : ZMod p) b := by
    fin_cases b <;> simp [fourReflectionResidue]
  fin_cases a <;> norm_num at ha
  all_goals norm_num [fourPrimePlaneInvolution] at hv hj
  · refine ⟨0,(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    rw [residue_cast]
    dsimp [fourReflectionResidue]
    field_simp at hv
    apply (mul_eq_zero.mp (show (2 : ZMod p)*_=0 from ?_)).resolve_left h2
    linear_combination hv
  · refine ⟨1,(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    rw [residue_cast]
    dsimp [fourReflectionResidue]
    field_simp at hj
    apply (mul_eq_zero.mp (show (2 : ZMod p)*_=0 from ?_)).resolve_left h2
    linear_combination hj
  · refine ⟨2,(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    rw [residue_cast]
    dsimp [fourReflectionResidue]
    field_simp at hv
    apply (mul_eq_zero.mp (show (2*(2*(m : ZMod p)))*_=0 from ?_)).resolve_left (mul_ne_zero h2 (mul_ne_zero h2 hm))
    linear_combination -((m : ZMod p)-n)*hv+2*(3*(m : ZMod p)-9)*hpp
  · refine ⟨3,(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    rw [residue_cast]
    dsimp [fourReflectionResidue]
    field_simp at hv
    apply (mul_eq_zero.mp (show (2*(2*(n : ZMod p)))*_=0 from ?_)).resolve_left (mul_ne_zero h2 (mul_ne_zero h2 hn))
    linear_combination -((m : ZMod p)+n)*hv-2*(3*(n : ZMod p)+9)*hpp

end Ramanujan.MultiQuintuple
