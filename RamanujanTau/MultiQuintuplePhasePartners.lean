/-
# Actual finite phase sums force opposite partners
-/
import RamanujanTau.MultiQuintuplePhasePairing

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

def oppositePhaseParam (p : ℕ) (x : Bool × Fin p) : ZMod (2*p) :=
  ((2*x.2.val+(if x.1 then p else 0) : ℕ) : ZMod (2*p))

theorem oppositePhaseParam_surjective (p : ℕ) (hp : 0 < p) (hodd : Odd p) :
    Function.Surjective (oppositePhaseParam p) := by
  letI : NeZero (2*p) := ⟨by omega⟩
  intro a
  obtain ⟨m,hm⟩ := hodd
  have hb := ZMod.val_lt a
  have hmod : a.val%2=0 ∨ a.val%2=1 := by omega
  rcases hmod with he | he
  · have hn : 2*(a.val/2)=a.val := by omega
    refine ⟨(false,⟨a.val/2,by omega⟩),?_⟩
    simp only [oppositePhaseParam,Bool.false_eq_true,if_false,add_zero,hn]
    exact ZMod.natCast_zmod_val a
  · by_cases hpa : p ≤ a.val
    · have hn : 2*((a.val-p)/2)+p=a.val := by omega
      refine ⟨(true,⟨(a.val-p)/2,by omega⟩),?_⟩
      simp only [oppositePhaseParam,if_true,hn]
      exact ZMod.natCast_zmod_val a
    · have hn : 2*((a.val+p)/2)+p=a.val+2*p := by omega
      refine ⟨(true,⟨(a.val+p)/2,by omega⟩),?_⟩
      simp only [oppositePhaseParam,if_true,hn,Nat.cast_add,ZMod.natCast_self,add_zero]
      exact ZMod.natCast_zmod_val a

noncomputable def oppositePhaseEquiv (p : ℕ) (hp : 0 < p) (hodd : Odd p) :
    Bool × Fin p ≃ ZMod (2*p) := by
  letI : NeZero (2*p) := ⟨by omega⟩
  exact Equiv.ofBijective (oppositePhaseParam p)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨oppositePhaseParam_surjective p hp hodd,by simp⟩)

theorem oppositePhaseParam_power {K : Type*} [Field K] {p : ℕ} (hp : 0 < p)
    (rho : K) (hrho : rho^p = -1) (b : Bool) (j : Fin p) :
    rho^(oppositePhaseParam p (b,j)).val = rho^(2*j.val+(if b then p else 0)) := by
  letI : NeZero (2*p) := ⟨by omega⟩
  have hperiod : rho^(2*p)=1 := by rw [mul_comm 2 p,pow_mul,hrho]; ring
  rw [oppositePhaseParam,ZMod.val_natCast]
  exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hperiod

theorem phase_sum_eq_opposite_buckets {K I : Type*} [Field K] [CharZero K] [Fintype I]
    (p : ℕ) (hp : 0 < p) (hodd : Odd p) (rho : K) (hrho : rho^p = -1)
    (phase : I → ZMod (2*p)) :
    (∑ i, rho^(phase i).val) = ∑ j : Fin p,
      ((shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))) : K)*rho^(2*j.val)+
      (shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))+p) : K)*rho^(2*j.val+p)) := by
  classical
  letI : NeZero (2*p) := ⟨by omega⟩
  let m := shellPhaseMultiplicity phase
  have hgroup : (∑ a : ZMod (2*p), (m a : K)*rho^a.val) = ∑ i, rho^(phase i).val := by
    simpa only [m,shellPhaseMultiplicity,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card] using
      (Fintype.sum_fiberwise' phase (fun a => rho^a.val))
  rw [← hgroup,← (oppositePhaseEquiv p hp hodd).sum_comp]
  change (∑ x : Bool × Fin p, (m (oppositePhaseParam p x) : K)*rho^(oppositePhaseParam p x).val) = _
  rw [Fintype.sum_prod_type]
  simp_rw [oppositePhaseParam_power hp rho hrho]
  simp [oppositePhaseParam,Finset.sum_add_distrib,m,add_comm]

/-- Cancellation of the actual root powers, together with the antipodal
law, gives an opposite-phase partner for every member of a finite shell. -/
theorem opposite_phase_partner_of_antipodal_sum_zero
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (rho : K)
    (hrho : rho^p = -1) (hprimitive : IsPrimitiveRoot (rho^2) p)
    (phase : I → ZMod (2*p)) (antipode : I ≃ I)
    (hanti : ∀ i, phase (antipode i)=(p : ZMod (2*p))-phase i)
    (hzero : (∑ i, rho^(phase i).val)=0) :
    ∀ i, ∃ j, phase j=phase i+p := by
  classical
  have hsum := (phase_sum_eq_opposite_buckets p hp.pos (hp.odd_of_ne_two hp2) rho hrho phase).symm.trans hzero
  have hbalance := (antipodal_shell_amplitude_zero_iff_pair_balance hp hrho hprimitive phase antipode hanti).mp hsum
  have hpadd : (p : ZMod (2*p))+(p : ZMod (2*p))=0 := by
    rw [← Nat.cast_add,← two_mul,ZMod.natCast_self]
  have hall : ∀ a : ZMod (2*p), shellPhaseMultiplicity phase a=shellPhaseMultiplicity phase (a+p) := by
    intro a
    obtain ⟨⟨b,j⟩,rfl⟩ := oppositePhaseParam_surjective p hp.pos (hp.odd_of_ne_two hp2) a
    cases b
    · simpa [oppositePhaseParam] using hbalance j
    · simpa [oppositePhaseParam,add_assoc,hpadd] using (hbalance j).symm
  intro i
  have hpos : 0 < shellPhaseMultiplicity phase (phase i) := by
    have hh : 0 < Fintype.card {j // phase j=phase i} := Fintype.card_pos_iff.mpr ⟨⟨i,rfl⟩⟩
    simpa only [shellPhaseMultiplicity,Fintype.card_eq_nat_card] using hh
  rw [hall] at hpos
  have hne : Nonempty {j // phase j=phase i+p} := by
    apply Fintype.card_pos_iff.mp
    simpa only [shellPhaseMultiplicity,Fintype.card_eq_nat_card] using hpos
  obtain ⟨⟨j,hj⟩⟩ := hne
  exact ⟨j,hj⟩

end Ramanujan.MultiQuintuple
