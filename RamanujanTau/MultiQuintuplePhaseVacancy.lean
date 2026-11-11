import RamanujanTau.MultiQuintuplePhasePartners

/-!
# Opposite partners from a missing phase

Even-dimensional Watson products do not have the odd-dimensional twisted
antipodal law. A vacant phase bucket supplies the missing cyclotomic input.
The finite-field lemma explains why a nonzero projective norm shell has a
vacant phase. These are algebraic lemmas, not a four-factor converse theorem.
-/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators

/-- A nonzero norm cannot represent every phase over a finite field. -/
theorem exists_missing_projective_phase {F : Type*} [Field F] [Finite F]
    (D e : F) (he : e ≠ 0) :
    ∃ a : F, ∀ l : F, l*a-D*l^2 ≠ e := by
  classical
  let f : F → F := fun l => if l=0 then e+D else e/l+D*l
  have hf01 : f 0=f 1 := by simp [f]
  have hninj : ¬ Function.Injective f := by
    intro h
    exact zero_ne_one (h hf01)
  have hnsurj : ¬ Function.Surjective f := by
    intro h
    exact hninj ((Finite.injective_iff_surjective).mpr h)
  obtain ⟨a,ha⟩ := not_forall.mp hnsurj
  refine ⟨a,?_⟩
  intro l hl
  have hl0 : l ≠ 0 := by
    intro hz
    simp only [hz,zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at hl
    exact he hl.symm
  apply ha
  refine ⟨l,?_⟩
  simp only [f,if_neg hl0]
  apply (mul_left_cancel₀ hl0)
  field_simp
  linear_combination -hl

/-- One balanced opposite bucket suffices; no antipodal hypothesis is needed. -/
theorem opposite_phase_partner_of_balanced_bucket_sum_zero
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (rho : K)
    (hrho : rho^p = -1) (hprimitive : IsPrimitiveRoot (rho^2) p)
    (phase : I → ZMod (2*p)) (j0 : Fin p)
    (hbucket : shellPhaseMultiplicity phase (2*(j0.val : ZMod (2*p))) =
      shellPhaseMultiplicity phase (2*(j0.val : ZMod (2*p))+p))
    (hzero : (∑ i, rho^(phase i).val)=0) :
    ∀ i, ∃ j, phase j=phase i+p := by
  classical
  have hsum := (phase_sum_eq_opposite_buckets p hp.pos (hp.odd_of_ne_two hp2)
    rho hrho phase).symm.trans hzero
  have hfactor :
      (∑ j : Fin p,
        ((shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))) : K) -
          shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))+p)) *
            (rho^2)^j.val)=0 := by
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add,hrho,pow_mul]
    ring
  have hbalance := (prime_phase_sum_zero_iff_bucket_balance hp hprimitive
    (fun j => shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))))
    (fun j => shellPhaseMultiplicity phase (2*(j.val : ZMod (2*p))+p)) j0 hbucket).mp hfactor
  have hpadd : (p : ZMod (2*p))+(p : ZMod (2*p))=0 := by
    rw [← Nat.cast_add,← two_mul,ZMod.natCast_self]
  have hall : ∀ a : ZMod (2*p),
      shellPhaseMultiplicity phase a=shellPhaseMultiplicity phase (a+p) := by
    intro a
    obtain ⟨⟨b,j⟩,rfl⟩ := oppositePhaseParam_surjective p hp.pos (hp.odd_of_ne_two hp2) a
    cases b
    · simpa [oppositePhaseParam] using hbalance j
    · simpa [oppositePhaseParam,add_assoc,hpadd] using (hbalance j).symm
  intro i
  have hpos : 0 < shellPhaseMultiplicity phase (phase i) := by
    have hh : 0 < Fintype.card {j // phase j=phase i} :=
      Fintype.card_pos_iff.mpr ⟨⟨i,rfl⟩⟩
    simpa only [shellPhaseMultiplicity,Fintype.card_eq_nat_card] using hh
  rw [hall] at hpos
  have hne : Nonempty {j // phase j=phase i+p} := by
    apply Fintype.card_pos_iff.mp
    simpa only [shellPhaseMultiplicity,Fintype.card_eq_nat_card] using hpos
  obtain ⟨⟨j,hj⟩⟩ := hne
  exact ⟨j,hj⟩

/-- A nonzero projective norm forces the vacant bucket needed for even products. -/
theorem opposite_phase_partner_of_projective_norm
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (rho : K)
    (hrho : rho^p = -1) (hprimitive : IsPrimitiveRoot (rho^2) p)
    (phase : I → ZMod (2*p)) (scalar : I → ZMod p) (D e : ZMod p)
    (he : e ≠ 0)
    (hnorm : ∀ i, scalar i *
      (ZMod.castHom (dvd_mul_left p 2) (ZMod p) (phase i)) - D*(scalar i)^2=e)
    (hzero : (∑ i, rho^(phase i).val)=0) :
    ∀ i, ∃ j, phase j=phase i+p := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨a,ha⟩ := exists_missing_projective_phase D e he
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (fun h => hp2 (Nat.dvd_prime (by decide : Nat.Prime 2) |>.mp h |>.resolve_left hp.ne_one))
  let j0 : Fin p := ⟨(a/2).val,ZMod.val_lt _⟩
  have hj : (2*(j0.val : ZMod p))=a := by
    simp only [j0,ZMod.natCast_zmod_val]
    field_simp
  have hempty (b : ZMod (2*p))
      (hb : ZMod.castHom (dvd_mul_left p 2) (ZMod p) b=a) :
      shellPhaseMultiplicity phase b=0 := by
    letI : IsEmpty {i // phase i=b} := ⟨by
      rintro ⟨i,hi⟩
      apply ha (scalar i)
      simpa only [hi,hb] using hnorm i⟩
    simp [shellPhaseMultiplicity]
  apply opposite_phase_partner_of_balanced_bucket_sum_zero hp hp2 rho hrho hprimitive
    phase j0 _ hzero
  have h0 := hempty (2*(j0.val : ZMod (2*p))) (by
    simpa only [map_mul,map_ofNat,map_natCast] using hj)
  have h1 := hempty (2*(j0.val : ZMod (2*p))+p) (by
    simpa only [map_add,map_mul,map_ofNat,map_natCast,ZMod.natCast_self,add_zero] using hj)
  rw [h0,h1]

end Ramanujan.MultiQuintuple
