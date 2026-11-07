import RamanujanTau.MultiQuintupleFourFamilyData

/-! Four persistent zero progressions in an explicit infinite four-factor family. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 10000
set_option maxHeartbeats 0

lemma fourFamilyP_pos (t : ℕ) : 0 < fourFamilyP t := by
  dsimp [fourFamilyP]; positivity

lemma fourFamily_branch_constant (t : ℕ) (r : Fin 4) (b1 b2 b3 b4 : Bool) :
    fourFamilyBitSum t b1 b2 b3 b4+12*fourFamilyC0 t r b1 b2 b3 b4 =
      fourFamilyR t r+fourFamilyP t*fourFamilyQ0 t r b1 b2 b3 b4 := by
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [fourFamilyBitSum,fourFamilyI1,fourFamilyI2,fourFamilyI3,
      fourFamilyP,fourFamilyR,fourFamilyC0,fourFamilyQ0,
      fourFamilyC0_0,fourFamilyC0_1,fourFamilyC0_2,fourFamilyC0_3,
      fourFamilyQ0_0,fourFamilyQ0_1,fourFamilyQ0_2,fourFamilyQ0_3] <;> ring

lemma fourFamily_fiber_representation (t : ℕ) (r : Fin 4) (x : QuadQuintBranchIndex) (q : ℤ)
    (hres : quadResidue (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4 x =
      fourFamilyR t r+fourFamilyP t*q) :
    x = fourFamilyFiberPoint t r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
      (quadN1 x) (quadN2 x) (quadN3 x) (fourFamilyFiberZ t r x) := by
  let d := quadN4 x-fourFamilyA1 t*quadN1 x-fourFamilyA2 t*quadN2 x-
    fourFamilyA3 t*quadN3 x-fourFamilyC0 t r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
  let a := q-fourFamilyQ0 t r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)-
    3*quadN1 x-3*quadN2 x-3*quadN3 x
  have he : 12*d=fourFamilyP t*a := by
    have hc := fourFamily_branch_constant t r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)
    dsimp [quadResidue,fourFamilyBitSum,fourFamilyI1,fourFamilyI2,fourFamilyI3,
      fourFamilyA1,fourFamilyA2,fourFamilyA3,fourFamilyP,d,a] at hres hc ⊢
    push_cast at hres hc ⊢
    linear_combination hres-hc
  have hbezout : (12 : ℤ)*fourFamilyInv12 t-7*fourFamilyP t=1 := by
    norm_num [fourFamilyInv12,fourFamilyP]; ring
  have hd : (fourFamilyP t : ℤ) ∣ d := by
    refine ⟨fourFamilyInv12 t*a-7*d,?_⟩
    linear_combination (fourFamilyInv12 t : ℤ)*he-d*hbezout
  obtain ⟨z,hz⟩ := hd
  have hp : (fourFamilyP t : ℤ) ≠ 0 := by exact_mod_cast (fourFamilyP_pos t).ne'
  have hq : fourFamilyFiberZ t r x=z := by
    change d/(fourFamilyP t : ℤ)=z
    rw [hz]
    exact Int.mul_ediv_cancel_left z hp
  have hlast : quadN4 x=fourFamilyA1 t*quadN1 x+fourFamilyA2 t*quadN2 x+
      fourFamilyA3 t*quadN3 x+fourFamilyC0 t r (quadB1 x) (quadB2 x) (quadB3 x) (quadB4 x)+
      fourFamilyP t*fourFamilyFiberZ t r x := by
    rw [hq]; dsimp [d] at hz; linarith
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simpa [fourFamilyFiberPoint,quadB1,quadB2,quadB3,quadB4,quadN1,quadN2,quadN3,quadN4,
    pointB1,pointB2,pointB3,pointN1,pointN2,pointN3] using hlast

@[simp] lemma fourFamilyFiberZ_fiberPoint (t : ℕ) (r : Fin 4)
    (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    fourFamilyFiberZ t r (fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z)=z := by
  have hp : (fourFamilyP t : ℤ) ≠ 0 := by exact_mod_cast (fourFamilyP_pos t).ne'
  simp only [fourFamilyFiberZ,fourFamilyFiberPoint,quadB1,quadB2,quadB3,quadB4,
    quadN1,quadN2,quadN3,quadN4,pointB1,pointB2,pointB3,pointN1,pointN2,pointN3]
  convert Int.mul_ediv_cancel_left z hp using 1 <;> congr 1 <;> ring

@[simp] lemma fourFamilyPartner_fiberPoint (t : ℕ) (r : Fin 4)
    (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    fourFamilyPartner t r (fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z)=
      fourFamilyPartnerFiber t r b1 b2 b3 b4 n1 n2 n3 z := by
  unfold fourFamilyPartner
  rw [fourFamilyFiberZ_fiberPoint]
  rfl

lemma fourFamilyPartner_weight (t : ℕ) (r : Fin 4) (x : QuadQuintBranchIndex) :
    quadWeight (fourFamilyPartner t r x) = -quadWeight x := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [fourFamilyPartner,fourFamilyPartnerFiber,fourFamilyPartnerFiber_0,
      fourFamilyPartnerFiber_1,fourFamilyPartnerFiber_2,fourFamilyPartnerFiber_3,
      fourFamilyFiberPoint,quadWeight,pointBranchWeight,branchSign,
      quadB1,quadB2,quadB3,quadB4,pointB1,pointB2,pointB3]

lemma fourFamilyPartner_exponent (t : ℕ) (r : Fin 4)
    (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    quadExp2 (fourFamilyP t) (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4
      (fourFamilyPartner t r (fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z)) =
    quadExp2 (fourFamilyP t) (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4
      (fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z) := by
  rw [fourFamilyPartner_fiberPoint]
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    norm_num [fourFamilyPartnerFiber,fourFamilyPartnerFiber_0,fourFamilyPartnerFiber_1,
      fourFamilyPartnerFiber_2,fourFamilyPartnerFiber_3,fourFamilyFiberPoint,
      fourFamilyC0,fourFamilyC0_0,fourFamilyC0_1,fourFamilyC0_2,fourFamilyC0_3,
      fourFamilyA1,fourFamilyA2,fourFamilyA3,fourFamilyP,fourFamilyI1,fourFamilyI2,fourFamilyI3,
      quadExp2,pointTripleExp2,tripleQuintExp2,quintExp2,quintExpA2,quintExpB2,
      quadB4,quadN4,pointB1,pointB2,pointB3,pointN1,pointN2,pointN3] <;> ring

lemma fourFamilyPartner_involutive (t : ℕ) (r : Fin 4)
    (b1 b2 b3 b4 : Bool) (n1 n2 n3 z : ℤ) :
    fourFamilyPartner t r (fourFamilyPartner t r (fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z))=
      fourFamilyFiberPoint t r b1 b2 b3 b4 n1 n2 n3 z := by
  fin_cases r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    simp [fourFamilyPartnerFiber,fourFamilyPartnerFiber_0,fourFamilyPartnerFiber_1,
      fourFamilyPartnerFiber_2,fourFamilyPartnerFiber_3] <;>
    simp [fourFamilyFiberPoint] <;> ring_nf <;> try simp

lemma fourFamily_target_has_residue (t : ℕ) (r : Fin 4) (N : ℕ) (x : QuadQuintBranchIndex)
    (hexp : quadExp2 (fourFamilyP t) (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4 x=
      2*((fourFamilyP t*N+fourFamilyR t r : ℕ):ℤ)) :
    ∃ q : ℤ, quadResidue (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4 x =
      fourFamilyR t r+fourFamilyP t*q := by
  obtain ⟨u,hu⟩ := quadExp2_residue (fourFamilyP t) (fourFamilyI1 t) (fourFamilyI2 t) (fourFamilyI3 t) 4 x
  have hueven : Even u := by
    have hc := congrArg (fun z : ℤ => (z : ZMod 2)) (hexp.symm.trans hu)
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hp : (fourFamilyP t : ZMod 2) = 1 := by
      have hA : (5184 : ZMod 2)=0 := by decide
      have hB : (720 : ZMod 2)=0 := by decide
      have hC : (41 : ZMod 2)=1 := by decide
      simp only [fourFamilyP,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
        hA,hB,hC,zero_mul,zero_add]
    have hz : (u : ZMod 2)=0 := by
      push_cast at hc
      simpa only [htwo,hp,zero_mul,zero_add,one_mul] using hc.symm
    exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp hz)
  obtain ⟨w,hw⟩ := hueven
  refine ⟨(N : ℤ)-w,?_⟩
  rw [hw] at hu
  push_cast at hexp
  nlinarith

/-- Four infinite zero progressions, for every parameter and every progression index.
No primality assumption is required. -/
theorem coeff_four_family_zero (t N : ℕ) (r : Fin 4) :
    coeff (fourFamilyP t*N+fourFamilyR t r)
      (quintupleSpecialized (fourFamilyP t) (fourFamilyI1 t) *
       quintupleSpecialized (fourFamilyP t) (fourFamilyI2 t) *
       quintupleSpecialized (fourFamilyP t) (fourFamilyI3 t) *
       quintupleSpecialized (fourFamilyP t) 4)=0 := by
  apply coeff_quad_eq_zero_of_expInvolution (fourFamilyP t) (fourFamilyI1 t)
    (fourFamilyI2 t) (fourFamilyI3 t) 4 (fourFamilyP t*N+fourFamilyR t r) (fourFamilyPartner t r)
    (by dsimp [fourFamilyI1]; omega) (by dsimp [fourFamilyP,fourFamilyI1]; nlinarith)
    (by dsimp [fourFamilyI2]; omega) (by dsimp [fourFamilyP,fourFamilyI2]; nlinarith)
    (by dsimp [fourFamilyI3]; omega) (by dsimp [fourFamilyP,fourFamilyI3]; nlinarith)
    (by norm_num) (by dsimp [fourFamilyP]; nlinarith)
  · intro x _; exact fourFamilyPartner_weight t r x
  · intro x hx
    obtain ⟨q,hq⟩ := fourFamily_target_has_residue t r N x hx
    rw [fourFamily_fiber_representation t r x q hq]
    exact fourFamilyPartner_exponent _ _ _ _ _ _ _ _ _ _
  · intro x hx
    obtain ⟨q,hq⟩ := fourFamily_target_has_residue t r N x hx
    rw [fourFamily_fiber_representation t r x q hq]
    exact fourFamilyPartner_involutive _ _ _ _ _ _ _ _ _ _

/-- The modulus increases strictly, so the parameter supplies infinitely many distinct moduli. -/
theorem fourFamilyP_strictMono : StrictMono fourFamilyP := by
  intro a b hab
  unfold fourFamilyP
  gcongr

/-- All four formulas are canonical residues. -/
theorem fourFamilyR_lt (t : ℕ) (r : Fin 4) : fourFamilyR t r < fourFamilyP t := by
  fin_cases r <;> norm_num [fourFamilyR,fourFamilyP] <;> nlinarith

/-- The four formulas give distinct progressions at every parameter. -/
theorem fourFamilyR_injective (t : ℕ) : Function.Injective (fourFamilyR t) := by
  intro r s h
  fin_cases r <;> fin_cases s <;> first | rfl | (cases t <;> norm_num [fourFamilyR] at h <;> nlinarith)

end Ramanujan.MultiQuintuple
