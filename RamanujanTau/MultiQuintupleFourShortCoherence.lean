import RamanujanTau.MultiQuintupleFourPhaseParity

/-! Short equal-norm phase partners preserve all mutual dot products in four
integer dimensions. Coherence is derived from arithmetic, not assumed. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourVectorNorm (x : Fin 4 → ℤ) : ℤ := fourDot x x

theorem fourVectorNorm_nonneg (x : Fin 4 → ℤ) : 0 ≤ fourVectorNorm x := by
  simp only [fourVectorNorm,fourDot]
  nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
    mul_self_nonneg (x 2),mul_self_nonneg (x 3)]

theorem fourVectorNorm_eq_zero_iff (x : Fin 4 → ℤ) : fourVectorNorm x=0 ↔ x=0 := by
  constructor
  · intro h
    funext i
    simp only [fourVectorNorm,fourDot] at h
    fin_cases i
    · change x 0=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 1=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 2=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 3=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
  · rintro rfl
    simp [fourVectorNorm,fourDot]

theorem fourVectorNorm_sub (x y : Fin 4 → ℤ) :
    fourVectorNorm (x-y)=fourVectorNorm x-2*fourDot x y+fourVectorNorm y := by
  simp [fourVectorNorm,fourDot]
  ring

theorem fourDot_bounds (x y : Fin 4 → ℤ) :
    -(fourVectorNorm x+fourVectorNorm y) ≤ 2*fourDot x y ∧
      2*fourDot x y ≤ fourVectorNorm x+fourVectorNorm y := by
  have hplus := fourVectorNorm_nonneg (x+y)
  have hminus := fourVectorNorm_nonneg (x-y)
  simp [fourVectorNorm,fourDot] at hplus hminus ⊢
  constructor <;> nlinarith

theorem four_short_dot_eq_of_square_dvd (p : ℤ) (x y x' y' : Fin 4 → ℤ)
    (hx : 2*fourVectorNorm x<p^2) (hy : 2*fourVectorNorm y<p^2)
    (hxn : fourVectorNorm x'=fourVectorNorm x)
    (hyn : fourVectorNorm y'=fourVectorNorm y)
    (hd : p^2 ∣ fourDot x' y'-fourDot x y) : fourDot x' y'=fourDot x y := by
  obtain ⟨hlo,hhi⟩ := fourDot_bounds x y
  obtain ⟨hlo',hhi'⟩ := fourDot_bounds x' y'
  rw [hxn,hyn] at hlo' hhi'
  have habs : |fourDot x' y'-fourDot x y|<p^2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hcast : ((fourDot x' y'-fourDot x y).natAbs : ℤ)<((p^2).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs,abs_of_nonneg (sq_nonneg p)] using habs
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by exact_mod_cast hcast))

theorem four_short_translate_unique (p : ℤ) (x y z : Fin 4 → ℤ)
    (hp : 0<p) (hpodd : Odd p) (hpoint : x=y+p • z)
    (hnorm : fourVectorNorm x=fourVectorNorm y)
    (hshort : 2*fourVectorNorm y<p^2) : x=y := by
  have hmul : p*(2*fourDot y z+p*fourVectorNorm z)=0 := by
    rw [hpoint] at hnorm
    simp only [fourVectorNorm,fourDot,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hnorm ⊢
    linear_combination hnorm
  have hpair : 2*fourDot y z+p*fourVectorNorm z=0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
  obtain ⟨k,hk⟩ := hpodd
  have heven : fourVectorNorm z=2*(-fourDot y z-k*fourVectorNorm z) := by
    linear_combination hpair-fourVectorNorm z*hk
  have hsum := fourVectorNorm_nonneg ((2 : ℤ) • y+p • z)
  have he : fourVectorNorm ((2 : ℤ) • y+p • z)=
      4*fourVectorNorm y+4*p*fourDot y z+p^2*fourVectorNorm z := by
    simp [fourVectorNorm,fourDot]
    ring
  rw [he] at hsum
  have hpair' : 2*p*fourDot y z+p^2*fourVectorNorm z=0 := by
    linear_combination p*hpair
  have hupper : p^2*fourVectorNorm z<p^2*2 := by nlinarith
  have hnlt : fourVectorNorm z<2 :=
    (mul_lt_mul_iff_right₀ (sq_pos_of_pos hp)).mp (by simpa [mul_comm] using hupper)
  have hnnonneg := fourVectorNorm_nonneg z
  have hz : z=0 := (fourVectorNorm_eq_zero_iff z).mp (by omega)
  simpa [hz] using hpoint

structure FourProjectiveLift (p : ℕ) (v : Fin 4 → ℤ) where
  point : Fin 4 → ℤ
  scalar : ℤ
  remainder : Fin 4 → ℤ
  point_eq : point=scalar • v+(p : ℤ) • remainder

namespace FourProjectiveLift
variable {p : ℕ} {v : Fin 4 → ℤ}

def pairing (x : FourProjectiveLift p v) : ℤ := fourDot v x.point/p

theorem dot_base (x : FourProjectiveLift p v) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) :
    fourDot v x.point=(p : ℤ)*(x.scalar*H+fourDot v x.remainder) := by
  rw [x.point_eq]
  simp [fourDot,fourVectorNorm] at hv ⊢
  linear_combination x.scalar*hv

theorem pairing_eq (x : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) :
    x.pairing=x.scalar*H+fourDot v x.remainder := by
  rw [pairing,x.dot_base H hv]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp)

theorem dot_identity (x y : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) :
    fourDot x.point y.point=(p : ℤ)*(x.scalar*y.pairing+y.scalar*x.pairing-
      H*x.scalar*y.scalar)+(p : ℤ)^2*fourDot x.remainder y.remainder := by
  rw [x.point_eq,y.point_eq,x.pairing_eq hp H hv,y.pairing_eq hp H hv]
  simp [fourDot,fourVectorNorm] at hv ⊢
  linear_combination x.scalar*y.scalar*hv

theorem dot_quotient_eq (x y : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) :
    fourDot x.point y.point/p=x.scalar*y.pairing+y.scalar*x.pairing-H*x.scalar*y.scalar+
      (p : ℤ)*fourDot x.remainder y.remainder := by
  have he : fourDot x.point y.point=(p : ℤ)*(x.scalar*y.pairing+y.scalar*x.pairing-
      H*x.scalar*y.scalar+(p : ℤ)*fourDot x.remainder y.remainder) := by
    rw [x.dot_identity y hp H hv]
    ring
  rw [he]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp)

theorem dot_dvd (x y : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) : (p : ℤ) ∣ fourDot x.point y.point := by
  refine ⟨x.scalar*y.pairing+y.scalar*x.pairing-H*x.scalar*y.scalar+
    (p : ℤ)*fourDot x.remainder y.remainder,?_⟩
  rw [x.dot_identity y hp H hv]
  ring

def phase (x : FourProjectiveLift p v) (c : ZMod p) : ZMod p :=
  2*(x.pairing : ZMod p)+c*x.scalar

theorem norm_phase (x : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p) :
    ((fourVectorNorm x.point/p : ℤ) : ZMod p)=
      (x.scalar : ZMod p)*x.phase c-((H : ZMod p)+c)*(x.scalar : ZMod p)^2 := by
  rw [fourVectorNorm,x.dot_quotient_eq x hp H hv]
  push_cast
  simp only [ZMod.natCast_self,zero_mul,add_zero,phase]
  ring

theorem dot_phase (x y : FourProjectiveLift p v) (hp : p ≠ 0) (H : ℤ)
    (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p) :
    2*((fourDot x.point y.point/p : ℤ) : ZMod p)=
      (x.scalar : ZMod p)*y.phase c+(y.scalar : ZMod p)*x.phase c-
        2*((H : ZMod p)+c)*(x.scalar : ZMod p)*(y.scalar : ZMod p) := by
  rw [x.dot_quotient_eq y hp H hv]
  push_cast
  simp only [ZMod.natCast_self,zero_mul,add_zero,phase]
  ring

theorem short_eq_of_scalar_eq (x y : FourProjectiveLift p v) (hp : 0<p)
    (hpodd : Odd (p : ℤ)) (hnorm : fourVectorNorm x.point=fourVectorNorm y.point)
    (hshort : 2*fourVectorNorm y.point<(p : ℤ)^2)
    (hscalar : (x.scalar : ZMod p)=(y.scalar : ZMod p)) : x.point=y.point := by
  have hd : (p : ℤ) ∣ x.scalar-y.scalar :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [hscalar]; ring)
  obtain ⟨t,ht⟩ := hd
  have hs : x.scalar=y.scalar+(p : ℤ)*t := by omega
  let z := t • v+x.remainder-y.remainder
  have hpoint : x.point=y.point+(p : ℤ) • z := by
    rw [x.point_eq,y.point_eq,hs]
    dsimp [z]
    module
  exact four_short_translate_unique p x.point y.point z (by exact_mod_cast hp)
    hpodd hpoint hnorm hshort

theorem short_partner_reflection [Fact p.Prime] (x y : FourProjectiveLift p v)
    (hpodd : Odd (p : ℤ)) (H : ℤ) (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p)
    (hnorm : fourVectorNorm y.point=fourVectorNorm x.point)
    (hshort : 2*fourVectorNorm x.point<(p : ℤ)^2) (hne : y.point ≠ x.point)
    (hphase : y.phase c=x.phase c) :
    ((H : ZMod p)+c)*((x.scalar : ZMod p)+y.scalar)=x.phase c := by
  have hp : p.Prime := Fact.out
  have hquad : (x.scalar : ZMod p)*x.phase c-((H : ZMod p)+c)*(x.scalar : ZMod p)^2=
      (y.scalar : ZMod p)*x.phase c-((H : ZMod p)+c)*(y.scalar : ZMod p)^2 := by
    rw [← x.norm_phase hp.ne_zero H hv c,← hphase,← y.norm_phase hp.ne_zero H hv c,hnorm]
  rcases phase_norm_identity_or_reflection _ _ _ _ hquad with heq | hreflect
  · exact False.elim (hne (y.short_eq_of_scalar_eq x hp.pos hpodd hnorm hshort heq.symm))
  · exact hreflect

theorem short_partners_preserve_dot [Fact p.Prime] (x y x' y' : FourProjectiveLift p v)
    (hpodd : Odd (p : ℤ)) (H : ℤ) (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p)
    (hxn : fourVectorNorm x'.point=fourVectorNorm x.point)
    (hyn : fourVectorNorm y'.point=fourVectorNorm y.point)
    (hx : 2*fourVectorNorm x.point<(p : ℤ)^2)
    (hy : 2*fourVectorNorm y.point<(p : ℤ)^2)
    (hxne : x'.point ≠ x.point) (hyne : y'.point ≠ y.point)
    (hxp : x'.phase c=x.phase c) (hyp : y'.phase c=y.phase c) :
    fourDot x'.point y'.point=fourDot x.point y.point := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by intro heq; subst p; norm_num [Odd] at hpodd
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr (by
      intro hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with hh | hh
      · exact hp.ne_one hh
      · exact hp2 hh)
  have hrx := x.short_partner_reflection x' hpodd H hv c hxn hx hxne hxp
  have hry := y.short_partner_reflection y' hpodd H hv c hyn hy hyne hyp
  have hbil := phase_reflection_preserves_polarization ((H : ZMod p)+c)
    (x.phase c) (y.phase c) (x.scalar : ZMod p) (y.scalar : ZMod p)
    (x'.scalar : ZMod p) (y'.scalar : ZMod p) hrx hry
  have hquot : ((fourDot x'.point y'.point/p : ℤ) : ZMod p)=
      ((fourDot x.point y.point/p : ℤ) : ZMod p) := by
    apply mul_left_cancel₀ h2
    rw [x'.dot_phase y' hp.ne_zero H hv c,x.dot_phase y hp.ne_zero H hv c,hxp,hyp]
    exact hbil
  have hd : (p : ℤ) ∣ fourDot x'.point y'.point/p-fourDot x.point y.point/p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [hquot]; ring)
  obtain ⟨a,ha⟩ := hd
  have hmul := Int.ediv_mul_cancel (x.dot_dvd y hp.ne_zero H hv)
  have hmul' := Int.ediv_mul_cancel (x'.dot_dvd y' hp.ne_zero H hv)
  apply four_short_dot_eq_of_square_dvd p x.point y.point x'.point y'.point hx hy hxn hyn
  refine ⟨a,?_⟩
  linear_combination (p : ℤ)*ha-hmul'+hmul

theorem short_partner_unique [Fact p.Prime] (x y z : FourProjectiveLift p v)
    (hpodd : Odd (p : ℤ)) (H : ℤ) (hv : fourVectorNorm v=(p : ℤ)*H) (c : ZMod p)
    (hyn : fourVectorNorm y.point=fourVectorNorm x.point)
    (hzn : fourVectorNorm z.point=fourVectorNorm x.point)
    (hx : 2*fourVectorNorm x.point<(p : ℤ)^2)
    (hyne : y.point ≠ x.point) (hzne : z.point ≠ x.point)
    (hyp : y.phase c=x.phase c) (hzp : z.phase c=x.phase c) : y.point=z.point := by
  have hdot := x.short_partners_preserve_dot x y z hpodd H hv c hyn hzn hx hx hyne hzne hyp hzp
  apply sub_eq_zero.mp
  apply (fourVectorNorm_eq_zero_iff _).mp
  rw [fourVectorNorm_sub,hyn,hzn,hdot]
  simp only [fourVectorNorm]
  ring

end FourProjectiveLift

def fourFourierLift (p : ℕ) (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) :
    FourProjectiveLift p v where
  point := fourDualPoint p v x
  scalar := -3*(x.1.val : ℤ)
  remainder := x.2
  point_eq := by
    funext i
    simp [fourDualPoint]
    ring

theorem fourFourierLift_norm (p : ℕ) (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) :
    fourVectorNorm (fourFourierLift p v x).point=fourDualNorm p v x := by
  simp [fourVectorNorm,fourDot,fourDualNorm,fourFourierLift,Fin.sum_univ_succ]
  ring

theorem fourFourierLift_phase {p : ℕ} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0)
    (v : Fin 4 → ℤ) (R : ℤ) (x : ZMod p × (Fin 4 → ℤ))
    (hx : fourCubicCharacter x.2 ≠ 0) :
    (fourFourierLift p v x).phase (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3)=
      ZMod.castHom (dvd_mul_left p 2) (ZMod p) (fourCanonicalPhase p v R x) := by
  rw [fourCanonicalPhase,map_intCast,
    four_compressed_phase_mod_prime h3 v R x _ (fourCanonicalSigns_spec x.2 hx)]
  simp only [FourProjectiveLift.phase,FourProjectiveLift.pairing,fourFourierLift]
  have he : fourDot v (fourDualPoint p v x)=∑ i, v i*fourDualPoint p v x i := by
    simp [fourDot,Fin.sum_univ_succ]
    ring
  rw [he]
  push_cast
  simp only [ZMod.natCast_zmod_val]

/-- The canonical phases obtained from actual Fourier amplitudes satisfy the
arithmetic coherence theorem; they are not arbitrary phase assignments. -/
theorem four_short_canonical_partners_preserve_dot {p : ℕ} [Fact p.Prime]
    (hpodd : Odd (p : ℤ)) (h3 : (3 : ZMod p) ≠ 0) (v : Fin 4 → ℤ)
    (hvi : (v 0 : ZMod p) ≠ 0) (R H : ℤ) (hv : (∑ i, v i*v i)=(p : ℤ)*H)
    (x y x' y' : ZMod p × (Fin 4 → ℤ))
    (hsx : fourCubicCharacter x.2 ≠ 0) (hsy : fourCubicCharacter y.2 ≠ 0)
    (hsx' : fourCubicCharacter x'.2 ≠ 0) (hsy' : fourCubicCharacter y'.2 ≠ 0)
    (hxn : fourDualNorm p v x'=fourDualNorm p v x)
    (hyn : fourDualNorm p v y'=fourDualNorm p v y)
    (hx : 2*fourDualNorm p v x<(p : ℤ)^2) (hy : 2*fourDualNorm p v y<(p : ℤ)^2)
    (hxp : fourCanonicalPhase p v R x'=fourCanonicalPhase p v R x+p)
    (hyp : fourCanonicalPhase p v R y'=fourCanonicalPhase p v R y+p) :
    fourDot (fourDualPoint p v x') (fourDualPoint p v y')=
      fourDot (fourDualPoint p v x) (fourDualPoint p v y) := by
  have hp : p.Prime := Fact.out
  have hpnonzero : (p : ZMod (2*p)) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff p (2*p)).not.mpr
      (Nat.not_dvd_of_pos_of_lt hp.pos (by have := hp.pos; omega))
  have hdistinct (a b : ZMod p × (Fin 4 → ℤ))
      (hphase : fourCanonicalPhase p v R b=fourCanonicalPhase p v R a+p) :
      (fourFourierLift p v b).point ≠ (fourFourierLift p v a).point := by
    intro he
    have hab := fourDualPoint_injective v h3 hvi he
    subst b
    exact hpnonzero (by linear_combination -hphase)
  have hpres (a b : ZMod p × (Fin 4 → ℤ))
      (ha : fourCubicCharacter a.2 ≠ 0) (hb : fourCubicCharacter b.2 ≠ 0)
      (hphase : fourCanonicalPhase p v R b=fourCanonicalPhase p v R a+p) :
      (fourFourierLift p v b).phase (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3)=
        (fourFourierLift p v a).phase (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3) := by
    rw [fourFourierLift_phase h3 v R a ha,fourFourierLift_phase h3 v R b hb]
    have he := congrArg (ZMod.castHom (dvd_mul_left p 2) (ZMod p)) hphase
    simpa only [map_add,map_natCast,ZMod.natCast_self,add_zero] using he
  have hv' : fourVectorNorm v=(p : ℤ)*H := by
    convert hv using 1
    simp [fourVectorNorm,fourDot,Fin.sum_univ_succ]
    ring
  exact (fourFourierLift p v x).short_partners_preserve_dot
    (fourFourierLift p v y) (fourFourierLift p v x') (fourFourierLift p v y') hpodd H hv' _
    (by simpa only [fourFourierLift_norm] using hxn)
    (by simpa only [fourFourierLift_norm] using hyn)
    (by simpa only [fourFourierLift_norm] using hx)
    (by simpa only [fourFourierLift_norm] using hy)
    (hdistinct x x' hxp) (hdistinct y y' hyp)
    (hpres x x' hsx hsx' hxp) (hpres y y' hsy hsy' hyp)

end Ramanujan.MultiQuintuple
