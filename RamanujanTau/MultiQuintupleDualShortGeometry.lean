/-
# Short-vector arithmetic on the integral Poisson-dual lattice

This file connects the phase-reflection identities to actual integral
projective lifts.  Equal phases and equal short norms force equality of
mutual dot products, without assuming a common linear map.
-/
import RamanujanTau.MultiQuintupleShortCoherence
import RamanujanTau.MultiQuintupleThetaArithmetic

namespace Ramanujan.MultiQuintuple

def ternaryIntNorm (x : TernaryIntPoint) : ℤ :=
  ternaryNorm x.1.1 x.1.2 x.2

def ternaryIntDot (x y : TernaryIntPoint) : ℤ :=
  ternaryDot x.1.1 x.1.2 x.2 y.1.1 y.1.2 y.2

@[simp] theorem ternaryIntDot_self (x : TernaryIntPoint) :
    ternaryIntDot x x = ternaryIntNorm x := by
  simp [ternaryIntDot, ternaryIntNorm, ternaryDot, ternaryNorm, pow_two]

theorem ternaryIntNorm_nonneg (x : TernaryIntPoint) : 0 ≤ ternaryIntNorm x :=
  add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem ternaryIntNorm_eq_zero_iff (x : TernaryIntPoint) :
    ternaryIntNorm x = 0 ↔ x = 0 := by
  rcases x with ⟨⟨a,b⟩,c⟩
  constructor
  · intro h
    simp only [ternaryIntNorm, ternaryNorm] at h
    have ha : a = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha, hb, hc]
  · intro h
    rw [h]
    norm_num [ternaryIntNorm, ternaryNorm]

theorem ternaryIntDot_bounds (x y : TernaryIntPoint) :
    -(ternaryIntNorm x + ternaryIntNorm y) ≤ 2*ternaryIntDot x y ∧
      2*ternaryIntDot x y ≤ ternaryIntNorm x + ternaryIntNorm y := by
  have hplus := ternaryIntNorm_nonneg (x+y)
  have hminus := ternaryIntNorm_nonneg (x-y)
  rcases x with ⟨⟨a,b⟩,c⟩
  rcases y with ⟨⟨d,e⟩,f⟩
  simp [ternaryIntNorm, ternaryNorm, ternaryIntDot, ternaryDot] at hplus hminus ⊢
  constructor <;> nlinarith

theorem ternaryIntNorm_sub (x y : TernaryIntPoint) :
    ternaryIntNorm (x-y) = ternaryIntNorm x-2*ternaryIntDot x y+ternaryIntNorm y := by
  rcases x with ⟨⟨a,b⟩,c⟩
  rcases y with ⟨⟨d,e⟩,f⟩
  simp [ternaryIntNorm, ternaryNorm, ternaryIntDot, ternaryDot]
  ring

/-- The strict p-squared/2 bound upgrades a p-squared congruence of dot
products to an exact equality. -/
theorem short_dot_eq_of_square_dvd
    (p : ℤ) (x y x' y' : TernaryIntPoint)
    (hx : 2*ternaryIntNorm x < p^2) (hy : 2*ternaryIntNorm y < p^2)
    (hxn : ternaryIntNorm x' = ternaryIntNorm x)
    (hyn : ternaryIntNorm y' = ternaryIntNorm y)
    (hd : p^2 ∣ ternaryIntDot x' y' - ternaryIntDot x y) :
    ternaryIntDot x' y' = ternaryIntDot x y := by
  obtain ⟨hlo, hhi⟩ := ternaryIntDot_bounds x y
  obtain ⟨hlo', hhi'⟩ := ternaryIntDot_bounds x' y'
  rw [hxn, hyn] at hlo' hhi'
  have habs : |ternaryIntDot x' y' - ternaryIntDot x y| < p^2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hcast : ((ternaryIntDot x' y' - ternaryIntDot x y).natAbs : ℤ) <
      ((p^2).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs, abs_of_nonneg (sq_nonneg p)] using habs
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by exact_mod_cast hcast)

theorem short_equal_norm_point_translate_unique
    (p : ℤ) (x y z : TernaryIntPoint) (hp : 0 < p) (hpodd : Odd p)
    (hpoint : x = y+p • z) (hnorm : ternaryIntNorm x = ternaryIntNorm y)
    (hshort : 2*ternaryIntNorm y < p^2) : x = y := by
  have hz := short_equal_norm_translate_unique p y.1.1 y.1.2 y.2
    z.1.1 z.1.2 z.2 hp hpodd (by simpa [hpoint, ternaryIntNorm] using hnorm) hshort
  have hz' : z = 0 := by
    apply Prod.ext
    · exact Prod.ext hz.1 hz.2.1
    · exact hz.2.2
  simpa [hz'] using hpoint

/-- Explicit integral coordinates for a point of p times the dual lattice. -/
structure ProjectiveDualLift (p : ℕ) (v : TernaryIntPoint) where
  point : TernaryIntPoint
  scalar : ℤ
  remainder : TernaryIntPoint
  point_eq : point = scalar • v + (p : ℤ) • remainder

namespace ProjectiveDualLift

variable {p : ℕ} {v : TernaryIntPoint}

/-- The integral pairing quotient, independent of the chosen lift data. -/
def pairing (x : ProjectiveDualLift p v) : ℤ := ternaryIntDot v x.point / p

theorem dot_base (x : ProjectiveDualLift p v) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) :
    ternaryIntDot v x.point =
      (p : ℤ)*(x.scalar*h + ternaryIntDot v x.remainder) := by
  rw [x.point_eq]
  rcases v with ⟨⟨a,b⟩,c⟩
  rcases x.remainder with ⟨⟨d,e⟩,f⟩
  simp only [ternaryIntDot, ternaryIntNorm, ternaryDot, ternaryNorm,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at hv ⊢
  linear_combination x.scalar * hv

theorem pairing_eq (x : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) :
    x.pairing = x.scalar*h + ternaryIntDot v x.remainder := by
  rw [pairing, x.dot_base h hv]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp)

theorem dot_identity (x y : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) :
    ternaryIntDot x.point y.point =
      (p : ℤ)*(x.scalar*y.pairing + y.scalar*x.pairing - h*x.scalar*y.scalar) +
        (p : ℤ)^2 * ternaryIntDot x.remainder y.remainder := by
  rw [x.point_eq, y.point_eq, x.pairing_eq hp h hv, y.pairing_eq hp h hv]
  exact projective_lift_dot_quotient_identity p h x.scalar y.scalar
    v.1.1 v.1.2 v.2 x.remainder.1.1 x.remainder.1.2 x.remainder.2
    y.remainder.1.1 y.remainder.1.2 y.remainder.2 hv

theorem dot_quotient_eq (x y : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) :
    ternaryIntDot x.point y.point / p =
      x.scalar*y.pairing + y.scalar*x.pairing - h*x.scalar*y.scalar +
        (p : ℤ)*ternaryIntDot x.remainder y.remainder := by
  have heq : ternaryIntDot x.point y.point = (p : ℤ)*
      (x.scalar*y.pairing + y.scalar*x.pairing - h*x.scalar*y.scalar +
        (p : ℤ)*ternaryIntDot x.remainder y.remainder) := by
    rw [x.dot_identity y hp h hv]
    ring
  rw [heq]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp)

theorem dot_dvd (x y : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) :
    (p : ℤ) ∣ ternaryIntDot x.point y.point := by
  refine ⟨x.scalar*y.pairing + y.scalar*x.pairing - h*x.scalar*y.scalar +
    (p : ℤ)*ternaryIntDot x.remainder y.remainder, ?_⟩
  rw [x.dot_identity y hp h hv]
  ring

/-- The actual linear phase modulo p in projective coordinates. -/
def phase (x : ProjectiveDualLift p v) (c : ZMod p) : ZMod p :=
  2*(x.pairing : ZMod p)+c*x.scalar

/-- The existing Watson compression, now evaluated on an actual dual lift. -/
def compressedPhase (x : ProjectiveDualLift p v) (q R n : ℤ) : ℤ :=
  dualWatsonCompressedPhase p
    (dualWatsonBasePhase q R x.pairing x.point.1.1 x.point.1.2 x.point.2) n

/-- The abstract phase coordinate is the reduction of the actual Watson
phase. The conjugate-factor count disappears modulo p. -/
theorem phase_eq_compressed_mod_prime (x : ProjectiveDualLift p v)
    (q R n : ℤ) (hq : (3 : ZMod p)*q*v.2 = 1) :
    3*x.phase (((q*v.2*(2*R-(v.1.1+v.1.2+v.2)) : ℤ) : ZMod p)) =
      (x.compressedPhase q R n : ZMod p) := by
  unfold phase compressedPhase dualWatsonCompressedPhase dualWatsonBasePhase
  rw [x.point_eq]
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero]
  linear_combination -(x.scalar : ZMod p)*
    ((v.1.1 : ZMod p)+v.1.2+v.2)*hq

theorem phase_eq_of_compressed_congruent [Fact p.Prime]
    (x x' : ProjectiveDualLift p v) (hp3 : p ≠ 3)
    (q R n n' : ℤ) (hq : (3 : ZMod p)*q*v.2 = 1)
    (hphase : (p : ℤ) ∣ x'.compressedPhase q R n' - x.compressedPhase q R n) :
    x'.phase (((q*v.2*(2*R-(v.1.1+v.1.2+v.2)) : ℤ) : ZMod p)) =
      x.phase (((q*v.2*(2*R-(v.1.1+v.1.2+v.2)) : ℤ) : ZMod p)) := by
  have hp : p.Prime := Fact.out
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hh | hh
    · exact hp.ne_one hh
    · exact hp3 hh
  apply mul_left_cancel₀ h3
  rw [x.phase_eq_compressed_mod_prime q R n hq,
    x'.phase_eq_compressed_mod_prime q R n' hq]
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hphase
  push_cast at hz
  exact sub_eq_zero.mp hz

theorem norm_phase (x : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p) :
    ((ternaryIntNorm x.point / p : ℤ) : ZMod p) =
      (x.scalar : ZMod p)*x.phase c - ((h : ZMod p)+c)*(x.scalar : ZMod p)^2 := by
  have heq := x.dot_quotient_eq x hp h hv
  rw [ternaryIntDot_self] at heq
  rw [heq]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero, phase]
  ring

theorem dot_phase (x y : ProjectiveDualLift p v) (hp : p ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p) :
    2*((ternaryIntDot x.point y.point / p : ℤ) : ZMod p) =
      (x.scalar : ZMod p)*y.phase c + (y.scalar : ZMod p)*x.phase c -
        2*((h : ZMod p)+c)*(x.scalar : ZMod p)*(y.scalar : ZMod p) := by
  rw [x.dot_quotient_eq y hp h hv]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, add_zero, phase]
  ring

theorem short_eq_of_scalar_cast_eq (x y : ProjectiveDualLift p v)
    (hp : 0 < p) (hpodd : Odd (p : ℤ))
    (hnorm : ternaryIntNorm x.point = ternaryIntNorm y.point)
    (hshort : 2*ternaryIntNorm y.point < (p : ℤ)^2)
    (hscalar : (x.scalar : ZMod p) = (y.scalar : ZMod p)) : x.point = y.point := by
  have hdiv : (p : ℤ) ∣ x.scalar-y.scalar :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [hscalar]; ring)
  obtain ⟨t, ht⟩ := hdiv
  have hs : x.scalar = y.scalar+(p : ℤ)*t := by omega
  let z := t • v + x.remainder-y.remainder
  have hpoint : x.point = y.point+(p : ℤ) • z := by
    rw [x.point_eq, y.point_eq, hs]
    dsimp [z]
    module
  exact short_equal_norm_point_translate_unique p x.point y.point z
    (by exact_mod_cast hp) hpodd hpoint hnorm hshort

/-- On short distinct partners the identity branch is impossible, so the
same arithmetic reflection governs every pair. -/
theorem short_partner_reflection [Fact p.Prime]
    (x x' : ProjectiveDualLift p v) (hpodd : Odd (p : ℤ))
    (h : ℤ) (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hnorm : ternaryIntNorm x'.point = ternaryIntNorm x.point)
    (hshort : 2*ternaryIntNorm x.point < (p : ℤ)^2)
    (hne : x'.point ≠ x.point) (hphase : x'.phase c = x.phase c) :
    ((h : ZMod p)+c)*((x.scalar : ZMod p)+x'.scalar) = x.phase c := by
  have hp : p.Prime := Fact.out
  have hquad : (x.scalar : ZMod p)*x.phase c - ((h : ZMod p)+c)*(x.scalar : ZMod p)^2 =
      (x'.scalar : ZMod p)*x.phase c - ((h : ZMod p)+c)*(x'.scalar : ZMod p)^2 := by
    rw [← x.norm_phase hp.ne_zero h hv c, ← hphase,
      ← x'.norm_phase hp.ne_zero h hv c, hnorm]
  rcases phase_norm_identity_or_reflection _ _ _ _ hquad with heq | hreflect
  · exact False.elim (hne (x'.short_eq_of_scalar_cast_eq x hp.pos hpodd hnorm hshort heq.symm))
  · exact hreflect

/-- Actual short equal-norm phase partners preserve every mutual dot
product.  This theorem does not assume a common linear map or a pairing
that was already known to be coherent. -/
theorem short_phase_partners_preserve_dot [Fact p.Prime]
    (x y x' y' : ProjectiveDualLift p v) (hpodd : Odd (p : ℤ))
    (h : ℤ) (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hxn : ternaryIntNorm x'.point = ternaryIntNorm x.point)
    (hyn : ternaryIntNorm y'.point = ternaryIntNorm y.point)
    (hx : 2*ternaryIntNorm x.point < (p : ℤ)^2)
    (hy : 2*ternaryIntNorm y.point < (p : ℤ)^2)
    (hxne : x'.point ≠ x.point) (hyne : y'.point ≠ y.point)
    (hxp : x'.phase c = x.phase c) (hyp : y'.phase c = y.phase c) :
    ternaryIntDot x'.point y'.point = ternaryIntDot x.point y.point := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by intro heq; subst p; norm_num [Odd] at hpodd
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr (by
      intro hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with hh | hh
      · exact hp.ne_one hh
      · exact hp2 hh)
  have hrx := x.short_partner_reflection x' hpodd h hv c hxn hx hxne hxp
  have hry := y.short_partner_reflection y' hpodd h hv c hyn hy hyne hyp
  have hbil := phase_reflection_preserves_polarization
    ((h : ZMod p)+c) (x.phase c) (y.phase c)
    (x.scalar : ZMod p) (y.scalar : ZMod p) (x'.scalar : ZMod p) (y'.scalar : ZMod p) hrx hry
  have hquot : ((ternaryIntDot x'.point y'.point / p : ℤ) : ZMod p) =
      ((ternaryIntDot x.point y.point / p : ℤ) : ZMod p) := by
    apply mul_left_cancel₀ h2
    rw [x'.dot_phase y' hp.ne_zero h hv c, x.dot_phase y hp.ne_zero h hv c, hxp, hyp]
    exact hbil
  have hdiv : (p : ℤ) ∣ ternaryIntDot x'.point y'.point / p -
      ternaryIntDot x.point y.point / p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [hquot]; ring)
  obtain ⟨a, ha⟩ := hdiv
  have hmul := Int.ediv_mul_cancel (x.dot_dvd y hp.ne_zero h hv)
  have hmul' := Int.ediv_mul_cancel (x'.dot_dvd y' hp.ne_zero h hv)
  apply short_dot_eq_of_square_dvd p x.point y.point x'.point y'.point hx hy hxn hyn
  refine ⟨a, ?_⟩
  linear_combination (p : ℤ)*ha - hmul' + hmul

/-- Equal-norm short phase partners are unique as integral points. This
is proved from the arithmetic, rather than supplied to a coherence theorem. -/
theorem short_phase_partner_unique [Fact p.Prime]
    (x y z : ProjectiveDualLift p v) (hpodd : Odd (p : ℤ))
    (h : ℤ) (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hyn : ternaryIntNorm y.point = ternaryIntNorm x.point)
    (hzn : ternaryIntNorm z.point = ternaryIntNorm x.point)
    (hx : 2*ternaryIntNorm x.point < (p : ℤ)^2)
    (hyne : y.point ≠ x.point) (hzne : z.point ≠ x.point)
    (hyp : y.phase c = x.phase c) (hzp : z.phase c = x.phase c) :
    y.point = z.point := by
  have hdot := x.short_phase_partners_preserve_dot x y z hpodd h hv c
    hyn hzn hx hx hyne hzne hyp hzp
  rw [ternaryIntDot_self] at hdot
  apply sub_eq_zero.mp
  apply (ternaryIntNorm_eq_zero_iff _).mp
  rw [ternaryIntNorm_sub, hyn, hzn, hdot]
  ring

/-- The dot-product conclusion for the original compressed Watson phases,
including their exact arithmetic identification. -/
theorem short_compressed_partners_preserve_dot [Fact p.Prime]
    (x y x' y' : ProjectiveDualLift p v) (hpodd : Odd (p : ℤ)) (hp3 : p ≠ 3)
    (h : ℤ) (hv : ternaryIntNorm v = (p : ℤ)*h)
    (q R nx ny nx' ny' : ℤ) (hq : (3 : ZMod p)*q*v.2 = 1)
    (hxn : ternaryIntNorm x'.point = ternaryIntNorm x.point)
    (hyn : ternaryIntNorm y'.point = ternaryIntNorm y.point)
    (hx : 2*ternaryIntNorm x.point < (p : ℤ)^2)
    (hy : 2*ternaryIntNorm y.point < (p : ℤ)^2)
    (hxne : x'.point ≠ x.point) (hyne : y'.point ≠ y.point)
    (hxp : (p : ℤ) ∣ x'.compressedPhase q R nx' - x.compressedPhase q R nx)
    (hyp : (p : ℤ) ∣ y'.compressedPhase q R ny' - y.compressedPhase q R ny) :
    ternaryIntDot x'.point y'.point = ternaryIntDot x.point y.point := by
  exact x.short_phase_partners_preserve_dot y x' y' hpodd h hv _ hxn hyn hx hy hxne hyne
    (x.phase_eq_of_compressed_congruent x' hp3 q R nx nx' hq hxp)
    (y.phase_eq_of_compressed_congruent y' hp3 q R ny ny' hq hyp)

end ProjectiveDualLift
end Ramanujan.MultiQuintuple
