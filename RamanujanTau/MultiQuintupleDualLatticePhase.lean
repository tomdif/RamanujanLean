/-
# The linear phase on the actual integral dual lattice
-/
import RamanujanTau.MultiQuintupleDualLattice

namespace Ramanujan.MultiQuintuple

def dualLatticePhase (p : ℕ) [Fact p.Prime] (v : TernaryIntPoint) (c : ZMod p)
    (x : TernaryIntPoint) : ZMod p :=
  2*((ternaryIntDot v x / p : ℤ) : ZMod p) + c*(x.1.1 : ZMod p)/(v.1.1 : ZMod p)

theorem projectiveDualLattice_pairing_dvd {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint}
    (hv : (p : ℤ) ∣ ternaryIntNorm v) {x : TernaryIntPoint}
    (hx : x ∈ projectiveDualLattice p v) : (p : ℤ) ∣ ternaryIntDot v x := by
  apply congruence_projective_dot_dvd (y := x) _ hx
  change (p : ℤ) ∣ ternaryIntDot v v
  simpa using hv

theorem dualLatticePhase_add {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (c : ZMod p)
    (x y : TernaryIntPoint) (hx : x ∈ projectiveDualLattice p v)
    (hy : y ∈ projectiveDualLattice p v) :
    dualLatticePhase p v c (x+y) = dualLatticePhase p v c x + dualLatticePhase p v c y := by
  obtain ⟨a,ha⟩ := projectiveDualLattice_pairing_dvd hv hx
  obtain ⟨b,hb⟩ := projectiveDualLattice_pairing_dvd hv hy
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hab : ternaryIntDot v (x+y) = (p : ℤ)*(a+b) := by
    rw [ternaryIntDot_add_right,ha,hb]
    ring
  simp only [dualLatticePhase,hab,ha,hb,Int.mul_ediv_cancel_left _ hpz,
    Prod.fst_add,Int.cast_add]
  ring

theorem dualLatticePhase_smul {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (c : ZMod p)
    (a : ℤ) (x : TernaryIntPoint) (hx : x ∈ projectiveDualLattice p v) :
    dualLatticePhase p v c (a • x) = a • dualLatticePhase p v c x := by
  obtain ⟨b,hb⟩ := projectiveDualLattice_pairing_dvd hv hx
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hab : ternaryIntDot v (a • x) = (p : ℤ)*(a*b) := by
    rw [ternaryIntDot_smul_right,hb]
    ring
  simp only [dualLatticePhase]
  rw [hab,hb]
  simp only [Int.mul_ediv_cancel_left _ hpz,Prod.smul_fst,smul_eq_mul,Int.cast_mul]
  rw [zsmul_eq_mul]
  ring

@[simp] theorem dualLatticePhase_zero (p : ℕ) [Fact p.Prime] (v : TernaryIntPoint) (c : ZMod p) :
    dualLatticePhase p v c 0 = 0 := by
  simp [dualLatticePhase,ternaryIntDot,ternaryDot]

def dualLatticePhaseLinear (p : ℕ) [Fact p.Prime] (v : TernaryIntPoint) (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (c : ZMod p) :
    projectiveDualLattice p v →ₗ[ℤ] ZMod p where
  toFun x := dualLatticePhase p v c x
  map_add' x y := dualLatticePhase_add hp hv c x y x.property y.property
  map_smul' a x := dualLatticePhase_smul hp hv c a x x.property

theorem ProjectiveDualLift.phase_eq_dualLatticePhase
    {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint}
    (x : ProjectiveDualLift p v) (c : ZMod p) (hvi : (v.1.1 : ZMod p) ≠ 0) :
    x.phase c = dualLatticePhase p v c x.point := by
  have hs : (x.point.1.1 : ZMod p) = (x.scalar : ZMod p)*v.1.1 := by
    rw [x.point_eq]
    simp
  simp only [ProjectiveDualLift.phase,ProjectiveDualLift.pairing,dualLatticePhase,hs]
  field_simp [hvi]

theorem dualLatticePhase_p_basis1 {p : ℕ} [Fact p.Prime] (hp : p ≠ 0)
    (v : TernaryIntPoint) (c : ZMod p) :
    dualLatticePhase p v c ((p : ℤ) • thetaIndexBasis1) = 2*(v.1.1 : ZMod p) := by
  have hdot : ternaryIntDot v ((p : ℤ) • thetaIndexBasis1) = (p : ℤ)*v.1.1 := by
    simp [ternaryIntDot,ternaryDot,thetaIndexBasis1,mul_comm]
  simp only [dualLatticePhase]
  rw [hdot,Int.mul_ediv_cancel_left _ (show (p : ℤ) ≠ 0 by exact_mod_cast hp)]
  simp [thetaIndexBasis1]

/-- The phase identity extends along an integral generating family together
with the integer image. -/
theorem phase_preserved_of_integral_generators
    {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (c : ZMod p)
    (S : Set TernaryIntPoint) (hspan : Submodule.span ℤ S = projectiveDualLattice p v)
    (T : TernaryRatPoint →ₗ[ℚ] TernaryRatPoint)
    (himages : ∀ x ∈ S, ∃ y ∈ projectiveDualLattice p v,
      T (ternaryIntIndexToRat x) = ternaryIntIndexToRat y ∧
      dualLatticePhase p v c y = dualLatticePhase p v c x) :
    ∀ x ∈ projectiveDualLattice p v, ∃ y ∈ projectiveDualLattice p v,
      T (ternaryIntIndexToRat x) = ternaryIntIndexToRat y ∧
      dualLatticePhase p v c y = dualLatticePhase p v c x := by
  intro x hx
  rw [← hspan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact himages x hx
  | zero =>
      refine ⟨0,(projectiveDualLattice p v).zero_mem,?_,rfl⟩
      change T 0 = 0
      exact map_zero T
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hea,hpa⟩ := ix
      obtain ⟨b,hb,heb,hpb⟩ := iy
      refine ⟨a+b,(projectiveDualLattice p v).add_mem ha hb,?_,?_⟩
      · change T (ternaryIntToRatLinear (x+y)) = ternaryIntToRatLinear (a+b)
        rw [map_add,map_add,map_add]
        exact congrArg₂ HAdd.hAdd hea heb
      · rw [hspan] at hx hy
        rw [dualLatticePhase_add hp hv c a b ha hb,
          dualLatticePhase_add hp hv c x y hx hy,hpa,hpb]
  | smul a x hx ix =>
      obtain ⟨y,hy,hey,hpy⟩ := ix
      refine ⟨a • y,(projectiveDualLattice p v).smul_mem a hy,?_,?_⟩
      · change (T.restrictScalars ℤ) (ternaryIntToRatLinear (a • x)) =
          ternaryIntToRatLinear (a • y)
        simp only [map_smul]
        exact congrArg (fun z => a • z) hey
      · rw [hspan] at hx
        rw [dualLatticePhase_smul hp hv c a y hy,
          dualLatticePhase_smul hp hv c a x hx,hpy]

/-- A generating set contains a vector of nonzero phase: the phase on
p times the first coordinate vector is twice the first base coordinate. -/
theorem exists_nonzero_dual_phase_generator
    {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ ternaryIntNorm v) (c : ZMod p)
    (S : Set TernaryIntPoint) (hspan : Submodule.span ℤ S = projectiveDualLattice p v)
    (hnonzero : (2 : ZMod p)*(v.1.1 : ZMod p) ≠ 0) :
    ∃ x ∈ S, dualLatticePhase p v c x ≠ 0 := by
  by_contra! hn
  have hall : ∀ x ∈ projectiveDualLattice p v, dualLatticePhase p v c x = 0 := by
    intro x hx
    rw [← hspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hn x hx
    | zero => exact dualLatticePhase_zero p v c
    | add x y hx hy ix iy =>
        rw [hspan] at hx hy
        rw [dualLatticePhase_add hp hv c x y hx hy,ix,iy,add_zero]
    | smul a x hx ix =>
        rw [hspan] at hx
        rw [dualLatticePhase_smul hp hv c a x hx,ix,smul_zero]
  have hz := hall ((p : ℤ) • thetaIndexBasis1) (projectiveDualLattice_mul p v _)
  rw [dualLatticePhase_p_basis1 hp v c] at hz
  exact hnonzero hz

end Ramanujan.MultiQuintuple
