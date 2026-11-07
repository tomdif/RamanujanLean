/-
# Integral duality for the projective congruence lattice

The integral projective lattice N = Z v + p Z^3 is p times the Euclidean
dual of L = {x : p divides v dot x}. Orthogonal involutions preserving N
therefore preserve L. Both integrality and the congruence are proved here.
-/
import RamanujanTau.MultiQuintupleDualPairingIsometry

namespace Ramanujan.MultiQuintuple

def ternaryIntToRatLinear : TernaryIntPoint →ₗ[ℤ] TernaryRatPoint where
  toFun := ternaryIntIndexToRat
  map_add' := by intros; ext <;> simp [ternaryIntIndexToRat]
  map_smul' := by intros; ext <;> simp [ternaryIntIndexToRat]

@[simp] theorem ternaryIntToRatLinear_apply (x : TernaryIntPoint) :
    ternaryIntToRatLinear x = ternaryIntIndexToRat x := rfl

theorem ternaryIntDot_comm (x y : TernaryIntPoint) :
    ternaryIntDot x y = ternaryIntDot y x := by
  simp only [ternaryIntDot, ternaryDot]
  ring

theorem ternaryIntDot_add_right (x y z : TernaryIntPoint) :
    ternaryIntDot x (y+z) = ternaryIntDot x y + ternaryIntDot x z := by
  simp [ternaryIntDot, ternaryDot]
  ring

theorem ternaryIntDot_smul_right (c : ℤ) (x y : TernaryIntPoint) :
    ternaryIntDot x (c • y) = c * ternaryIntDot x y := by
  simp [ternaryIntDot, ternaryDot]
  ring

def projectiveDualLattice (p : ℕ) (v : TernaryIntPoint) : Submodule ℤ TernaryIntPoint where
  carrier := {x | ∃ a : ℤ, ∃ z : TernaryIntPoint, x = a • v + (p : ℤ) • z}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a,z,rfl⟩ ⟨b,w,rfl⟩
    refine ⟨a+b,z+w,?_⟩
    module
  smul_mem' := by
    rintro c x ⟨a,z,rfl⟩
    refine ⟨c*a,c • z,?_⟩
    module

def congruenceLattice (p : ℕ) (v : TernaryIntPoint) : Submodule ℤ TernaryIntPoint where
  carrier := {x | (p : ℤ) ∣ ternaryIntDot v x}
  zero_mem' := by simp [ternaryIntDot, ternaryDot]
  add_mem' := by
    intro x y hx hy
    change (p : ℤ) ∣ ternaryIntDot v (x+y)
    rw [ternaryIntDot_add_right]
    exact dvd_add hx hy
  smul_mem' := by
    intro c x hx
    change (p : ℤ) ∣ ternaryIntDot v (c • x)
    rw [ternaryIntDot_smul_right]
    exact dvd_mul_of_dvd_right hx c

theorem projectiveDualLattice_base (p : ℕ) (v : TernaryIntPoint) :
    v ∈ projectiveDualLattice p v := ⟨1,0,by simp⟩

theorem projectiveDualLattice_mul (p : ℕ) (v x : TernaryIntPoint) :
    (p : ℤ) • x ∈ projectiveDualLattice p v := ⟨0,x,by simp⟩

theorem congruence_projective_dot_dvd {p : ℕ} {v x y : TernaryIntPoint}
    (hx : x ∈ congruenceLattice p v) (hy : y ∈ projectiveDualLattice p v) :
    (p : ℤ) ∣ ternaryIntDot x y := by
  obtain ⟨a,z,rfl⟩ := hy
  rw [ternaryIntDot_add_right, ternaryIntDot_smul_right, ternaryIntDot_smul_right]
  apply dvd_add
  · rw [ternaryIntDot_comm]
    exact dvd_mul_of_dvd_right hx a
  · exact dvd_mul_right _ _

/-- Pairing integrally, in multiples of p, with the full projective lattice
characterizes the integral congruence lattice even among rational points. -/
theorem integral_dual_characterization (p : ℕ) (hp : p ≠ 0)
    (v : TernaryIntPoint) (y : TernaryRatPoint) :
    (∃ x ∈ congruenceLattice p v, y = ternaryIntIndexToRat x) ↔
      ∀ w ∈ projectiveDualLattice p v, ∃ a : ℤ,
        ternaryRatDot y (ternaryIntIndexToRat w) = (p : ℚ)*a := by
  constructor
  · rintro ⟨x,hx,rfl⟩ w hw
    obtain ⟨a,ha⟩ := congruence_projective_dot_dvd hx hw
    refine ⟨a,?_⟩
    rw [ternaryRatDot_intIndexToRat]
    exact_mod_cast ha
  · intro h
    obtain ⟨a,ha⟩ := h ((p : ℤ) • thetaIndexBasis1) (projectiveDualLattice_mul p v _)
    obtain ⟨b,hb⟩ := h ((p : ℤ) • thetaIndexBasis2) (projectiveDualLattice_mul p v _)
    obtain ⟨c,hc⟩ := h ((p : ℤ) • thetaIndexBasis3) (projectiveDualLattice_mul p v _)
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
    have ha' : y.1.1 = (a : ℚ) := by
      apply mul_right_cancel₀ hpq
      simpa [ternaryRatDot,ternaryIntIndexToRat,thetaIndexBasis1,mul_comm] using ha
    have hb' : y.1.2 = (b : ℚ) := by
      apply mul_right_cancel₀ hpq
      simpa [ternaryRatDot,ternaryIntIndexToRat,thetaIndexBasis2,mul_comm] using hb
    have hc' : y.2 = (c : ℚ) := by
      apply mul_right_cancel₀ hpq
      simpa [ternaryRatDot,ternaryIntIndexToRat,thetaIndexBasis3,mul_comm] using hc
    have hy : y = ternaryIntIndexToRat ((a,b),c) := by
      exact Prod.ext (Prod.ext ha' hb') hc'
    refine ⟨((a,b),c),?_,hy⟩
    obtain ⟨d,hd⟩ := h v (projectiveDualLattice_base p v)
    rw [hy,ternaryRatDot_intIndexToRat] at hd
    change (p : ℤ) ∣ ternaryIntDot v ((a,b),c)
    rw [ternaryIntDot_comm]
    exact ⟨d,by exact_mod_cast hd⟩

theorem RationalTernaryOrthogonalInvolution.dot_self_adjoint
    (T : RationalTernaryOrthogonalInvolution) (x y : TernaryRatPoint) :
    ternaryRatDot (T.linear x) y = ternaryRatDot x (T.linear y) := by
  simpa only [T.involutive] using T.dot_preserving x (T.linear y)

/-- Integer generation, not merely rational spanning, transports preservation
from the selected generators to the entire integral lattice. -/
theorem lattice_preserved_of_integral_generators
    (P : Submodule ℤ TernaryIntPoint) (S : Set TernaryIntPoint)
    (hspan : Submodule.span ℤ S = P)
    (T : TernaryRatPoint →ₗ[ℚ] TernaryRatPoint)
    (himages : ∀ x ∈ S, ∃ y ∈ P,
      T (ternaryIntIndexToRat x) = ternaryIntIndexToRat y) :
    ∀ x ∈ P, ∃ y ∈ P, T (ternaryIntIndexToRat x) = ternaryIntIndexToRat y := by
  intro x hx
  rw [← hspan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact himages x hx
  | zero =>
      refine ⟨0,P.zero_mem,?_⟩
      change T 0 = 0
      exact map_zero T
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hea⟩ := ix
      obtain ⟨b,hb,heb⟩ := iy
      refine ⟨a+b,P.add_mem ha hb,?_⟩
      change T (ternaryIntToRatLinear (x+y)) = ternaryIntToRatLinear (a+b)
      rw [map_add,map_add,map_add]
      exact congrArg₂ HAdd.hAdd hea heb
  | smul c x hx ix =>
      obtain ⟨a,ha,hea⟩ := ix
      refine ⟨c • a,P.smul_mem c ha,?_⟩
      change (T.restrictScalars ℤ) (ternaryIntToRatLinear (c • x)) =
        ternaryIntToRatLinear (c • a)
      simp only [map_smul]
      exact congrArg (fun z => c • z) hea

/-- Preservation of the projective lattice forces preservation of its
integral dual congruence lattice. No determinant or covolume assumption is
used to infer integrality of the image. -/
theorem RationalTernaryOrthogonalInvolution.preserves_congruence_of_projective
    (T : RationalTernaryOrthogonalInvolution) (p : ℕ) (hp : p ≠ 0)
    (v : TernaryIntPoint)
    (hN : ∀ w ∈ projectiveDualLattice p v, ∃ z ∈ projectiveDualLattice p v,
      T.linear (ternaryIntIndexToRat w) = ternaryIntIndexToRat z) :
    ∀ x ∈ congruenceLattice p v, ∃ y ∈ congruenceLattice p v,
      T.linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y := by
  intro x hx
  apply (integral_dual_characterization p hp v _).mpr
  intro w hw
  obtain ⟨z,hz,hTz⟩ := hN w hw
  rw [T.dot_self_adjoint, hTz, ternaryRatDot_intIndexToRat]
  obtain ⟨a,ha⟩ := congruence_projective_dot_dvd hx hz
  exact ⟨a,by exact_mod_cast ha⟩

/-- An integral generating set of N automatically spans rational three-space,
because N contains p times every integer coordinate vector. -/
theorem projective_integral_generators_span_rat
    (p : ℕ) (hp : p ≠ 0) (v : TernaryIntPoint) (S : Set TernaryIntPoint)
    (hspan : Submodule.span ℤ S = projectiveDualLattice p v) :
    Submodule.span ℚ (ternaryIntIndexToRat '' S) = ⊤ := by
  let P := Submodule.span ℚ (ternaryIntIndexToRat '' S)
  have hmem : ∀ x ∈ projectiveDualLattice p v, ternaryIntIndexToRat x ∈ P := by
    intro x hx
    rw [← hspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x,hx,rfl⟩
    | zero => exact P.zero_mem
    | add x y hx hy ix iy =>
        change ternaryIntToRatLinear (x+y) ∈ P
        rw [map_add]
        exact P.add_mem ix iy
    | smul a x hx ix =>
        change ternaryIntToRatLinear (a • x) ∈ P
        rw [map_smul]
        exact (P.restrictScalars ℤ).smul_mem a ix
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have he : ∀ e : TernaryIntPoint, ternaryIntIndexToRat e ∈ P := by
    intro e
    have hm := P.smul_mem (p : ℚ)⁻¹ (hmem ((p : ℤ) • e) (projectiveDualLattice_mul p v e))
    have hs : ternaryIntIndexToRat ((p : ℤ) • e) = (p : ℚ) • ternaryIntIndexToRat e := by
      ext <;> simp [ternaryIntIndexToRat]
    rwa [hs,smul_smul,inv_mul_cancel₀ hpq,one_smul] at hm
  apply top_unique
  intro z _
  have hz : z = z.1.1 • ternaryIntIndexToRat thetaIndexBasis1 +
      z.1.2 • ternaryIntIndexToRat thetaIndexBasis2 +
        z.2 • ternaryIntIndexToRat thetaIndexBasis3 := by
    ext <;> simp [ternaryIntIndexToRat,thetaIndexBasis1,thetaIndexBasis2,thetaIndexBasis3]
  rw [hz]
  exact P.add_mem (P.add_mem (P.smul_mem _ (he _)) (P.smul_mem _ (he _)))
    (P.smul_mem _ (he _))

end Ramanujan.MultiQuintuple
