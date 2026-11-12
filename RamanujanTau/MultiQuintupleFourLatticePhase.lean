import RamanujanTau.MultiQuintupleFourPrimeBlockCharacters

/-! The phase identity extends from short generators to the integral projective lattice. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourLatticePhase (p : ℕ) [Fact p.Prime] (v : Fin 4 → ℤ) (c : ZMod p)
    (x : Fin 4 → ℤ) : ZMod p :=
  2*((fourDot v x / p : ℤ) : ZMod p)+c*(x 0 : ZMod p)/(v 0 : ZMod p)

theorem fourLatticePhase_add {p : ℕ} [Fact p.Prime] {v : Fin 4 → ℤ} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ fourVectorNorm v) (c : ZMod p) (x y : Fin 4 → ℤ)
    (hx : x ∈ fourProjectiveModule p v) (hy : y ∈ fourProjectiveModule p v) :
    fourLatticePhase p v c (x+y)=fourLatticePhase p v c x+fourLatticePhase p v c y := by
  obtain ⟨a,ha⟩ := four_projective_pairing_dvd p v v x hv hx
  obtain ⟨b,hb⟩ := four_projective_pairing_dvd p v v y hv hy
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hab : fourDot v (x+y)=(p : ℤ)*(a+b) := by rw [fourDot_add_right,ha,hb]; ring
  simp only [fourLatticePhase,hab,ha,hb,Int.mul_ediv_cancel_left _ hpz,Pi.add_apply,Int.cast_add]
  ring

theorem fourLatticePhase_smul {p : ℕ} [Fact p.Prime] {v : Fin 4 → ℤ} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ fourVectorNorm v) (c : ZMod p) (a : ℤ) (x : Fin 4 → ℤ)
    (hx : x ∈ fourProjectiveModule p v) :
    fourLatticePhase p v c (a • x)=(a : ZMod p)*fourLatticePhase p v c x := by
  obtain ⟨b,hb⟩ := four_projective_pairing_dvd p v v x hv hx
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hab : fourDot v (a • x)=(p : ℤ)*(a*b) := by rw [fourDot_smul_right,hb]; ring
  simp only [fourLatticePhase,hab,hb,Int.mul_ediv_cancel_left _ hpz,Pi.smul_apply,smul_eq_mul,Int.cast_mul]
  ring

@[simp] theorem fourLatticePhase_zero (p : ℕ) [Fact p.Prime] (v : Fin 4 → ℤ) (c : ZMod p) :
    fourLatticePhase p v c 0=0 := by simp [fourLatticePhase,fourDot]

theorem FourProjectiveLift.phase_eq_fourLatticePhase
    {p : ℕ} [Fact p.Prime] {v : Fin 4 → ℤ}
    (x : FourProjectiveLift p v) (c : ZMod p) (hvi : (v 0 : ZMod p) ≠ 0) :
    x.phase c=fourLatticePhase p v c x.point := by
  have hs : (x.point 0 : ZMod p)=(x.scalar : ZMod p)*(v 0 : ZMod p) := by
    rw [x.point_eq]
    simp
  simp only [FourProjectiveLift.phase,FourProjectiveLift.pairing,fourLatticePhase,hs]
  field_simp [hvi]

theorem four_phase_preserved_of_integral_generators
    {p : ℕ} [Fact p.Prime] {v : Fin 4 → ℤ} (hp : p ≠ 0)
    (hv : (p : ℤ) ∣ fourVectorNorm v) (c : ZMod p)
    (S : Set (Fin 4 → ℤ)) (hspan : Submodule.span ℤ S=fourProjectiveModule p v)
    (T : FourRatPoint →ₗ[ℚ] FourRatPoint)
    (himages : ∀ x ∈ S, ∃ y ∈ fourProjectiveModule p v,
      T (fourIntToRat x)=fourIntToRat y ∧ fourLatticePhase p v c y=fourLatticePhase p v c x) :
    ∀ x ∈ fourProjectiveModule p v, ∃ y ∈ fourProjectiveModule p v,
      T (fourIntToRat x)=fourIntToRat y ∧ fourLatticePhase p v c y=fourLatticePhase p v c x := by
  intro x hx
  rw [← hspan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact himages x hx
  | zero =>
      refine ⟨0,(fourProjectiveModule p v).zero_mem,?_,rfl⟩
      have hz0 : fourIntToRat (0 : Fin 4 → ℤ)=(0 : FourRatPoint) := by ext i; simp [fourIntToRat]
      rw [hz0,map_zero]
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hea,hpa⟩ := ix
      obtain ⟨b,hb,heb,hpb⟩ := iy
      refine ⟨a+b,(fourProjectiveModule p v).add_mem ha hb,?_,?_⟩
      · rw [fourIntToRat_add,map_add,hea,heb,fourIntToRat_add]
      · rw [hspan] at hx hy
        rw [fourLatticePhase_add hp hv c a b ha hb,fourLatticePhase_add hp hv c x y hx hy,hpa,hpb]
  | smul a x hx ix =>
      obtain ⟨y,hy,hey,hpy⟩ := ix
      refine ⟨a • y,(fourProjectiveModule p v).smul_mem a hy,?_,?_⟩
      · rw [fourIntToRat_int_smul,map_smul,hey,fourIntToRat_int_smul]
      · rw [hspan] at hx
        rw [fourLatticePhase_smul hp hv c a y hy,fourLatticePhase_smul hp hv c a x hx,hpy]

/-- Opposite canonical phases coincide modulo the prime. -/
theorem four_short_phase_preservation {p : ℕ} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0)
    (v : Fin 4 → ℤ) (hvi : (v 0 : ZMod p) ≠ 0) (R : ℤ)
    (x y : FourShortIndex p v)
    (hphase : fourCanonicalPhase p v R y.val=fourCanonicalPhase p v R x.val+p) :
    fourLatticePhase p v (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3) (fourDualPoint p v y.val)=
      fourLatticePhase p v (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3) (fourDualPoint p v x.val) := by
  change fourLatticePhase p v _ (fourFourierLift p v y.val).point=
    fourLatticePhase p v _ (fourFourierLift p v x.val).point
  rw [← (fourFourierLift p v y.val).phase_eq_fourLatticePhase _ hvi,
    ← (fourFourierLift p v x.val).phase_eq_fourLatticePhase _ hvi,
    fourFourierLift_phase h3 v R x.val x.property.1,
    fourFourierLift_phase h3 v R y.val y.property.1]
  have he := congrArg (ZMod.castHom (dvd_mul_left p 2) (ZMod p)) hphase
  simpa only [map_add,map_natCast,ZMod.natCast_self,add_zero] using he

end Ramanujan.MultiQuintuple
