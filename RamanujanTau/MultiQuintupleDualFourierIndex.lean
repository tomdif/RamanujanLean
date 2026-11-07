/-
# Identifying the Fourier indices with the actual projective lattice
-/
import RamanujanTau.MultiQuintupleDualLattice
import RamanujanTau.MultiQuintupleLatticeNormalization

namespace Ramanujan.MultiQuintuple

def fourierDualPoint (p : ℕ) (v : TernaryIntPoint) (x : ZMod p × TernaryIntPoint) : TernaryIntPoint :=
  (p : ℤ) • x.2-(3*(x.1.val : ℤ)) • v

theorem fourierDualPoint_mem (p : ℕ) (v : TernaryIntPoint) (x : ZMod p × TernaryIntPoint) :
    fourierDualPoint p v x ∈ projectiveDualLattice p v := by
  refine ⟨-3*(x.1.val : ℤ),x.2,?_⟩
  unfold fourierDualPoint
  module

theorem fourierDualPoint_injective {p : ℕ} [Fact p.Prime] (v : TernaryIntPoint)
    (h3 : (3 : ZMod p) ≠ 0) (hv : (v.1.1 : ZMod p) ≠ 0) :
    Function.Injective (fourierDualPoint p v) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ hxy
  have he := congrArg (fun z : TernaryIntPoint => (z.1.1 : ZMod p)) hxy
  have hab : a=b := by
    have hm : (3 : ZMod p)*a*(v.1.1 : ZMod p)=(3 : ZMod p)*b*(v.1.1 : ZMod p) := by
      simpa [fourierDualPoint] using congrArg Neg.neg he
    exact mul_left_cancel₀ h3 (mul_right_cancel₀ hv hm)
  subst b
  have hh : (p : ℤ) • x=(p : ℤ) • y := by
    change (p : ℤ) • x-(3*(a.val : ℤ)) • v=(p : ℤ) • y-(3*(a.val : ℤ)) • v at hxy
    exact sub_left_inj.mp hxy
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 := congrArg (fun z : TernaryIntPoint => z.1.1) hh
  have h2 := congrArg (fun z : TernaryIntPoint => z.1.2) hh
  have h3' := congrArg (fun z : TernaryIntPoint => z.2) hh
  have hx : x=y := Prod.ext (Prod.ext (mul_left_cancel₀ hpZ h1) (mul_left_cancel₀ hpZ h2))
    (mul_left_cancel₀ hpZ h3')
  exact Prod.ext rfl hx

theorem fourierDualPoint_surjective {p : ℕ} [Fact p.Prime] (v : TernaryIntPoint)
    (h3 : (3 : ZMod p) ≠ 0) (w : TernaryIntPoint) (hw : w ∈ projectiveDualLattice p v) :
    ∃ x : ZMod p × TernaryIntPoint, fourierDualPoint p v x=w := by
  obtain ⟨a,z,rfl⟩ := hw
  let h : ZMod p := -(a : ZMod p)/3
  have hd : (p : ℤ) ∣ a+3*(h.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,ZMod.natCast_zmod_val]
    dsimp [h]
    field_simp
    ring
  obtain ⟨d,hd⟩ := hd
  refine ⟨(h,z+d • v),?_⟩
  have ha : a=(p : ℤ)*d-3*(h.val : ℤ) := by omega
  unfold fourierDualPoint
  rw [ha]
  module

noncomputable def dualFourierEquiv {p : ℕ} [Fact p.Prime] (v : TernaryIntPoint)
    (h3 : (3 : ZMod p) ≠ 0) (hv : (v.1.1 : ZMod p) ≠ 0) :
    ZMod p × TernaryIntPoint ≃ projectiveDualLattice p v :=
  Equiv.ofBijective (fun x => ⟨fourierDualPoint p v x,fourierDualPoint_mem p v x⟩)
    ⟨fun x y h => fourierDualPoint_injective v h3 hv (congrArg Subtype.val h),
      fun w => by
        obtain ⟨x,hx⟩ := fourierDualPoint_surjective v h3 w.val w.property
        exact ⟨x,Subtype.ext hx⟩⟩

theorem ternary_norm_shell_finite (d : ℕ) :
    Set.Finite {x : TernaryIntPoint | ternaryIntNorm x=(d : ℤ)} := by
  apply (Set.finite_Icc (((-(d : ℤ)-1,-(d : ℤ)-1)),-(d : ℤ)-1)
    ((((d : ℤ)+1,(d : ℤ)+1)),(d : ℤ)+1)).subset
  rintro ⟨⟨a,b⟩,c⟩ hx
  change a^2+b^2+c^2=(d : ℤ) at hx
  have ha : -(d : ℤ)-1 ≤ a ∧ a ≤ (d : ℤ)+1 := by
    constructor <;> nlinarith [sq_nonneg b,sq_nonneg c,Int.natCast_nonneg d]
  have hb : -(d : ℤ)-1 ≤ b ∧ b ≤ (d : ℤ)+1 := by
    constructor <;> nlinarith [sq_nonneg a,sq_nonneg c,Int.natCast_nonneg d]
  have hc : -(d : ℤ)-1 ≤ c ∧ c ≤ (d : ℤ)+1 := by
    constructor <;> nlinarith [sq_nonneg a,sq_nonneg b,Int.natCast_nonneg d]
  exact ⟨⟨⟨ha.1,hb.1⟩,hc.1⟩,⟨⟨ha.2,hb.2⟩,hc.2⟩⟩

end Ramanujan.MultiQuintuple
