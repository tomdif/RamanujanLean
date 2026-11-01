/-
# The cubic character of a rational short reflection
-/
import RamanujanTau.MultiQuintupleDualLattice

namespace Ramanujan.MultiQuintuple

def ternaryCubicCharacter (x : TernaryIntPoint) : ZMod 3 :=
  (x.1.1 : ZMod 3)*(x.1.2 : ZMod 3)*(x.2 : ZMod 3)

@[simp] theorem ternaryCubicCharacter_neg (x : TernaryIntPoint) :
    ternaryCubicCharacter (-x) = -ternaryCubicCharacter x := by
  simp [ternaryCubicCharacter]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every ternary reflection over F₃ acts on the cubic coordinate character
by minus the norm of its normal. This includes all supported input vectors. -/
theorem reflection_cubic_character_mod_three :
    ∀ w1 w2 w3 a x1 x2 x3 : ZMod 3,
      a*(w1^2+w2^2+w3^2) = 2 →
      (x1-a*(w1*x1+w2*x2+w3*x3)*w1) *
        (x2-a*(w1*x1+w2*x2+w3*x3)*w2) *
        (x3-a*(w1*x1+w2*x2+w3*x3)*w3) =
          -(w1^2+w2^2+w3^2)*(x1*x2*x3) := by
  decide +kernel

/-- The rational Householder formula is cleared before reducing modulo
three, so no map from Q to F₃ is presumed. -/
theorem householder_integral_cubic_character
    (w x y : TernaryIntPoint) (hw : w ≠ 0)
    (hmod : (ternaryIntNorm w : ZMod 3) ≠ 0)
    (hmap : ternaryRatHouseholder (ternaryIntIndexToRat w)
      (ternaryIntIndexToRat x) = ternaryIntIndexToRat y) :
    ternaryCubicCharacter y = -(ternaryIntNorm w : ZMod 3)*ternaryCubicCharacter x := by
  have hwq : ternaryIntIndexToRat w ≠ 0 := by
    intro hz
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa [ternaryIntIndexToRat] using hz
  have hnq : ternaryRatNorm (ternaryIntIndexToRat w) ≠ 0 :=
    ne_of_gt (ternaryRatNorm_pos hwq)
  have hclear : (ternaryIntNorm w) • y =
      (ternaryIntNorm w) • x - (2*ternaryIntDot x w) • w := by
    have hh := congrArg (fun z => ternaryRatNorm (ternaryIntIndexToRat w) • z) hmap
    simp only [ternaryRatHouseholder,smul_sub,smul_smul] at hh
    rw [mul_div_cancel₀ _ hnq,ternaryRatDot_intIndexToRat,
      ternaryRatNorm_intIndexToRat] at hh
    apply ternaryIntIndexToRat_injective
    change ternaryIntToRatLinear ((ternaryIntNorm w) • y) =
      ternaryIntToRatLinear ((ternaryIntNorm w) • x - (2*ternaryIntDot x w) • w)
    simp only [map_sub,map_smul]
    simpa [ternaryIntToRatLinear,ternaryIntIndexToRat,ternaryIntNorm,
      smul_eq_mul] using hh.symm
  have hy1 : (y.1.1 : ZMod 3) = (x.1.1 : ZMod 3) -
      (2/(ternaryIntNorm w : ZMod 3))*(ternaryIntDot w x : ZMod 3)*w.1.1 := by
    have hc := congrArg (fun z : TernaryIntPoint => (z.1.1 : ZMod 3)) hclear
    simp only [Prod.smul_fst,Prod.fst_sub,smul_eq_mul,Int.cast_mul,Int.cast_sub,
      Int.cast_ofNat,ternaryIntDot_comm x w] at hc
    field_simp
    linear_combination hc
  have hy2 : (y.1.2 : ZMod 3) = (x.1.2 : ZMod 3) -
      (2/(ternaryIntNorm w : ZMod 3))*(ternaryIntDot w x : ZMod 3)*w.1.2 := by
    have hc := congrArg (fun z : TernaryIntPoint => (z.1.2 : ZMod 3)) hclear
    simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul,
      Int.cast_mul,Int.cast_sub,Int.cast_ofNat,ternaryIntDot_comm x w] at hc
    field_simp
    linear_combination hc
  have hy3 : (y.2 : ZMod 3) = (x.2 : ZMod 3) -
      (2/(ternaryIntNorm w : ZMod 3))*(ternaryIntDot w x : ZMod 3)*w.2 := by
    have hc := congrArg (fun z : TernaryIntPoint => (z.2 : ZMod 3)) hclear
    simp only [Prod.smul_snd,Prod.snd_sub,smul_eq_mul,Int.cast_mul,Int.cast_sub,
      Int.cast_ofNat,ternaryIntDot_comm x w] at hc
    field_simp
    linear_combination hc
  have ha : (2/(ternaryIntNorm w : ZMod 3)) *
      ((w.1.1 : ZMod 3)^2+(w.1.2 : ZMod 3)^2+(w.2 : ZMod 3)^2) = 2 := by
    have hn : (ternaryIntNorm w : ZMod 3) =
        (w.1.1 : ZMod 3)^2+(w.1.2 : ZMod 3)^2+(w.2 : ZMod 3)^2 := by
      simp [ternaryIntNorm,ternaryNorm]
    rw [← hn]
    exact div_mul_cancel₀ _ hmod
  simp only [ternaryCubicCharacter,hy1,hy2,hy3]
  simpa [ternaryIntNorm,ternaryNorm,ternaryIntDot,ternaryDot] using
    reflection_cubic_character_mod_three w.1.1 w.1.2 w.2
      (2/(ternaryIntNorm w : ZMod 3)) x.1.1 x.1.2 x.2 ha

end Ramanujan.MultiQuintuple
