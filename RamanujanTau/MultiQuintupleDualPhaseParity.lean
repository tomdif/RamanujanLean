/-
# Opposite compressed phases reverse the cubic character
-/
import RamanujanTau.MultiQuintupleDualCharacter

namespace Ramanujan.MultiQuintuple

def dualCubicSign (b : Bool) : ZMod 3 := if b then -1 else 1

structure CompressedDualSigns (p : ℕ) (x : TernaryIntPoint) where
  b1 : Bool
  b2 : Bool
  b3 : Bool
  h1 : (x.1.1 : ZMod 3) = (p : ZMod 3)*dualCubicSign b1
  h2 : (x.1.2 : ZMod 3) = (p : ZMod 3)*dualCubicSign b2
  h3 : (x.2 : ZMod 3) = (p : ZMod 3)*dualCubicSign b3

def CompressedDualSigns.count {p : ℕ} {x : TernaryIntPoint}
    (s : CompressedDualSigns p x) : ℕ := cubicWatsonConjugateCount s.b1 s.b2 s.b3

theorem CompressedDualSigns.cubicCharacter_ne_zero {p : ℕ} {x : TernaryIntPoint}
    (s : CompressedDualSigns p x) (hp : (p : ZMod 3) ≠ 0) :
    ternaryCubicCharacter x ≠ 0 := by
  have hs : ∀ b : Bool, dualCubicSign b ≠ 0 := by
    intro b
    cases b <;> decide
  simp only [ternaryCubicCharacter,s.h1,s.h2,s.h3]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp (hs _)) (mul_ne_zero hp (hs _)))
    (mul_ne_zero hp (hs _))

private theorem nonzero_mod_three_sign :
    ∀ p x : ZMod 3, p ≠ 0 → x ≠ 0 → ∃ b : Bool, x = p*dualCubicSign b := by
  decide +kernel

theorem exists_compressedDualSigns (p : ℕ) (hp : (p : ZMod 3) ≠ 0)
    (x : TernaryIntPoint) (hx : ternaryCubicCharacter x ≠ 0) :
    Nonempty (CompressedDualSigns p x) := by
  have h1 : (x.1.1 : ZMod 3) ≠ 0 := by intro h; exact hx (by simp [ternaryCubicCharacter,h])
  have h2 : (x.1.2 : ZMod 3) ≠ 0 := by intro h; exact hx (by simp [ternaryCubicCharacter,h])
  have h3 : (x.2 : ZMod 3) ≠ 0 := by intro h; exact hx (by simp [ternaryCubicCharacter,h])
  obtain ⟨b1,hb1⟩ := nonzero_mod_three_sign p x.1.1 hp h1
  obtain ⟨b2,hb2⟩ := nonzero_mod_three_sign p x.1.2 hp h2
  obtain ⟨b3,hb3⟩ := nonzero_mod_three_sign p x.2 hp h3
  exact ⟨⟨b1,b2,b3,hb1,hb2,hb3⟩⟩

private theorem mod_two_square : ∀ a : ZMod 2, a^2 = a := by decide +kernel

theorem equal_norm_coordinate_sum_mod_two (x y : TernaryIntPoint)
    (hn : ternaryIntNorm y = ternaryIntNorm x) :
    (y.1.1 : ZMod 2)+(y.1.2 : ZMod 2)+(y.2 : ZMod 2) =
      (x.1.1 : ZMod 2)+(x.1.2 : ZMod 2)+(x.2 : ZMod 2) := by
  have hh := congrArg (fun n : ℤ => (n : ZMod 2)) hn
  simpa [ternaryIntNorm,ternaryNorm,mod_two_square] using hh

private theorem opposite_count_signs :
    ∀ a b c d e f : Bool,
      (cubicWatsonConjugateCount d e f : ZMod 2) -
        (cubicWatsonConjugateCount a b c : ZMod 2) = 1 →
      dualCubicSign d*dualCubicSign e*dualCubicSign f =
        -(dualCubicSign a*dualCubicSign b*dualCubicSign c) := by
  decide +kernel

/-- Norm equality and a half-turn difference of actual compressed phases
force cubic-character reversal. The parity conclusion is not an extra
hypothesis of the dual-to-root construction. -/
theorem opposite_compressed_phase_reverses_cubic
    (p : ℕ) (hpodd : Odd (p : ℤ)) (x y : TernaryIntPoint)
    (sx : CompressedDualSigns p x) (sy : CompressedDualSigns p y)
    (q R u u' : ℤ) (hn : ternaryIntNorm y = ternaryIntNorm x)
    (hphase : (6*(p : ℤ)) ∣
      dualWatsonCompressedPhase p (dualWatsonBasePhase q R u' y.1.1 y.1.2 y.2) sy.count -
        dualWatsonCompressedPhase p (dualWatsonBasePhase q R u x.1.1 x.1.2 x.2) sx.count - 3*p) :
    ternaryCubicCharacter y = -ternaryCubicCharacter x := by
  have hp2 : ((p : ℤ) : ZMod 2) = 1 := by
    obtain ⟨a,ha⟩ := hpodd
    have hh := congrArg (fun z : ℤ => (z : ZMod 2)) ha
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,
      show (2 : ZMod 2) = 0 by decide,zero_mul,zero_add] using hh
  obtain ⟨a,ha⟩ := hphase
  have hh := congrArg (fun z : ℤ => (z : ZMod 2)) ha
  have hsum := equal_norm_coordinate_sum_mod_two x y hn
  have hcount : (sy.count : ZMod 2)-(sx.count : ZMod 2) = 1 := by
    simp only [dualWatsonCompressedPhase,dualWatsonBasePhase,Int.cast_add,Int.cast_sub,
      Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,hp2] at hh
    simp only [show (6 : ZMod 2) = 0 by decide,
      show (3 : ZMod 2) = 1 by decide,zero_mul,zero_add] at hh
    linear_combination hh + hsum
  have hsign := opposite_count_signs sx.b1 sx.b2 sx.b3 sy.b1 sy.b2 sy.b3 hcount
  simp only [ternaryCubicCharacter,sy.h1,sy.h2,sy.h3,sx.h1,sx.h2,sx.h3]
  linear_combination (p : ZMod 3)^3*hsign

end Ramanujan.MultiQuintuple
