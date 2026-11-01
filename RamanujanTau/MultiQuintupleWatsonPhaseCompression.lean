/-
# Compressing the actual Fourier amplitudes to one phase per vector
-/
import RamanujanTau.MultiQuintupleCanonicalDualPhase
import RamanujanTau.MultiQuintupleWatsonFourierAmplitude

namespace Ramanujan.MultiQuintuple

noncomputable def watsonSixthRoot : ℂ := Complex.exp (Real.pi*Complex.I/3)

noncomputable def watsonCommonFactor : ℂ := (1-watsonSixthRoot^2)^3

theorem watsonSixthRoot_cube : watsonSixthRoot^3 = -1 := by
  rw [watsonSixthRoot,← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring

theorem watsonAddChar_six_p (p : ℕ) [NeZero p] :
    watsonAddChar (6*p) (p : ℤ)=watsonSixthRoot := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [watsonAddChar_exp,watsonSixthRoot]
  congr 1
  push_cast
  field_simp
  ring

theorem watsonAddChar_nat_mul (n : ℕ) [NeZero n] (a : ℤ) (m : ℕ) :
    watsonAddChar n (a*(m : ℤ))=(watsonAddChar n a)^m := by
  induction m with
  | zero => simp [watsonAddChar]
  | succ m ih =>
    push_cast
    rw [mul_add,mul_one,watsonAddChar_add,ih,pow_succ]

theorem watsonAddChar_three_times (p : ℕ) [NeZero p] (a : ℤ) :
    watsonAddChar (6*p) (3*a)=watsonAddChar (2*p) a := by
  simp only [watsonAddChar_exp]
  congr 1
  push_cast
  ring

theorem watson_cubic_factor (m : ℤ) (b : Bool) (hm : (m : ZMod 3)=dualCubicSign b) :
    1-watsonAddChar 3 m=cubicWatsonFactor watsonSixthRoot b := by
  have he : watsonAddChar 3 m=watsonAddChar 3 (if b then 2 else 1) := by
    unfold watsonAddChar
    congr 1
    cases b <;> simpa [dualCubicSign,show (-1 : ZMod 3)=2 by decide] using hm
  rw [he]
  cases b <;>
    simp only [Bool.false_eq_true,if_false,if_true,cubicWatsonFactor,watsonAddChar_exp,
      watsonSixthRoot,← Complex.exp_nat_mul] <;>
    congr 2 <;> push_cast <;> ring

theorem fourierDualPoint_mod_three (p : ℕ) (v : TernaryIntPoint)
    (x : ZMod p × TernaryIntPoint) :
    ((fourierDualPoint p v x).1.1 : ZMod 3)=(p : ZMod 3)*(x.2.1.1 : ZMod 3) ∧
    ((fourierDualPoint p v x).1.2 : ZMod 3)=(p : ZMod 3)*(x.2.1.2 : ZMod 3) ∧
    ((fourierDualPoint p v x).2 : ZMod 3)=(p : ZMod 3)*(x.2.2 : ZMod 3) := by
  simp [fourierDualPoint,show (3 : ZMod 3)=0 by decide]

theorem rawFourierAmplitude_zero_of_unsupported (p : ℕ) [NeZero p]
    (hp3 : (p : ZMod 3) ≠ 0) (v : TernaryIntPoint) (R : ℤ)
    (x : ZMod p × TernaryIntPoint) (hx : ternaryCubicCharacter (fourierDualPoint p v x)=0) :
    rawFourierAmplitude p v R x=0 := by
  obtain ⟨h1,h2,h3⟩ := fourierDualPoint_mod_three p v x
  have hm : (x.2.1.1 : ZMod 3)=0 ∨ (x.2.1.2 : ZMod 3)=0 ∨ (x.2.2 : ZMod 3)=0 := by
    simpa only [ternaryCubicCharacter,h1,h2,h3,mul_eq_zero,hp3,false_or,or_assoc] using hx
  rcases hm with hm | hm | hm <;>
    simp [rawFourierAmplitude,watsonAddChar,hm]

theorem rawFourierPhase_congruent {p : ℕ} [Fact p.Prime] (v : TernaryIntPoint)
    (q R : ℤ) (hq : (3 : ZMod p)*q*(v.2 : ZMod p)=1)
    (x : ZMod p × TernaryIntPoint) :
    (6*(p : ℤ)) ∣ rawFourierPhase p v R x-
      dualLatticeBasePhase p v q R (fourierDualPoint p v x) := by
  have hd : (p : ℤ) ∣ (fourierDualPoint p v x).2*q+(x.1.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [fourierDualPoint,Prod.snd_sub,Prod.smul_snd,smul_eq_mul,
      Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,Int.cast_ofNat,
      ZMod.natCast_self,ZMod.natCast_zmod_val,zero_mul,zero_sub]
    linear_combination -x.1*hq
  obtain ⟨d,hd⟩ := hd
  refine ⟨-R*d,?_⟩
  unfold rawFourierPhase dualLatticeBasePhase dualWatsonBasePhase
  linear_combination -6*R*hd

theorem rawFourierAmplitude_compressed {p : ℕ} [Fact p.Prime]
    (hp3 : (p : ZMod 3) ≠ 0) (v : TernaryIntPoint) (q R : ℤ)
    (hq : (3 : ZMod p)*q*(v.2 : ZMod p)=1)
    (x : ZMod p × TernaryIntPoint) (s : CompressedDualSigns p (fourierDualPoint p v x)) :
    rawFourierAmplitude p v R x = watsonCommonFactor *
      watsonAddChar (2*p) (dualLatticeCompressedPhase p v q R (fourierDualPoint p v x) s / 3) := by
  obtain ⟨h1,h2,h3⟩ := fourierDualPoint_mod_three p v x
  have hm1 := mul_left_cancel₀ hp3 (h1.symm.trans s.h1)
  have hm2 := mul_left_cancel₀ hp3 (h2.symm.trans s.h2)
  have hm3 := mul_left_cancel₀ hp3 (h3.symm.trans s.h3)
  have hc : watsonAddChar (6*p) (rawFourierPhase p v R x)=
      watsonAddChar (6*p) (dualLatticeBasePhase p v q R (fourierDualPoint p v x)) := by
    apply watsonAddChar_eq_of_dvd
    simpa using rawFourierPhase_congruent v q R hq x
  rw [rawFourierAmplitude,hc,watson_cubic_factor _ _ hm1,watson_cubic_factor _ _ hm2,
    watson_cubic_factor _ _ hm3]
  rw [mul_assoc,mul_assoc,← mul_assoc (cubicWatsonFactor _ _),
    product_cubicWatsonFactor_eq_common_cube _ watsonSixthRoot_cube]
  have hd := s.three_dvd_phase v q R
  have he : dualLatticeCompressedPhase p v q R (fourierDualPoint p v x) s =
      3*(dualLatticeCompressedPhase p v q R (fourierDualPoint p v x) s/3) :=
    (Int.mul_ediv_cancel' hd).symm
  have hphase : watsonAddChar (6*p) (dualLatticeBasePhase p v q R (fourierDualPoint p v x))*
      watsonSixthRoot^s.count =
      watsonAddChar (2*p) (dualLatticeCompressedPhase p v q R (fourierDualPoint p v x) s/3) := by
    rw [← watsonAddChar_six_p p,← watsonAddChar_nat_mul,← watsonAddChar_add]
    change watsonAddChar (6*p) (dualLatticeCompressedPhase p v q R (fourierDualPoint p v x) s)=_
    conv_lhs => rw [he]
    exact watsonAddChar_three_times p _
  dsimp [watsonCommonFactor]
  rw [← hphase]
  dsimp [CompressedDualSigns.count]
  ring

end Ramanujan.MultiQuintuple
