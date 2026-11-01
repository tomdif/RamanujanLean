/-
# Canonical root-of-unity phases and their antipodal law
-/
import RamanujanTau.MultiQuintupleWatsonPhaseCompression

namespace Ramanujan.MultiQuintuple

noncomputable def canonicalDualSigns (p : ℕ) (hp3 : (p : ZMod 3) ≠ 0)
    (x : TernaryIntPoint) (hx : ternaryCubicCharacter x ≠ 0) : CompressedDualSigns p x :=
  Classical.choice (exists_compressedDualSigns p hp3 x hx)

noncomputable def canonicalDualPhase (p : ℕ) (hp3 : (p : ZMod 3) ≠ 0)
    (v : TernaryIntPoint) (q R : ℤ) (x : TernaryIntPoint) : ZMod (2*p) := by
  classical
  exact if hx : ternaryCubicCharacter x ≠ 0 then
    ((dualLatticeCompressedPhase p v q R x (canonicalDualSigns p hp3 x hx)/3 : ℤ) : ZMod (2*p)) else 0

theorem canonicalDualPhase_eq (p : ℕ) (hp3 : (p : ZMod 3) ≠ 0)
    (v : TernaryIntPoint) (q R : ℤ) (x : TernaryIntPoint) (s : CompressedDualSigns p x) :
    canonicalDualPhase p hp3 v q R x=
      ((dualLatticeCompressedPhase p v q R x s/3 : ℤ) : ZMod (2*p)) := by
  classical
  letI : NeZero (p : ZMod 3) := ⟨hp3⟩
  simp only [canonicalDualPhase,dif_pos (s.cubicCharacter_ne_zero hp3)]
  rw [Subsingleton.elim (canonicalDualSigns p hp3 x _) s]

theorem canonicalDualPhase_neg {p : ℕ} [Fact p.Prime] (hp3 : (p : ZMod 3) ≠ 0)
    {v x : TernaryIntPoint} (hv : (p : ℤ) ∣ ternaryIntNorm v)
    (hx : x ∈ projectiveDualLattice p v) (hs : ternaryCubicCharacter x ≠ 0) (q R : ℤ) :
    canonicalDualPhase p hp3 v q R (-x)=(p : ZMod (2*p))-canonicalDualPhase p hp3 v q R x := by
  let s := canonicalDualSigns p hp3 x hs
  rw [canonicalDualPhase_eq p hp3 v q R (-x) s.neg,canonicalDualPhase_eq p hp3 v q R x s,
    dualLatticeCompressedPhase_neg hv hx]
  have hd := s.three_dvd_phase v q R
  have he : (3*(p : ℤ)-dualLatticeCompressedPhase p v q R x s)/3 =
      (p : ℤ)-dualLatticeCompressedPhase p v q R x s/3 := by omega
  rw [he]
  push_cast
  rfl

theorem watsonAddChar_eq_root_power (n : ℕ) [NeZero n] (a : ℤ) :
    watsonAddChar n a=(watsonAddChar n 1)^((a : ZMod n).val) := by
  have hh := (ZMod.stdAddChar (N := n)).map_nsmul_eq_pow ((a : ZMod n).val) 1
  simpa only [watsonAddChar,nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val,Int.cast_one] using hh

noncomputable def watsonPhaseRoot (p : ℕ) [NeZero p] : ℂ := watsonAddChar (2*p) 1

theorem watsonPhaseRoot_half_turn (p : ℕ) [NeZero p] : (watsonPhaseRoot p)^p = -1 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [watsonPhaseRoot,← watsonAddChar_nat_mul,one_mul,watsonAddChar_exp]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  push_cast
  field_simp

theorem watsonPhaseRoot_square_primitive (p : ℕ) [NeZero p] :
    IsPrimitiveRoot ((watsonPhaseRoot p)^2) p := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have he : (watsonPhaseRoot p)^2=Complex.exp (2*Real.pi*Complex.I/(p : ℂ)) := by
    rw [watsonPhaseRoot,← watsonAddChar_nat_mul,watsonAddChar_exp]
    congr 1
    push_cast
    field_simp
  rw [he]
  exact Complex.isPrimitiveRoot_exp p (NeZero.ne p)

theorem watsonCommonFactor_ne_zero : watsonCommonFactor ≠ 0 := by
  have he : 1-watsonAddChar 3 1=1-watsonSixthRoot^2 :=
    watson_cubic_factor 1 false (by decide)
  have hn : watsonAddChar 3 1 ≠ 1 := by
    intro h
    have hh : (1 : ZMod 3)=0 := ZMod.injective_stdAddChar (by
      simpa only [watsonAddChar,Int.cast_one,AddChar.map_zero_eq_one] using h)
    exact one_ne_zero hh
  rw [watsonCommonFactor,← he]
  exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hn))

theorem rawFourierAmplitude_canonical {p : ℕ} [Fact p.Prime]
    (hp3 : (p : ZMod 3) ≠ 0) (v : TernaryIntPoint) (q R : ℤ)
    (hq : (3 : ZMod p)*q*(v.2 : ZMod p)=1)
    (x : ZMod p × TernaryIntPoint) (hx : ternaryCubicCharacter (fourierDualPoint p v x) ≠ 0) :
    rawFourierAmplitude p v R x=watsonCommonFactor*
      (watsonPhaseRoot p)^(canonicalDualPhase p hp3 v q R (fourierDualPoint p v x)).val := by
  let s := canonicalDualSigns p hp3 (fourierDualPoint p v x) hx
  rw [rawFourierAmplitude_compressed hp3 v q R hq x s,canonicalDualPhase_eq p hp3 v q R _ s,
    watsonAddChar_eq_root_power]
  rfl

end Ramanujan.MultiQuintuple
