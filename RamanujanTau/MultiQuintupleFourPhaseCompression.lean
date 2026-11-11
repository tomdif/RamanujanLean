import RamanujanTau.MultiQuintupleFourFourierShells
import RamanujanTau.MultiQuintupleCanonicalPhaseCharacter

/-! Compression of four-factor amplitudes. The extra `p` in the numerator
is essential in even dimension: the common factor contains a sixth-root
inverse, and the antipodal law has no half-turn. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourSignCount (b : Fin 4 → Bool) : ℕ := ∑ i, if b i then 1 else 0

def fourCompressedNumerator (p : ℕ) (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (b : Fin 4 → Bool) : ℤ :=
  fourRawPhase p v R x+(p : ℤ)*(fourSignCount b+1)

noncomputable def fourCommonFactor (p : ℕ) [NeZero p] : ℂ :=
  (1-watsonSixthRoot^2)^4*watsonAddChar (6*p) (-(p : ℤ))

def fourCubicCharacter (z : Fin 4 → ℤ) : ZMod 3 := ∏ i, (z i : ZMod 3)

theorem fourDualPoint_mod_three (p : ℕ) (v : Fin 4 → ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (i : Fin 4) :
    (fourDualPoint p v x i : ZMod 3)=(p : ZMod 3)*(x.2 i : ZMod 3) := by
  simp [fourDualPoint,show (3 : ZMod 3)=0 by decide]

theorem fourRawAmplitude_zero_of_unsupported (p : ℕ) [NeZero p]
    (v : Fin 4 → ℤ) (R : ℤ) (x : ZMod p × (Fin 4 → ℤ))
    (hx : fourCubicCharacter x.2=0) : fourRawAmplitude p v R x=0 := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hx
  have hf : ∏ i, (1-watsonAddChar 3 (x.2 i))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [watsonAddChar,hi]
  simp only [fourRawAmplitude,hf,mul_zero]

theorem exists_four_signs (z : Fin 4 → ℤ) (hz : fourCubicCharacter z ≠ 0) :
    ∃ b : Fin 4 → Bool, ∀ i, (z i : ZMod 3)=dualCubicSign (b i) := by
  have hs : ∀ t : ZMod 3, t ≠ 0 → ∃ b : Bool, t=dualCubicSign b := by decide +kernel
  have hi (i : Fin 4) : (z i : ZMod 3) ≠ 0 := by
    intro h
    exact hz (Finset.prod_eq_zero (Finset.mem_univ i) h)
  exact Classical.axiomOfChoice (fun i => hs (z i) (hi i))

theorem four_compressed_numerator_dvd (p : ℕ) (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (b : Fin 4 → Bool)
    (hb : ∀ i, (x.2 i : ZMod 3)=dualCubicSign (b i)) :
    (3 : ℤ) ∣ fourCompressedNumerator p v R x b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  have hc : (∑ i, dualCubicSign (b i))=(fourSignCount b : ZMod 3)+1 := by
    have hf : ∀ b : Fin 4 → Bool, (∑ i, dualCubicSign (b i))=
        (fourSignCount b : ZMod 3)+1 := by decide +kernel
    exact hf b
  simp only [fourCompressedNumerator,fourRawPhase,Int.cast_add,Int.cast_mul,
    Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_ofNat,
    show (6 : ZMod 3)=0 by decide,zero_mul,zero_sub,sub_zero,
    fourDualPoint_mod_three,hb,← Finset.mul_sum,hc]
  ring

theorem four_cubic_factor_product (b : Fin 4 → Bool) :
    (∏ i, cubicWatsonFactor watsonSixthRoot (b i)) =
      (1-watsonSixthRoot^2)^4*watsonSixthRoot^(fourSignCount b) := by
  have hf (t : Bool) : cubicWatsonFactor watsonSixthRoot t=
      (1-watsonSixthRoot^2)*watsonSixthRoot^(if t then 1 else 0 : ℕ) := by
    cases t
    · simp [cubicWatsonFactor]
    · simp only [cubicWatsonFactor,if_true,pow_one]
      have h := watsonSixthRoot_cube
      linear_combination (1-watsonSixthRoot)*h
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,fourSignCount]

theorem fourRawAmplitude_compressed (p : ℕ) [NeZero p] (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (b : Fin 4 → Bool)
    (hb : ∀ i, (x.2 i : ZMod 3)=dualCubicSign (b i)) :
    fourRawAmplitude p v R x = fourCommonFactor p *
      watsonAddChar (2*p) (fourCompressedNumerator p v R x b/3) := by
  have hd := four_compressed_numerator_dvd p v R x b hb
  have hphase : watsonAddChar (6*p) (-(p : ℤ))*
      watsonAddChar (2*p) (fourCompressedNumerator p v R x b/3) =
      watsonAddChar (6*p) (fourRawPhase p v R x)*watsonSixthRoot^(fourSignCount b) := by
    rw [← watsonAddChar_three_times p,
      Int.mul_ediv_cancel' hd,← watsonAddChar_add,
      ← watsonAddChar_six_p p,← watsonAddChar_nat_mul,← watsonAddChar_add]
    congr 1
    simp only [fourCompressedNumerator]
    ring
  simp only [fourRawAmplitude]
  simp_rw [watson_cubic_factor _ _ (hb _)]
  rw [four_cubic_factor_product,fourCommonFactor,mul_assoc, hphase]
  ring

theorem fourCommonFactor_ne_zero (p : ℕ) [NeZero p] : fourCommonFactor p ≠ 0 := by
  have hbase : 1-watsonSixthRoot^2 ≠ 0 := by
    intro h
    exact watsonCommonFactor_ne_zero (by simp [watsonCommonFactor,h])
  exact mul_ne_zero (pow_ne_zero _ hbase) (by rw [watsonAddChar_exp]; exact Complex.exp_ne_zero _)

end Ramanujan.MultiQuintuple
