/-
# Exact amplitudes of the Poisson-transformed Watson branches
-/
import RamanujanTau.MultiQuintupleWatsonPoisson
import RamanujanTau.MultiQuintupleDualFourierIndex
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

noncomputable def watsonAddChar (n : ℕ) [NeZero n] (a : ℤ) : ℂ :=
  ZMod.stdAddChar (a : ZMod n)

theorem watsonAddChar_exp (n : ℕ) [NeZero n] (a : ℤ) :
    watsonAddChar n a=Complex.exp (2*Real.pi*Complex.I*(a : ℂ)/n) :=
  ZMod.stdAddChar_coe a

theorem watsonAddChar_add (n : ℕ) [NeZero n] (a b : ℤ) :
    watsonAddChar n (a+b)=watsonAddChar n a*watsonAddChar n b := by
  unfold watsonAddChar
  rw [Int.cast_add,AddChar.map_add_eq_mul]

theorem watsonAddChar_eq_of_dvd (n : ℕ) [NeZero n] (a b : ℤ) (h : (n : ℤ) ∣ a-b) :
    watsonAddChar n a=watsonAddChar n b := by
  apply congrArg (ZMod.stdAddChar (N := n))
  apply sub_eq_zero.mp
  simpa only [Int.cast_sub] using (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) n).mpr h

def rawFourierPhase (p : ℕ) (v : TernaryIntPoint) (R : ℤ)
    (x : ZMod p × TernaryIntPoint) : ℤ :=
  6*(ternaryIntDot v (fourierDualPoint p v x)/p)-
    ((fourierDualPoint p v x).1.1+(fourierDualPoint p v x).1.2+(fourierDualPoint p v x).2)-
      6*(x.1.val : ℤ)*R

noncomputable def rawFourierAmplitude (p : ℕ) [NeZero p] (v : TernaryIntPoint) (R : ℤ)
    (x : ZMod p × TernaryIntPoint) : ℂ :=
  watsonAddChar (6*p) (rawFourierPhase p v R x) *
    (1-watsonAddChar 3 x.2.1.1)*(1-watsonAddChar 3 x.2.1.2)*(1-watsonAddChar 3 x.2.2)

noncomputable def dualNormGaussian (p : ℕ) (a : ℂ) (w : TernaryIntPoint) : ℂ :=
  Complex.exp (-Real.pi*(ternaryIntNorm w : ℂ)/((p : ℂ)^2*a))

theorem fourierDualPoint_pairing (p : ℕ) [NeZero p] (v : TernaryIntPoint)
    (H : ℤ) (hv : ternaryIntNorm v=(p : ℤ)*H) (x : ZMod p × TernaryIntPoint) :
    ternaryIntDot v (fourierDualPoint p v x)/p = ternaryIntDot v x.2-3*(x.1.val : ℤ)*H := by
  have he : ternaryIntDot v (fourierDualPoint p v x)=
      (p : ℤ)*(ternaryIntDot v x.2-3*(x.1.val : ℤ)*H) := by
    unfold fourierDualPoint ternaryIntDot ternaryDot
    simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    change v.1.1^2+v.1.2^2+v.2^2=(p : ℤ)*H at hv
    linear_combination -3*(x.1.val : ℤ)*hv
  rw [he,Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne p))]

set_option maxHeartbeats 1000000 in
theorem watson_poisson_branch_term (p i j k R : ℕ) [NeZero p]
    (H : ℤ) (hv : ternaryIntNorm (((i : ℤ),(j : ℤ)),(k : ℤ))=(p : ℤ)*H)
    (a : ℂ) (ha : a ≠ 0) (b : TripleBranchBits) (x : ZMod p × TernaryIntPoint) :
    congruenceGaussianPhase p (3*i) (3*j) (3*k) (watsonBranchResidue i j k R b)
      (watsonBranchShift p i j k b) x.1 *
        separatedDualGaussian a (watsonBranchShift p i j k b)
          (congruenceModulation p (3*i) (3*j) (3*k) x.1) x.2 =
    watsonAddChar (6*p) (rawFourierPhase p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x) *
      (if b.1.1 then watsonAddChar 3 x.2.1.1 else 1) *
      (if b.1.2 then watsonAddChar 3 x.2.1.2 else 1) *
      (if b.2 then watsonAddChar 3 x.2.2 else 1) *
        dualNormGaussian p a (fourierDualPoint p (((i : ℤ),(j : ℤ)),(k : ℤ)) x) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hvC : (i : ℂ)^2+(j : ℂ)^2+(k : ℂ)^2=(p : ℂ)*(H : ℂ) := by
    exact_mod_cast hv
  simp only [rawFourierPhase,fourierDualPoint_pairing p _ H hv]
  rcases b with ⟨⟨b1,b2⟩,b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [Bool.false_eq_true,if_false,if_true,mul_one,watsonAddChar_exp,
      congruenceGaussianPhase,separatedDualGaussian,dualShiftedGaussian,
      watsonBranchShift,watsonBranchResidue,branchSign,dualNormGaussian,
      fourierDualPoint,ternaryIntNorm,ternaryNorm,ternaryIntDot,ternaryDot,
      congruenceModulation,Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul,
      Bool.false_eq_true,if_false,if_true] <;>
    push_cast <;>
    repeat rw [← Complex.exp_add]
  all_goals
    congr 1
    field_simp
    first
    | linear_combination -36*Complex.I*(x.1.val : ℂ)*a*hvC
    | linear_combination -108*Complex.I*(x.1.val : ℂ)*a*hvC

set_option maxHeartbeats 400000 in
theorem sum_watson_poisson_branch_terms (p i j k R : ℕ) [NeZero p]
    (H : ℤ) (hv : ternaryIntNorm (((i : ℤ),(j : ℤ)),(k : ℤ))=(p : ℤ)*H)
    (a : ℂ) (ha : a ≠ 0) (x : ZMod p × TernaryIntPoint) :
    (∑ b : TripleBranchBits, (tripleBranchWeight b : ℂ)*
      congruenceGaussianPhase p (3*i) (3*j) (3*k) (watsonBranchResidue i j k R b)
        (watsonBranchShift p i j k b) x.1 *
          separatedDualGaussian a (watsonBranchShift p i j k b)
            (congruenceModulation p (3*i) (3*j) (3*k) x.1) x.2) =
      rawFourierAmplitude p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x *
        dualNormGaussian p a (fourierDualPoint p (((i : ℤ),(j : ℤ)),(k : ℤ)) x) := by
  simp only [mul_assoc (tripleBranchWeight _ : ℂ),watson_poisson_branch_term p i j k R H hv a ha]
  simp [Fintype.sum_prod_type,tripleBranchWeight,branchSign,rawFourierAmplitude]
  ring

end Ramanujan.MultiQuintuple
