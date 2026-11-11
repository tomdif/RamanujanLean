import RamanujanTau.MultiQuintupleFourWatsonPoisson
import RamanujanTau.MultiQuintupleWatsonFourierAmplitude

/-! The actual amplitudes in the four-factor Fourier transform. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

def fourDualPoint (p : ℕ) (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) : Fin 4 → ℤ :=
  fun i => (p : ℤ)*x.2 i-3*(x.1.val : ℤ)*v i

def fourRawPhase (p : ℕ) (v : Fin 4 → ℤ) (R : ℤ) (x : ZMod p × (Fin 4 → ℤ)) : ℤ :=
  6*((∑ i, v i*fourDualPoint p v x i)/p)-(∑ i, fourDualPoint p v x i)-6*(x.1.val : ℤ)*R

noncomputable def fourRawAmplitude (p : ℕ) [NeZero p] (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) : ℂ :=
  watsonAddChar (6*p) (fourRawPhase p v R x) * ∏ i, (1-watsonAddChar 3 (x.2 i))

noncomputable def fourDualNormGaussian (p : ℕ) (a : ℂ) (w : Fin 4 → ℤ) : ℂ :=
  Complex.exp (-Real.pi*((∑ i, w i*w i : ℤ) : ℂ)/((p : ℂ)^2*a))

theorem fourDualPoint_pairing (p : ℕ) [NeZero p] (v : Fin 4 → ℤ) (H : ℤ)
    (hv : (∑ i, v i*v i)=(p : ℤ)*H) (x : ZMod p × (Fin 4 → ℤ)) :
    (∑ i, v i*fourDualPoint p v x i)/p = (∑ i, v i*x.2 i)-3*(x.1.val : ℤ)*H := by
  have he : (∑ i, v i*fourDualPoint p v x i) =
      (p : ℤ)*((∑ i, v i*x.2 i)-3*(x.1.val : ℤ)*H) := by
    calc
      _ = (p : ℤ)*(∑ i, v i*x.2 i)-3*(x.1.val : ℤ)*(∑ i, v i*v i) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [fourDualPoint]
        ring
      _ = _ := by rw [hv]; ring
  rw [he,Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne p))]

theorem four_watson_poisson_branch_term (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (a : ℂ) (ha : a ≠ 0) (b : Fin 4 → Bool) (x : ZMod p × (Fin 4 → ℤ)) :
    fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ)) (fourBranchResidue v R b)
      (fourBranchShift p v b) x.1 *
      fourSeparatedDualGaussian a (fourBranchShift p v b)
        (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) x.1) x.2 =
    watsonAddChar (6*p) (fourRawPhase p (fun i => (v i : ℤ)) R x) *
      (∏ i, if b i then watsonAddChar 3 (x.2 i) else 1) *
        fourDualNormGaussian p a (fourDualPoint p (fun i => (v i : ℤ)) x) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hvC : (∑ i, (v i : ℂ)*(v i : ℂ))=(p : ℂ)*(H : ℂ) := by exact_mod_cast hv
  simp only [fourRawPhase,fourDualPoint_pairing p _ H hv]
  simp [fourCongruenceGaussianPhase,fourSeparatedDualGaussian,dualShiftedGaussian,
    fourBranchShift,fourBranchResidue,fourDualNormGaussian,fourDualPoint,
    fourCongruenceModulation,Fin.sum_univ_succ,Fin.prod_univ_succ,
    -ZMod.natCast_val] at hvC ⊢
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;> cases h3 : b 3 <;>
    simp only [branchSign,Bool.false_eq_true,if_false,if_true,
      watsonAddChar_exp,Int.cast_one,Int.cast_neg] <;>
    push_cast <;>
    repeat rw [← Complex.exp_add]
  all_goals
    congr 1
    field_simp
    first
    | linear_combination -36*Complex.I*(x.1.val : ℂ)*a*hvC
    | linear_combination -108*Complex.I*(x.1.val : ℂ)*a*hvC

theorem four_branch_factor_sum (z : Fin 4 → ℂ) :
    (∑ b : Fin 4 → Bool, (fourBranchWeight b : ℂ)*(∏ i, if b i then z i else 1)) =
      ∏ i, (1-z i) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset Bool))
    (fun i b => (-branchSign b : ℂ)*(if b then z i else 1))
  simp only [Fintype.piFinset_univ] at h
  have he : ∀ b : Fin 4 → Bool,
      (fourBranchWeight b : ℂ)*(∏ i, if b i then z i else 1) =
      ∏ i, (-branchSign (b i) : ℂ)*(if b i then z i else 1) := by
    intro b
    simp only [fourBranchWeight,Int.cast_prod,Int.cast_neg,Finset.prod_mul_distrib]
  simp_rw [he]
  rw [← h]
  apply Finset.prod_congr rfl
  intro i _
  simp [branchSign,sub_eq_add_neg,add_comm]

theorem four_sum_poisson_branches (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (a : ℂ) (ha : a ≠ 0) (x : ZMod p × (Fin 4 → ℤ)) :
    (∑ b : Fin 4 → Bool, (fourBranchWeight b : ℂ)*
      fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ)) (fourBranchResidue v R b)
        (fourBranchShift p v b) x.1 *
        fourSeparatedDualGaussian a (fourBranchShift p v b)
          (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) x.1) x.2) =
      fourRawAmplitude p (fun i => (v i : ℤ)) R x *
        fourDualNormGaussian p a (fourDualPoint p (fun i => (v i : ℤ)) x) := by
  simp_rw [mul_assoc (fourBranchWeight _ : ℂ),four_watson_poisson_branch_term p v R H hv a ha]
  calc
    _ = watsonAddChar (6*p) (fourRawPhase p (fun i => (v i : ℤ)) R x) *
      (∑ b : Fin 4 → Bool, (fourBranchWeight b : ℂ)*(∏ i, if b i then watsonAddChar 3 (x.2 i) else 1)) *
        fourDualNormGaussian p a (fourDualPoint p (fun i => (v i : ℤ)) x) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [four_branch_factor_sum]; rfl

end Ramanujan.MultiQuintuple
