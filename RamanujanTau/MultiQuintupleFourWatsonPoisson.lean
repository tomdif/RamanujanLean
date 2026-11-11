import RamanujanTau.MultiQuintupleFourPrimalGaussian
import RamanujanTau.MultiQuintupleWatsonPoisson

/-! Poisson summation on all sixteen actual four-factor Watson branches. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 1000000

def fourWatsonIndexEquiv : ((Fin 4 → Bool) × (Fin 4 → ℤ)) ≃ QuadQuintBranchIndex where
  toFun x := quadAssemble x.1 x.2
  invFun x := (quadBits x,quadIntegers x)
  left_inv := by intro x; apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv := by intro x; rfl

def fourBranchWeight (b : Fin 4 → Bool) : ℤ := ∏ i, -branchSign (b i)

theorem four_assembled_weight (b : Fin 4 → Bool) (z : Fin 4 → ℤ) :
    quadWeight (quadAssemble b z)=fourBranchWeight b := by
  simp [quadWeight,quadAssemble,pointBranchWeight,pointB1,pointB2,pointB3,quadB4,
    fourBranchWeight,Fin.prod_univ_succ]
  ring

noncomputable def fourBranchShift (p : ℕ) (v : Fin 4 → ℕ) (b : Fin 4 → Bool) : Fin 4 → ℂ :=
  fun i => (v i : ℂ)/p+(branchSign (b i) : ℂ)/6

def fourBranchResidue (v : Fin 4 → ℕ) (R : ℕ) (b : Fin 4 → Bool) : ℤ :=
  (R : ℤ)-∑ i, (v i : ℤ)*(if b i then 1 else 0)

theorem four_assembled_residue (v : Fin 4 → ℕ) (R : ℕ)
    (b : Fin 4 → Bool) (z : Fin 4 → ℤ) :
    quadResidue (v 0) (v 1) (v 2) (v 3) (quadAssemble b z)-(R : ℤ) =
      (∑ i, 3*(v i : ℤ)*z i)-fourBranchResidue v R b := by
  simp [quadResidue,quadAssemble,quadN1,quadN2,quadN3,quadN4,
    quadB1,quadB2,quadB3,quadB4,pointN1,pointN2,pointN3,pointB1,pointB2,pointB3,
    fourBranchResidue,Fin.sum_univ_succ]
  split_ifs <;> ring

theorem four_assembled_gaussian (p : ℕ) (hp : p ≠ 0) (v : Fin 4 → ℕ)
    (a : ℂ) (b : Fin 4 → Bool) (z : Fin 4 → ℤ) :
    Complex.exp (-Real.pi*a*(fourThetaNorm p v (quadAssemble b z) : ℂ)/(36*(p : ℂ)^2)) =
      fourSeparatedGaussian a (fourBranchShift p v b) 0 z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  simp [fourSeparatedGaussian,shiftedGaussian,fourBranchShift,fourThetaNorm,
    quadBits,quadIntegers,quadAssemble,quadN1,quadN2,quadN3,quadN4,
    pointN1,pointN2,pointN3,quintLatticeCoord_eq_cosetBase_add_period,
    Fin.sum_univ_succ,Fin.prod_univ_succ]
  repeat rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

noncomputable def fourBranchGaussianTerm (p : ℕ) (v : Fin 4 → ℕ) (R : ℕ) (a : ℂ)
    (b : Fin 4 → Bool) (z : Fin 4 → ℤ) : ℂ := by
  classical
  exact (fourBranchWeight b : ℂ) *
    if (p : ℤ) ∣ (∑ i, 3*(v i : ℤ)*z i)-fourBranchResidue v R b
      then fourSeparatedGaussian a (fourBranchShift p v b) 0 z else 0

theorem summable_fourBranchGaussianTerm (p : ℕ) (v : Fin 4 → ℕ) (R : ℕ)
    {a : ℂ} (ha : 0<a.re) (b : Fin 4 → Bool) :
    Summable (fourBranchGaussianTerm p v R a b) := by
  classical
  have hs := (summable_fourSeparatedGaussian ha (fourBranchShift p v b) 0).indicator
    {z | (p : ℤ) ∣ (∑ i, 3*(v i : ℤ)*z i)-fourBranchResidue v R b}
  simpa only [fourBranchGaussianTerm,Set.indicator_apply,Set.mem_setOf_eq] using
    hs.mul_left (fourBranchWeight b : ℂ)

theorem four_progression_gaussian_eq_branches (p : ℕ) (hp : p ≠ 0)
    (v : Fin 4 → ℕ) (R : ℕ) (t : ℝ) (ht : 0<t) :
    fourWatsonProgressionGaussian p v R t =
      ∑ b : Fin 4 → Bool, ∑' z : Fin 4 → ℤ, fourBranchGaussianTerm p v R (t : ℂ) b z := by
  classical
  unfold fourWatsonProgressionGaussian
  rw [← fourWatsonIndexEquiv.tsum_eq]
  have he : (fun x : (Fin 4 → Bool) × (Fin 4 → ℤ) =>
      if (p : ℤ) ∣ quadResidue (v 0) (v 1) (v 2) (v 3) (fourWatsonIndexEquiv x)-(R : ℤ) then
        (quadWeight (fourWatsonIndexEquiv x) : ℂ)*Complex.exp
          (-Real.pi*(t : ℂ)*(fourThetaNorm p v (fourWatsonIndexEquiv x) : ℂ)/(36*(p : ℂ)^2)) else 0) =
      (fun x => fourBranchGaussianTerm p v R (t : ℂ) x.1 x.2) := by
    funext x
    change (if (p : ℤ) ∣ quadResidue (v 0) (v 1) (v 2) (v 3) (quadAssemble x.1 x.2)-(R : ℤ) then
      (quadWeight (quadAssemble x.1 x.2) : ℂ)*Complex.exp
        (-Real.pi*(t : ℂ)*(fourThetaNorm p v (quadAssemble x.1 x.2) : ℂ)/(36*(p : ℂ)^2)) else 0)=_
    simp only [four_assembled_residue,four_assembled_gaussian p hp,four_assembled_weight,
      fourBranchGaussianTerm,mul_ite,mul_zero]
  have hs := summable_finite_outer
    (fun x : (Fin 4 → Bool) × (Fin 4 → ℤ) => fourBranchGaussianTerm p v R (t : ℂ) x.1 x.2)
    (fun b => summable_fourBranchGaussianTerm p v R (by simpa using ht) b)
  rw [he,hs.tsum_prod,tsum_fintype]

theorem four_progression_gaussian_poisson (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    (t : ℝ) (ht : 0<t) :
    fourWatsonProgressionGaussian p v R t =
      (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^4 *
        ∑ b : Fin 4 → Bool, ∑ h : ZMod p, (fourBranchWeight b : ℂ)*
          fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ)) (fourBranchResidue v R b)
            (fourBranchShift p v b) h *
          ∑' z : Fin 4 → ℤ, fourSeparatedDualGaussian (t : ℂ) (fourBranchShift p v b)
            (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) h) z := by
  classical
  rw [four_progression_gaussian_eq_branches p (NeZero.ne p) v R t ht]
  simp only [fourBranchGaussianTerm,tsum_mul_left]
  simp_rw [four_congruence_gaussian_poisson p (fun i => 3*(v i : ℤ)) _
    (by simpa using ht : 0<(t : ℂ).re)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro h _
  ring

end Ramanujan.MultiQuintuple
