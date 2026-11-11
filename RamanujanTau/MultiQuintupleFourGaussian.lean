import RamanujanTau.MultiQuintupleCongruencePoisson

/-! Four-dimensional congruence-restricted Gaussian Poisson summation. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 1000000

def fourIntIndexEquiv : (((ℤ × ℤ) × ℤ) × ℤ) ≃ (Fin 4 → ℤ) where
  toFun x := ![x.1.1.1,x.1.1.2,x.1.2,x.2]
  invFun x := (((x 0,x 1),x 2),x 3)
  left_inv := by intro x; rfl
  right_inv := by intro x; ext i; fin_cases i <;> rfl

theorem summable_four_separated_complex (f : Fin 4 → ℤ → ℂ)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin 4 → ℤ => ∏ i, f i (x i)) := by
  have h3 := summable_three_separated_complex (hf 0) (hf 1) (hf 2)
  have h4 := summable_mul_of_summable_norm h3.norm (hf 3).norm
  rw [← fourIntIndexEquiv.summable_iff]
  simpa [fourIntIndexEquiv,Fin.prod_univ_succ,mul_assoc] using h4

theorem tsum_four_separated_complex (f : Fin 4 → ℤ → ℂ)
    (hf : ∀ i, Summable (f i)) :
    (∑' x : Fin 4 → ℤ, ∏ i, f i (x i)) = ∏ i, ∑' n : ℤ, f i n := by
  have h3 := summable_three_separated_complex (hf 0) (hf 1) (hf 2)
  rw [← fourIntIndexEquiv.tsum_eq]
  simp only [fourIntIndexEquiv,Equiv.coe_fn_mk]
  simp [Fin.prod_univ_succ]
  rw [show (fun x : (((ℤ × ℤ) × ℤ) × ℤ) =>
    f 0 x.1.1.1*(f 1 x.1.1.2*(f 2 x.1.2*f 3 x.2))) =
      (fun x => (f 0 x.1.1.1*f 1 x.1.1.2*f 2 x.1.2)*f 3 x.2) by
        funext x; ring]
  rw [tsum_mul_tsum_of_summable_norm h3.norm (hf 3).norm |>.symm,
    tsum_three_separated_complex (hf 0) (hf 1) (hf 2)]
  ring

noncomputable def fourSeparatedGaussian (a : ℂ) (s b : Fin 4 → ℂ)
    (x : Fin 4 → ℤ) : ℂ := ∏ i, shiftedGaussian a (s i) (b i) (x i)

noncomputable def fourSeparatedDualGaussian (a : ℂ) (s b : Fin 4 → ℂ)
    (x : Fin 4 → ℤ) : ℂ := ∏ i, dualShiftedGaussian a (s i) (b i) (x i)

theorem summable_fourSeparatedGaussian {a : ℂ} (ha : 0 < a.re) (s b : Fin 4 → ℂ) :
    Summable (fourSeparatedGaussian a s b) :=
  summable_four_separated_complex _ (fun _ => summable_shiftedGaussian ha _ _)

theorem summable_fourSeparatedDualGaussian {a : ℂ} (ha : 0 < a.re) (s b : Fin 4 → ℂ) :
    Summable (fourSeparatedDualGaussian a s b) :=
  summable_four_separated_complex _ (fun _ => summable_dualShiftedGaussian ha _ _)

theorem tsum_four_shiftedGaussian_poisson {a : ℂ} (ha : 0 < a.re)
    (s b : Fin 4 → ℂ) :
    (∑' x, fourSeparatedGaussian a s b x) =
      (1/a^(1/2 : ℂ))^4 * ∑' x, fourSeparatedDualGaussian a s b x := by
  change (∑' x : Fin 4 → ℤ, ∏ i, shiftedGaussian a (s i) (b i) (x i)) =
    (1/a^(1/2 : ℂ))^4 * ∑' x : Fin 4 → ℤ, ∏ i, dualShiftedGaussian a (s i) (b i) (x i)
  rw [tsum_four_separated_complex _
    (fun i => summable_shiftedGaussian ha _ _)]
  rw [tsum_four_separated_complex _
    (fun i => summable_dualShiftedGaussian ha _ _)]
  simp_rw [tsum_shiftedGaussian_poisson ha]
  simp [Finset.prod_mul_distrib,dualShiftedGaussian]

noncomputable def fourCongruenceModulation (p : ℕ) (c : Fin 4 → ℤ) (h : ZMod p) :
    Fin 4 → ℂ := fun i => (h.val : ℂ)*c i/p

noncomputable def fourCongruenceGaussianPhase (p : ℕ) (c : Fin 4 → ℤ) (d : ℤ)
    (s : Fin 4 → ℂ) (h : ZMod p) : ℂ :=
  Complex.exp (-2*Real.pi*Complex.I*(h.val : ℂ)/p*((d : ℂ)+∑ i, (c i : ℂ)*s i))

theorem four_modulated_separatedGaussian (p : ℕ) (c : Fin 4 → ℤ) (d : ℤ)
    (a : ℂ) (s : Fin 4 → ℂ) (h : ZMod p) (x : Fin 4 → ℤ) :
    Complex.exp (2*Real.pi*Complex.I*(h.val : ℂ)*
      (((∑ i, c i*x i)-d : ℤ) : ℂ)/p)*fourSeparatedGaussian a s 0 x =
      fourCongruenceGaussianPhase p c d s h *
        fourSeparatedGaussian a s (fourCongruenceModulation p c h) x := by
  simp [fourSeparatedGaussian,shiftedGaussian,fourCongruenceGaussianPhase,
    fourCongruenceModulation,Fin.prod_univ_succ,Fin.sum_univ_succ]
  repeat rw [← Complex.exp_add]
  congr 1
  ring

theorem four_congruence_gaussian_poisson (p : ℕ) [NeZero p] (c : Fin 4 → ℤ) (d : ℤ)
    {a : ℂ} (ha : 0 < a.re) (s : Fin 4 → ℂ) :
    (∑' x : Fin 4 → ℤ,
      if (p : ℤ) ∣ (∑ i, c i*x i)-d then fourSeparatedGaussian a s 0 x else 0) =
      (1/(p : ℂ))*(1/a^(1/2 : ℂ))^4 * ∑ h : ZMod p,
        fourCongruenceGaussianPhase p c d s h *
          ∑' y, fourSeparatedDualGaussian a s (fourCongruenceModulation p c h) y := by
  classical
  have hpoint (x : Fin 4 → ℤ) :
      (if (p : ℤ) ∣ (∑ i, c i*x i)-d then fourSeparatedGaussian a s 0 x else 0) =
      (1/(p : ℂ))*∑ h : ZMod p, fourCongruenceGaussianPhase p c d s h *
        fourSeparatedGaussian a s (fourCongruenceModulation p c h) x := by
    calc
      _ = (if (p : ℤ) ∣ (∑ i, c i*x i)-d then (1 : ℂ) else 0)*
          fourSeparatedGaussian a s 0 x := by split_ifs <;> simp
      _ = _ := by
        rw [congruence_exponential_projector,mul_assoc,Finset.sum_mul]
        simp_rw [four_modulated_separatedGaussian]
  simp_rw [hpoint]
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun h _ =>
    (summable_fourSeparatedGaussian ha s (fourCongruenceModulation p c h)).mul_left _)]
  simp_rw [tsum_mul_left,tsum_four_shiftedGaussian_poisson ha]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

end Ramanujan.MultiQuintuple
