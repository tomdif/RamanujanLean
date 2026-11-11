import RamanujanTau.MultiQuintupleFourDualArithmetic

/-! Fourier index injectivity and finiteness of four-dimensional norm shells. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators

theorem fourDualPoint_injective {p : ℕ} [Fact p.Prime] (v : Fin 4 → ℤ)
    (h3 : (3 : ZMod p) ≠ 0) (hv : (v 0 : ZMod p) ≠ 0) :
    Function.Injective (fourDualPoint p v) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ hxy
  have he := congrArg (fun z : Fin 4 → ℤ => (z 0 : ZMod p)) hxy
  have hab : a=b := by
    have hm : (3 : ZMod p)*a*(v 0 : ZMod p)=(3 : ZMod p)*b*(v 0 : ZMod p) := by
      simpa [fourDualPoint] using congrArg Neg.neg he
    exact mul_left_cancel₀ h3 (mul_right_cancel₀ hv hm)
  subst b
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx : x=y := by
    funext i
    have hi := congrFun hxy i
    simp only [fourDualPoint] at hi
    exact mul_left_cancel₀ hpZ (sub_left_inj.mp hi)
  exact Prod.ext rfl hx

theorem four_norm_shell_finite (d : ℕ) :
    Set.Finite {x : Fin 4 → ℤ | (∑ i, x i*x i)=(d : ℤ)} := by
  apply (Set.Finite.pi (fun _ : Fin 4 => Set.finite_Icc (-(d : ℤ)-1) ((d : ℤ)+1))).subset
  intro x hx
  have hi (i : Fin 4) : -(d : ℤ)-1 ≤ x i ∧ x i ≤ (d : ℤ)+1 := by
    have hs : x i*x i ≤ (d : ℤ) := by
      rw [← hx]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    constructor <;> nlinarith [Int.natCast_nonneg d]
  exact fun i _ => hi i

theorem fourNormDegree_norm (p : ℕ) (v : Fin 4 → ℤ) (d : ℕ)
    (x : (fourNormDegree p v) ⁻¹' {d}) : fourDualNorm p v x=(d : ℤ) := by
  have hn := congrArg (fun n : ℕ => (n : ℤ)) x.property
  simpa only [fourNormDegree,Int.toNat_of_nonneg
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))] using hn

theorem four_norm_degree_finite {p : ℕ} [Fact p.Prime] (v : Fin 4 → ℤ)
    (h3 : (3 : ZMod p) ≠ 0) (hv : (v 0 : ZMod p) ≠ 0) (d : ℕ) :
    Finite ((fourNormDegree p v) ⁻¹' {d}) := by
  letI := (four_norm_shell_finite d).fintype
  apply Finite.of_injective (fun x : (fourNormDegree p v) ⁻¹' {d} =>
    (⟨fourDualPoint p v x,fourNormDegree_norm p v d x⟩ :
      {w : Fin 4 → ℤ | (∑ i, w i*w i)=(d : ℤ)}))
  intro x y h
  apply Subtype.ext
  exact fourDualPoint_injective v h3 hv (congrArg Subtype.val h)

end Ramanujan.MultiQuintuple
