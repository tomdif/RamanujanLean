import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Real diagonal operators on square-summable amplitudes

Multiplication by an arbitrary real function is defined on its maximal
square-summability domain. Finite-support vectors give density. Testing the
adjoint against single-coordinate vectors identifies its domain and action,
and proves self-adjointness as an equality of partially defined operators.
-/

set_option autoImplicit false
noncomputable section

namespace HilbertDiagonal

open scoped Classical ComplexConjugate

abbrev Space (ι : Type*) := lp (fun _ : ι => ℂ) 2

variable {ι : Type*}

def domain (w : ι → ℝ) : Submodule ℂ (Space ι) where
  carrier := {x | Memℓp (fun i => (w i : ℂ) * x i) 2}
  zero_mem' := by
    change Memℓp (fun i => (w i : ℂ) * 0) 2
    simpa using (zero_memℓp : Memℓp (0 : ι → ℂ) 2)
  add_mem' {x y} hx hy := by
    change Memℓp (fun i => (w i : ℂ) * (x i + y i)) 2
    have h : Memℓp (fun i => (w i : ℂ) * x i + (w i : ℂ) * y i) 2 := hx.add hy
    simpa only [mul_add] using h
  smul_mem' c x hx := by
    simpa [lp.coeFn_smul, smul_eq_mul, mul_left_comm] using hx.const_smul c

def operator (w : ι → ℝ) : Space ι →ₗ.[ℂ] Space ι where
  domain := domain w
  toFun :=
    { toFun := fun x => ⟨fun i => (w i : ℂ) * x.1 i, x.2⟩
      map_add' := by
        intro x y; ext i
        change (w i : ℂ) * (x.1 i + y.1 i) = (w i : ℂ) * x.1 i + (w i : ℂ) * y.1 i
        ring
      map_smul' := by
        intro c x; ext i
        change (w i : ℂ) * (c * x.1 i) = c * ((w i : ℂ) * x.1 i)
        ring }

@[simp] theorem operator_apply (w : ι → ℝ) (x : (operator w).domain) (i : ι) :
    operator w x i = (w i : ℂ) * x.1 i := rfl

theorem mem_domain_iff (w : ι → ℝ) (x : Space ι) :
    x ∈ (operator w).domain ↔ Summable (fun i => ‖(w i : ℂ) * x i‖ ^ 2) := by
  change Memℓp _ 2 ↔ _
  simpa using (memℓp_gen_iff (p := 2) (f := fun i => (w i : ℂ) * x i) (by norm_num))

theorem single_mem_domain (w : ι → ℝ) (i : ι) (c : ℂ) :
    lp.single 2 i c ∈ (operator w).domain := by
  classical
  change Memℓp (fun j => (w j : ℂ) * (lp.single 2 i c : Space ι) j) 2
  have h : (fun j => (w j : ℂ) * (lp.single 2 i c : Space ι) j) =
      (lp.single 2 i ((w i : ℂ) * c) : Space ι) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [lp.single_apply, Pi.single_eq_of_ne hj]
  rw [h]
  exact lp.memℓp _

theorem operator_single (w : ι → ℝ) (i : ι) (c : ℂ) :
    operator w ⟨lp.single 2 i c, single_mem_domain w i c⟩ =
      lp.single 2 i ((w i : ℂ) * c) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne hj]

theorem domain_dense (w : ι → ℝ) : Dense ((operator w).domain : Set (Space ι)) := by
  classical
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
  exact Filter.Eventually.of_forall fun s =>
    (operator w).domain.sum_mem (fun i _ => single_mem_domain w i (x i))

theorem formal_self_adjoint (w : ι → ℝ) :
    (operator w).IsFormalAdjoint (operator w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp [RCLike.inner_apply, mul_assoc, mul_left_comm]

/-- The adjoint's coordinate formula is forced by testing against single-coordinate states. -/
theorem adjoint_apply (w : ι → ℝ) (y : (operator w).adjoint.domain) (i : ι) :
    (operator w).adjoint y i = (w i : ℂ) * y.1 i := by
  classical
  have h := LinearPMap.adjoint_isFormalAdjoint (domain_dense w) y
    ⟨lp.single 2 i 1, single_mem_domain w i 1⟩
  change inner ℂ ((operator w).adjoint y) (lp.single 2 i 1) =
    inner ℂ y.1 (operator w ⟨lp.single 2 i 1, single_mem_domain w i 1⟩) at h
  rw [operator_single, lp.inner_single_right, lp.inner_single_right] at h
  simpa [RCLike.inner_apply, mul_comm] using congrArg star h

theorem adjoint_domain_le (w : ι → ℝ) : (operator w).adjoint.domain ≤ (operator w).domain := by
  intro x hx
  change Memℓp (fun i => (w i : ℂ) * x i) 2
  have h : (fun i => (w i : ℂ) * x i) = (operator w).adjoint ⟨x, hx⟩ := by
    funext i
    exact (adjoint_apply w ⟨x, hx⟩ i).symm
  rw [h]
  exact lp.memℓp _

theorem self_adjoint (w : ι → ℝ) : IsSelfAdjoint (operator w) := by
  have hle : operator w ≤ (operator w).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint (domain_dense w) (formal_self_adjoint w)
  exact (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 (adjoint_domain_le w))).symm

theorem adjoint_domain_eq (w : ι → ℝ) : (operator w).adjoint.domain = (operator w).domain :=
  congrArg LinearPMap.domain (self_adjoint w)

theorem closed (w : ι → ℝ) : (operator w).IsClosed := (self_adjoint w).isClosed

end HilbertDiagonal
