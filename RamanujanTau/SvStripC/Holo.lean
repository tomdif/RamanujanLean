/-
# `SvStripC`: holomorphy of `Γ^z` and `y_d(z)` on `Im z > −1` (unconditional)
-/
import RamanujanTau.SvStripC.Ident

set_option autoImplicit false

namespace RamanujanTau.SvStripC

open Complex Finset
open RamanujanTau.SvStripA (Ω diff_UdC)
open RamanujanTau.SvStripB (Jz Jz_differentiable)

lemma diff_tw (m : ℕ) (hm : m ≠ 0) (w : ℂ → ℂ) {z : ℂ} (hw : DifferentiableAt ℂ w z) :
    DifferentiableAt ℂ (fun z => tw (w z) m) z := by
  unfold tw
  exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hm))

/-- **`z ↦ Γ^z_d(u₁,u₂)` is holomorphic on `Im z > −1`.** -/
theorem diff_Γz (d u₁ u₂ : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℂ (fun z => Γz z d u₁ u₂) z := by
  unfold Γz Gz Fiz
  refine DifferentiableAt.fun_sum fun v₁ hv₁ => DifferentiableAt.fun_sum fun v₂ hv₂ => ?_
  have hv₁0 : v₁ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₁)
  have hv₂0 : v₂ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₂)
  have hu₁ := Nat.mem_divisors.1 hv₁
  have hq : u₁ / v₁ ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hu₁.2) hu₁.1)
    (Nat.pos_of_ne_zero hv₁0))
  refine (((differentiableAt_const _).mul ((diff_tw v₂ hv₂0 (fun z => -z) (by fun_prop)).mul
    (diff_UdC _ _ hz))).mul ((differentiableAt_const _).mul
      (diff_tw _ hq (fun z => z) differentiableAt_id))).mul (differentiableAt_const _)

/-- `z ↦ YdJ y z d` is holomorphic on `Im z > −1`. -/
theorem diff_YdJ (y d : ℕ) {z : ℂ} (hz : z ∈ Ω) : DifferentiableAt ℂ (fun z => YdJ y z d) z := by
  unfold YdJ
  refine DifferentiableAt.div_const (DifferentiableAt.fun_sum fun u₁ _ =>
    DifferentiableAt.fun_sum fun u₂ _ => ?_) _
  exact ((diff_Γz d u₁ u₂ hz).mul ((Jz_differentiable _) z)).mul (differentiableAt_const _)

end RamanujanTau.SvStripC
