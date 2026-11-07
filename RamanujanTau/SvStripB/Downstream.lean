/-
# The form of the `J_z` bound used by step 4 of `docs/SKQF_PROOF.md` §4 (level 1)

Step 4 writes `y_d = (log y)^{−2} Σ_{u₁,u₂≤y} Γ^z_d(u₁,u₂) J_z(y/u₁) J_0(y/u₂)`.  For `u ≤ y`,
`log(y/u) ≤ log y`, so (`Jz_div_bound`)

    |J_z(y/u)| ≤ K √(1+log y) (1 + |Re z| log y) y^{2|Im z|},     |J_0(y/u)| ≤ K √(1+log y),

and hence (`yd_bound`) for any complex kernel `Γ`,

    |(log y)^{−2} Σ Γ(u₁,u₂) J_z(y/u₁) J_0(y/u₂)|
        ≤ K² (1+log y)(1 + |Re z| log y) y^{2|Im z|} (log y)^{−2} Σ |Γ(u₁,u₂)|.

This is the complex analogue of `QFProof.abs_yv_le`: the only change is the factor
`(1 + |Re z| log y) y^{2|Im z|}`, which is linear in `|Re z| log y` (the hypothesis `SvStripHyp`
allows degree 2) and contributes `2t` to the exponent `c'`.
-/
import RamanujanTau.SvStripB.JTwist

set_option autoImplicit false

namespace RamanujanTau.SvStripB

open Finset Complex

/-- `J_z(y/u)` for `0 < u ≤ y`, bounded uniformly in `u`. -/
theorem Jz_div_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ∀ y : ℕ, ∀ u ∈ Ioc 0 y,
    ‖Jz z ((y : ℝ) / u)‖ ≤ K * Real.sqrt (1 + Real.log y) * (1 + |z.re| * Real.log y) *
      Real.exp (2 * |z.im| * Real.log y) := by
  obtain ⟨K, hK, h⟩ := Jz_bound_re
  refine ⟨K, hK, fun z y u hu => ?_⟩
  have h1 := mem_Ioc.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast h1.1
  have hyu : (u : ℝ) ≤ y := by exact_mod_cast h1.2
  have hx1 : 1 ≤ (y : ℝ) / u := by rw [le_div_iff₀ hu0]; linarith
  have hl : Real.log ((y : ℝ) / u) ≤ Real.log y :=
    Real.log_le_log (by linarith) (div_le_self (by linarith) (by exact_mod_cast h1.1))
  have hl0 : 0 ≤ Real.log ((y : ℝ) / u) := Real.log_nonneg hx1
  refine (h z _ hx1).trans ?_
  gcongr

/-- `J_0(y/u) ≤ K √(1+log y)`. -/
lemma J0_div_bound {K : ℝ}
    (h : ∀ z : ℂ, ∀ y : ℕ, ∀ u ∈ Ioc 0 y, ‖Jz z ((y : ℝ) / u)‖ ≤ K * Real.sqrt (1 + Real.log y) *
      (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y))
    (y : ℕ) (u : ℕ) (hu : u ∈ Ioc 0 y) : ‖Jz 0 ((y : ℝ) / u)‖ ≤ K * Real.sqrt (1 + Real.log y) := by
  simpa using h 0 y u hu

/-- **The bilinear `y_d` bound** (step 4 of §4, `J`-side): for every complex kernel `Γ`,
`|Σ_{u₁,u₂≤y} Γ(u₁,u₂) J_z(y/u₁) J_0(y/u₂)| ≤ K (1+log y)(1+|Re z| log y) y^{2|Im z|} Σ|Γ|`. -/
theorem yd_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (Γ : ℕ → ℕ → ℂ) (z : ℂ) (y : ℕ), 1 ≤ y →
    ‖∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Jz z ((y : ℝ) / u₁) * Jz 0 ((y : ℝ) / u₂)‖ ≤
      K * (1 + Real.log y) * (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y) *
        ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖Γ u₁ u₂‖ := by
  obtain ⟨K, hK, h⟩ := Jz_div_bound
  refine ⟨K ^ 2, by positivity, fun Γ z y hy => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hL0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  set s := Real.sqrt (1 + Real.log y) with hs
  have hss : s * s = 1 + Real.log y := Real.mul_self_sqrt (by linarith)
  set B := (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y) with hB
  have hB0 : 0 ≤ B := by positivity
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun u₁ hu₁ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun u₂ hu₂ => ?_)
  rw [norm_mul, norm_mul]
  have h1 := h z y u₁ hu₁
  have h2 := J0_div_bound h y u₂ hu₂
  calc ‖Γ u₁ u₂‖ * ‖Jz z ((y : ℝ) / u₁)‖ * ‖Jz 0 ((y : ℝ) / u₂)‖
      ≤ ‖Γ u₁ u₂‖ * (K * s * (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y)) *
          (K * s) := by gcongr
    _ = K ^ 2 * (s * s) * (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y) *
          ‖Γ u₁ u₂‖ := by ring
    _ = _ := by rw [hss]

/-- The same with the `(log y)^{−2}` normalisation of `y_d`. -/
theorem yd_bound_div : ∃ K : ℝ, 0 ≤ K ∧ ∀ (Γ : ℕ → ℕ → ℂ) (z : ℂ) (y : ℕ), 1 ≤ y →
    ‖(∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Jz z ((y : ℝ) / u₁) * Jz 0 ((y : ℝ) / u₂)) /
        (Real.log y : ℂ) ^ 2‖ ≤
      K * (1 + Real.log y) * (1 + |z.re| * Real.log y) * Real.exp (2 * |z.im| * Real.log y) /
        Real.log y ^ 2 * ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖Γ u₁ u₂‖ := by
  obtain ⟨K, hK, h⟩ := yd_bound
  refine ⟨K, hK, fun Γ z y hy => ?_⟩
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (h Γ z y hy) (sq_nonneg _)

/-- **Holomorphy** of the `y_d` bilinear sum in `z`, for a kernel `Γ^z` holomorphic in `z`
(the bound `yd_bound` is uniform in the kernel, so it applies to `Γ^z` for each `z`). -/
theorem yd_holo (Γ : ℂ → ℕ → ℕ → ℂ) (hΓ : ∀ u₁ u₂, Differentiable ℂ (fun z : ℂ => Γ z u₁ u₂))
    (y : ℕ) : Differentiable ℂ (fun z => ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y,
      Γ z u₁ u₂ * Jz z ((y : ℝ) / u₁) * Jz 0 ((y : ℝ) / u₂)) := by
  refine Differentiable.fun_sum fun u₁ _ => Differentiable.fun_sum fun u₂ _ => ?_
  exact ((hΓ u₁ u₂).mul (Jz_differentiable _)).mul (differentiable_const _)

end RamanujanTau.SvStripB
