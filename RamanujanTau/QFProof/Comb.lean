/-
# Finite-sum combinatorics for the `Q⁰`, `Q¹` reduction

* `sum_antidiag_reindex`: `Σ_{n≤N} Σ_{uv=n} φ(u,v) = Σ_{u≤N} Σ_{v≤N/u} φ(u,v)`.
* `smooth_one`: for `b` arbitrary and `F = fR/n`,
  `Σ_{n≤y} log(y/n) (b ∗ F)(n) = Σ_{u≤y} b(u) J(y/u)`, `J = Isum fR`.
* `smooth_two`: the two-variable version
  `Σ_{n₁,n₂≤y} log(y/n₁)log(y/n₂) Σ_{u₁|n₁,u₂|n₂} Γ(u₁,u₂)F(n₁/u₁)F(n₂/u₂) = Σ_{u₁,u₂≤y} Γ(u₁,u₂)J(y/u₁)J(y/u₂)`.
-/
import RamanujanTau.QFProof.JBound

set_option autoImplicit false

namespace RamanujanTau.QFProof

open Finset
open RamanujanTau.SelbergDelange2 (Isum)
open RamanujanTau.SelbergDelange3 (fR)

/-- `F(m) = fR(m)/m`. -/
noncomputable def Fm (m : ℕ) : ℝ := fR m / m

lemma sum_antidiag_reindex (φ : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, φ x.1 x.2 =
      ∑ u ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / u), φ u m := by
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, φ x.1 x.2
  · refine sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  trans ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, φ x.1 x.2
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => (by simp_all)
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun n hn => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by lia)]
  · intro hm
    grw [hm]
    simp [Nat.mul_div_le, Nat.div_le_self]

lemma J_eq (y u : ℕ) :
    Isum fR ((y : ℝ) / u) = ∑ m ∈ Ioc 0 (y / u), Fm m * Real.log ((y : ℝ) / (u * m)) := by
  unfold Isum
  rw [Nat.floor_div_eq_div]
  refine sum_congr rfl fun m _ => ?_
  rw [Fm, div_div]

/-- One-variable smoothing identity. -/
lemma smooth_one (y : ℕ) (b : ℕ → ℝ) :
    ∑ n ∈ Ioc 0 y, Real.log ((y : ℝ) / n) * ∑ u ∈ n.divisors, b u * Fm (n / u) =
      ∑ u ∈ Ioc 0 y, b u * Isum fR ((y : ℝ) / u) := by
  have h1 : ∀ n ∈ Ioc 0 y, Real.log ((y : ℝ) / n) * ∑ u ∈ n.divisors, b u * Fm (n / u) =
      ∑ x ∈ n.divisorsAntidiagonal, b x.1 * (Fm x.2 * Real.log ((y : ℝ) / (x.1 * x.2))) := by
    intro n _
    rw [← Nat.sum_divisorsAntidiagonal (fun i j => b i * Fm j), mul_sum]
    refine sum_congr rfl fun x hx => ?_
    have := (Nat.mem_divisorsAntidiagonal.1 hx).1
    rw [← this]; push_cast; ring
  rw [sum_congr rfl h1, sum_antidiag_reindex (fun u m => b u * (Fm m * Real.log ((y : ℝ) / (u * m)))) y]
  refine sum_congr rfl fun u _ => ?_
  rw [J_eq, mul_sum]

/-- Two-variable smoothing identity. -/
lemma smooth_two (y : ℕ) (Γ : ℕ → ℕ → ℝ) :
    ∑ n₁ ∈ Ioc 0 y, ∑ n₂ ∈ Ioc 0 y, Real.log ((y : ℝ) / n₁) * Real.log ((y : ℝ) / n₂) *
      ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fm (n₁ / u₁) * Fm (n₂ / u₂) =
      ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Isum fR ((y : ℝ) / u₁) * Isum fR ((y : ℝ) / u₂) := by
  set B : ℕ → ℝ := fun u₁ => ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Isum fR ((y : ℝ) / u₂) with hB
  have hin : ∀ u₁, ∑ n₂ ∈ Ioc 0 y, Real.log ((y : ℝ) / n₂) *
      ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fm (n₂ / u₂) = B u₁ := fun u₁ => smooth_one y (Γ u₁)
  have step : ∀ n₁ ∈ Ioc 0 y, ∑ n₂ ∈ Ioc 0 y, Real.log ((y : ℝ) / n₁) * Real.log ((y : ℝ) / n₂) *
      ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fm (n₁ / u₁) * Fm (n₂ / u₂) =
      Real.log ((y : ℝ) / n₁) * ∑ u₁ ∈ n₁.divisors, B u₁ * Fm (n₁ / u₁) := by
    intro n₁ _
    simp_rw [← hin]
    calc _ = ∑ n₂ ∈ Ioc 0 y, ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors,
          Real.log ((y : ℝ) / n₁) * (Real.log ((y : ℝ) / n₂) * (Γ u₁ u₂ * Fm (n₂ / u₂)) * Fm (n₁ / u₁)) := by
          refine sum_congr rfl fun n₂ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun u₁ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun u₂ _ => ?_
          ring
      _ = ∑ u₁ ∈ n₁.divisors, ∑ n₂ ∈ Ioc 0 y, ∑ u₂ ∈ n₂.divisors,
          Real.log ((y : ℝ) / n₁) * (Real.log ((y : ℝ) / n₂) * (Γ u₁ u₂ * Fm (n₂ / u₂)) * Fm (n₁ / u₁)) :=
          sum_comm
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun u₁ _ => ?_
          rw [sum_mul, mul_sum]
          refine sum_congr rfl fun n₂ _ => ?_
          rw [mul_sum, sum_mul, mul_sum]
  rw [sum_congr rfl step, smooth_one y B]
  refine sum_congr rfl fun u₁ _ => ?_
  rw [hB, sum_mul]
  refine sum_congr rfl fun u₂ _ => ?_
  ring

end RamanujanTau.QFProof
