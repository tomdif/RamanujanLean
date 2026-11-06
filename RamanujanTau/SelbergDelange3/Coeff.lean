/-
# The arithmetic function with prescribed von Mangoldt function

For `g : ℕ → ℝ` with `g 0 = g 1 = 0` define `recF g` by `recF g 1 = 1` and
`recF g n = (Σ_{d | n, d < n} g(n/d) recF g (d)) / log n` (`n ≥ 2`).  Then

* `recF_log`: `recF g n · log n = (g ∗ recF g)(n)` for `n ≥ 1` (so `g = Λ_{recF g}`);
* `abs_recF_le`: `|recF g n| ≤ recF |g| n` (the majorant), and `recF |g| ≥ 0`.

For `g = −ΛR/2` (`ΛR` the von Mangoldt function of `R(s) = Σ λ(n)² n^{−s}`), `recF g` is the
coefficient sequence of `R(s)^{−1/2}` (`−F'/F = −½ R'/R`, `F(1) = 1`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset ArithmeticFunction

/-- The function with von Mangoldt function `g`. -/
noncomputable def recF (g : ℕ → ℝ) : ℕ → ℝ
  | n => if n = 0 then 0 else if n = 1 then 1 else
      (∑ d ∈ n.properDivisors.attach, g (n / d.1) * recF g d.1) / Real.log n
termination_by n => n
decreasing_by exact (Nat.mem_properDivisors.1 d.2).2

lemma recF_eq (g : ℕ → ℝ) (n : ℕ) : recF g n = if n = 0 then 0 else if n = 1 then 1 else
    (∑ d ∈ n.properDivisors, g (n / d) * recF g d) / Real.log n := by
  rw [recF]
  split_ifs <;> try rfl
  rw [sum_attach n.properDivisors (fun d => g (n / d) * recF g d)]

lemma recF_zero (g : ℕ → ℝ) : recF g 0 = 0 := by rw [recF_eq]; simp

lemma recF_one (g : ℕ → ℝ) : recF g 1 = 1 := by rw [recF_eq]; simp

/-- As an arithmetic function. -/
noncomputable def recFA (g : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨recF g, recF_zero g⟩

/-- `g` as an arithmetic function (requires `g 0 = 0`). -/
noncomputable def toA (g : ℕ → ℝ) (h0 : g 0 = 0) : ArithmeticFunction ℝ := ⟨g, h0⟩

lemma conv_eq (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) {n : ℕ} (hn : n ≠ 0) :
    (toA g h0 * recFA g) n = ∑ d ∈ n.properDivisors, g (n / d) * recF g d := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (f := fun a b => toA g h0 a * recFA g b)]
  rw [← Nat.insert_self_properDivisors hn, sum_insert Nat.self_notMem_properDivisors]
  simp only [toA, recFA, coe_mk, Nat.div_self (Nat.pos_of_ne_zero hn), h1, zero_mul, zero_add]

/-- **`recF g · log = g ∗ recF g`.** -/
theorem recF_log (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) (n : ℕ) (hn : 0 < n) :
    recFA g n * Real.log n = (toA g h0 * recFA g) n := by
  rw [conv_eq g h0 h1 hn.ne']
  show recF g n * Real.log n = _
  rcases eq_or_ne n 1 with rfl | h1n
  · simp [Nat.properDivisors_one]
  have hl : Real.log n ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact (Real.log_pos this).ne'
  rw [recF_eq, if_neg hn.ne', if_neg h1n, div_mul_cancel₀ _ hl]

/-- The majorant is non-negative and dominates. -/
theorem abs_recF_le (g : ℕ → ℝ) (n : ℕ) :
    0 ≤ recF (fun m => |g m|) n ∧ |recF g n| ≤ recF (fun m => |g m|) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [recF_eq g, recF_eq (fun m => |g m|)]
    split_ifs with h0 h1
    · simp
    · simp
    · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hd : ∀ d ∈ n.properDivisors, d < n := fun d hd => (Nat.mem_properDivisors.1 hd).2
      constructor
      · exact div_nonneg (sum_nonneg fun d hdm => mul_nonneg (abs_nonneg _) (ih d (hd d hdm)).1) hl.le
      · rw [abs_div, abs_of_pos hl]
        gcongr
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd' => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ih d (hd d hd')).2 (abs_nonneg _)

end RamanujanTau.SelbergDelange3
