/-
# The integral-equation identity for logarithmic means (real-variable Selberg–Delange, step 1)

For real arithmetic functions `f`, `Λf` with `f(n) log n = (Λf ∗ f)(n)`, put

* `S(x) = Σ_{n≤x} f(n)/n`, `I(x) = Σ_{n≤x} (f(n)/n) log(x/n)`,
* `M(y) = Σ_{m≤y} Λf(m)/m`, `E(y) = M(y) − κ log y − c₀`,
* `R(x) = Σ_{n≤x} (f(n)/n) E(x/n)`.

**Identity** (`key_identity`): for `x ≥ 1`, `(log x − c₀) S(x) = (1+κ) I(x) + R(x)`.

Proof: `Σ_{n≤x} f(n) log n / n = Σ_{k≤x} (f(k)/k) M(x/k)` (Dirichlet hyperbola swap,
Mathlib's `sum_Ioc_mul_eq_sum_sum`), and `Σ f(n) log n/n = S log x − I`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange2

open Finset ArithmeticFunction

/-- `S(x) = Σ_{n≤x} f(n)/n`. -/
noncomputable def Ssum (f : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n

/-- `I(x) = Σ_{n≤x} (f(n)/n) log(x/n)`. -/
noncomputable def Isum (f : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n * Real.log (x / n)

/-- `M(y) = Σ_{m≤y} Λf(m)/m`. -/
noncomputable def Msum (g : ℕ → ℝ) (y : ℝ) : ℝ := ∑ m ∈ Ioc 0 ⌊y⌋₊, g m / m

/-- `E(y) = M(y) − κ log y − c₀`. -/
noncomputable def Err (g : ℕ → ℝ) (κ c₀ : ℝ) (y : ℝ) : ℝ := Msum g y - κ * Real.log y - c₀

/-- `R(x) = Σ_{n≤x} (f(n)/n) E(x/n)`. -/
noncomputable def Rsum (f g : ℕ → ℝ) (κ c₀ : ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n * Err g κ c₀ (x / n)

/-- The arithmetic function `n ↦ a(n)/n`. -/
noncomputable def divN (a : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => a n / n, by simp⟩

lemma divN_apply (a : ℕ → ℝ) (n : ℕ) : divN a n = a n / n := rfl

lemma divN_mul (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (divN g * divN f) n = (g * f) n / n := by
  rw [mul_apply, mul_apply, sum_div]
  refine sum_congr rfl fun p hp => ?_
  have hpn := (Nat.mem_divisorsAntidiagonal.1 hp).1
  rw [divN_apply, divN_apply, ← hpn]
  push_cast
  rcases eq_or_ne (p.1 : ℝ) 0 with h1 | h1
  · simp [h1]
  rcases eq_or_ne (p.2 : ℝ) 0 with h2 | h2
  · simp [h2]
  field_simp

/-- `Σ_{n≤N} (Λf ∗ f)(n)/n = Σ_{k≤N} (f(k)/k) Σ_{m≤N/k} Λf(m)/m`. -/
lemma swap_sum (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (g * f) n / n = ∑ k ∈ Ioc 0 N, f k / k * ∑ m ∈ Ioc 0 (N / k), g m / m := by
  have h := sum_Ioc_mul_eq_sum_sum (divN f) (divN g) N
  rw [mul_comm (divN f) (divN g)] at h
  simp only [divN_mul, divN_apply] at h
  exact h

lemma Msum_div (g : ℕ → ℝ) {x : ℝ} (k : ℕ) : Msum g (x / k) = ∑ m ∈ Ioc 0 (⌊x⌋₊ / k), g m / m := by
  rw [Msum, Nat.floor_div_natCast]

/-- **The key identity** `(log x − c₀) S(x) = (1+κ) I(x) + R(x)`. -/
theorem key_identity (f g : ArithmeticFunction ℝ) (hconv : ∀ n : ℕ, 0 < n → f n * Real.log n = (g * f) n)
    (κ c₀ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x - c₀) * Ssum f x = (1 + κ) * Isum f x + Rsum f g κ c₀ x := by
  have hx0 : 0 < x := by linarith
  -- Σ f(n) log n / n via the convolution
  have h1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, f n * Real.log n / n =
      ∑ k ∈ Ioc 0 ⌊x⌋₊, f k / k * Msum g (x / k) := by
    simp_rw [Msum_div]
    rw [← swap_sum f g ⌊x⌋₊]
    refine sum_congr rfl fun n hn => ?_
    rw [hconv n (mem_Ioc.1 hn).1]
  -- log n = log x − log(x/n)
  have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, f n * Real.log n / n = Real.log x * Ssum f x - Isum f x := by
    rw [Ssum, Isum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    rw [Real.log_div hx0.ne' hn0.ne']
    ring
  -- expand M = κ log + c₀ + E
  have h3 : ∑ k ∈ Ioc 0 ⌊x⌋₊, f k / k * Msum g (x / k) =
      κ * Isum f x + c₀ * Ssum f x + Rsum f g κ c₀ x := by
    rw [Isum, Ssum, Rsum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [Err]; ring
  rw [h2, h3] at h1
  linarith

end RamanujanTau.SelbergDelange2
