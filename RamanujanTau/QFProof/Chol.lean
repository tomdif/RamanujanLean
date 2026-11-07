/-
# The explicit local LDLᵀ of the Rankin–Selberg kernel (pure algebra, unconditional)

Let `μ` satisfy `μ₀ = 0`, `μ₁ = 1`, `μ_{k+2} = l μ_{k+1} − μ_k` (so `λ_k = μ_{k+1}`), and put
`ρ_0 = 1`, `ρ_k = (μ_{k+1} − Xμ_{k−1})/(1+X)` (this is `ρ_p(k)` with `X = 1/p`: `QFProof.Local`).
The local kernel is `K(a, a+n) = X^{a+n} ρ_n`. With `q = (1+X)² − X l²`,

    W₀ = 1,   W₁ = Xq/(1+X)²,   W_e = X^e (1−X) q/(1+X)   (e ≥ 2),

**`chol_loc`**: `X^{a+n} ρ_n = X^{2a+n} ρ_a ρ_{a+n} + Σ_{i<a} W_{a−i} X^{n+2i} λ_i λ_{i+n}`,

i.e. `K(a,b) = Σ_{e≤min(a,b)} W_e L(a,e) L(b,e)` with `L(a,0) = X^a ρ_a`, `L(a,e) = X^{a−e} λ_{a−e}`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.QFProof

open Finset

section Chol

variable (l X : ℝ) (μ : ℕ → ℝ)

/-- `ρ_k` in `μ`-notation. -/
noncomputable def rr (k : ℕ) : ℝ := if k = 0 then 1 else (μ (k + 1) - X * μ (k - 1)) / (1 + X)

/-- `q = (1+X)² − X l²`. -/
noncomputable def qq : ℝ := (1 + X) ^ 2 - X * l ^ 2

/-- The pivots `W_e`. -/
noncomputable def Wc : ℕ → ℝ
  | 0 => 1
  | 1 => X * qq l X / (1 + X) ^ 2
  | (e + 2) => X ^ (e + 2) * ((1 - X) * qq l X / (1 + X))

lemma Wc_succ_sub {e : ℕ} (he : 2 ≤ e) : Wc l X (e + 1) - X * Wc l X e = 0 := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
  simp only [Wc]
  ring

lemma rr_succ (k : ℕ) : rr X μ (k + 1) = (μ (k + 2) - X * μ k) / (1 + X) := by
  simp [rr]

lemma rr_zero : rr X μ 0 = 1 := by simp [rr]

lemma step0 (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n : ℕ) :
    X ^ (n + 2) * rr X μ 1 * rr X μ (n + 1) - X ^ (n + 1) * rr X μ n +
      Wc l X 1 * X ^ n * μ 1 * μ (n + 1) = 0 := by
  have h2 : μ 2 = l := by rw [hrec 0, hμ0, hμ1]; ring
  have r1 : rr X μ 1 = l / (1 + X) := by rw [rr_succ, h2, hμ0]; ring
  simp only [Wc, qq]
  rcases n with _ | m
  · rw [r1, rr_zero, hμ1, zero_add]
    field_simp
    ring
  · rw [r1, rr_succ, rr_succ, show m + 1 + 2 = (m + 1) + 2 by ring, hrec (m + 1), hrec m, hμ1]
    field_simp
    ring

lemma stepc (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k) (hX : 1 + X ≠ 0) (c n : ℕ) :
    X ^ (n + 2 * c + 4) * rr X μ (c + 2) * rr X μ (c + n + 2) -
      X ^ (n + 2 * c + 3) * rr X μ (c + 1) * rr X μ (c + n + 1) +
      (Wc l X 2 - X * Wc l X 1) * (X ^ (n + 2 * c) * μ (c + 1) * μ (c + n + 1)) +
      Wc l X 1 * (X ^ (n + 2 * c + 2) * μ (c + 2) * μ (c + n + 2)) = 0 := by
  rw [show c + 2 = (c + 1) + 1 by ring, rr_succ, rr_succ, show c + n + 2 = (c + n + 1) + 1 by ring,
    rr_succ, rr_succ]
  rw [show c + 1 + 2 = (c + 1) + 2 by ring, hrec (c + 1), show c + n + 1 + 2 = (c + n + 1) + 2 by ring,
    hrec (c + n + 1), show c + 1 + 1 = c + 2 by ring, show c + n + 1 + 1 = c + n + 2 by ring,
    hrec c, hrec (c + n)]
  simp only [Wc, qq]
  field_simp
  ring

theorem chol_loc (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n a : ℕ) :
    X ^ (a + n) * rr X μ n = X ^ (2 * a + n) * rr X μ a * rr X μ (a + n) +
      ∑ i ∈ range a, Wc l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) := by
  induction a with
  | zero => simp [rr]
  | succ a ih =>
    set T : ℕ → ℝ := fun i => X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) with hT
    have hsum : ∑ i ∈ range (a + 1), Wc l X (a + 1 - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) =
        X * ∑ i ∈ range a, Wc l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) +
        ∑ i ∈ range a, (Wc l X (a - i + 1) - X * Wc l X (a - i)) * T i + Wc l X 1 * T a := by
      rw [sum_range_succ, show a + 1 - a = 1 by omega, mul_sum, ← sum_add_distrib]
      congr 1
      swap
      · rw [hT]; ring
      refine sum_congr rfl fun i hi => ?_
      have hia : i < a := mem_range.1 hi
      rw [show a + 1 - i = a - i + 1 by omega, hT]
      ring
    have hcorr : ∑ i ∈ range a, (Wc l X (a - i + 1) - X * Wc l X (a - i)) * T i =
        if a = 0 then 0 else (Wc l X 2 - X * Wc l X 1) * T (a - 1) := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0; simp
      · rw [if_neg hpos.ne']
        rw [sum_eq_single (a - 1)]
        · rw [show a - (a - 1) = 1 by omega]
        · intro i hi hne
          have hia : i < a := mem_range.1 hi
          rw [Wc_succ_sub l X (by omega : 2 ≤ a - i), zero_mul]
        · intro h; exact absurd (mem_range.2 (by omega)) h
    have hS : ∑ i ∈ range a, Wc l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) =
        X ^ (a + n) * rr X μ n - X ^ (2 * a + n) * rr X μ a * rr X μ (a + n) := by linarith [ih]
    rw [hsum, hcorr, hS]
    simp only [hT]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp only [if_true, add_zero, Nat.zero_add, mul_zero, rr_zero, show 1 + n = n + 1 by ring]
      linear_combination (-1 : ℝ) * (step0 l X μ hμ0 hμ1 hrec hX n)
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      rw [if_neg (by omega), show c + 1 - 1 = c by omega]
      have h := stepc l X μ hrec hX c n
      rw [show c + 1 + 1 = c + 2 by ring, show c + 1 + 1 + n = c + n + 2 by ring,
        show c + 1 + n = c + n + 1 by ring]
      simp only [show c + n + 1 + 1 = c + n + 2 by ring]
      linear_combination (-1 : ℝ) * h

end Chol

end RamanujanTau.QFProof
