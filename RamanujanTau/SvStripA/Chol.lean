/-
# `SvStripA` step 2a: the local LDLᵀ over an arbitrary field (in particular `ℂ`)

A field-generic copy of `QFProof.Chol` (which is stated over `ℝ`).  Let `μ` satisfy `μ₀ = 0`,
`μ₁ = 1`, `μ_{k+2} = l μ_{k+1} − μ_k`, put `ρ_0 = 1`, `ρ_k = (μ_{k+1} − Xμ_{k−1})/(1+X)` and
`q = (1+X)² − X l²`, `W₀ = 1`, `W₁ = Xq/(1+X)²`, `W_e = X^e (1−X) q/(1+X)` (`e ≥ 2`).

**`cholK`**: `X^{a+n} ρ_n = X^{2a+n} ρ_a ρ_{a+n} + Σ_{i<a} W_{a−i} X^{n+2i} μ_{i+1} μ_{i+n+1}`
whenever `1 + X ≠ 0`.  With `X = p^{−s}` (`s` complex) this is the local Cholesky factorization
of the `s`-twisted Rankin–Selberg kernel.  Pure algebra; level 1.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SvStripA

open Finset

section Chol

variable {K : Type*} [Field K] (l X : K) (μ : ℕ → K)

/-- `ρ_k` in `μ`-notation. -/
def rrK (k : ℕ) : K := if k = 0 then 1 else (μ (k + 1) - X * μ (k - 1)) / (1 + X)

/-- `q = (1+X)² − X l²`. -/
def qqK : K := (1 + X) ^ 2 - X * l ^ 2

/-- The pivots `W_e`. -/
def WcK : ℕ → K
  | 0 => 1
  | 1 => X * qqK l X / (1 + X) ^ 2
  | (e + 2) => X ^ (e + 2) * ((1 - X) * qqK l X / (1 + X))

lemma WcK_succ_sub {e : ℕ} (he : 2 ≤ e) : WcK l X (e + 1) - X * WcK l X e = 0 := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
  simp only [WcK]
  ring

lemma rrK_succ (k : ℕ) : rrK X μ (k + 1) = (μ (k + 2) - X * μ k) / (1 + X) := by
  simp [rrK]

lemma rrK_zero : rrK X μ 0 = 1 := by simp [rrK]

lemma stepK0 (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n : ℕ) :
    X ^ (n + 2) * rrK X μ 1 * rrK X μ (n + 1) - X ^ (n + 1) * rrK X μ n +
      WcK l X 1 * X ^ n * μ 1 * μ (n + 1) = 0 := by
  have h2 : μ 2 = l := by rw [hrec 0, hμ0, hμ1]; ring
  have r1 : rrK X μ 1 = l / (1 + X) := by rw [rrK_succ, h2, hμ0]; ring
  simp only [WcK, qqK]
  rcases n with _ | m
  · rw [r1, rrK_zero, hμ1, zero_add]
    field_simp
    ring
  · rw [r1, rrK_succ, rrK_succ, show m + 1 + 2 = (m + 1) + 2 by ring, hrec (m + 1), hrec m, hμ1]
    field_simp
    ring

lemma stepKc (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k) (hX : 1 + X ≠ 0) (c n : ℕ) :
    X ^ (n + 2 * c + 4) * rrK X μ (c + 2) * rrK X μ (c + n + 2) -
      X ^ (n + 2 * c + 3) * rrK X μ (c + 1) * rrK X μ (c + n + 1) +
      (WcK l X 2 - X * WcK l X 1) * (X ^ (n + 2 * c) * μ (c + 1) * μ (c + n + 1)) +
      WcK l X 1 * (X ^ (n + 2 * c + 2) * μ (c + 2) * μ (c + n + 2)) = 0 := by
  rw [show c + 2 = (c + 1) + 1 by ring, rrK_succ, rrK_succ, show c + n + 2 = (c + n + 1) + 1 by ring,
    rrK_succ, rrK_succ]
  rw [show c + 1 + 2 = (c + 1) + 2 by ring, hrec (c + 1), show c + n + 1 + 2 = (c + n + 1) + 2 by ring,
    hrec (c + n + 1), show c + 1 + 1 = c + 2 by ring, show c + n + 1 + 1 = c + n + 2 by ring,
    hrec c, hrec (c + n)]
  simp only [WcK, qqK]
  field_simp
  ring

/-- **The local LDLᵀ over any field.** -/
theorem cholK (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n a : ℕ) :
    X ^ (a + n) * rrK X μ n = X ^ (2 * a + n) * rrK X μ a * rrK X μ (a + n) +
      ∑ i ∈ range a, WcK l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) := by
  induction a with
  | zero => simp [rrK]
  | succ a ih =>
    set T : ℕ → K := fun i => X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) with hT
    have hsum : ∑ i ∈ range (a + 1), WcK l X (a + 1 - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) =
        X * ∑ i ∈ range a, WcK l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) +
        ∑ i ∈ range a, (WcK l X (a - i + 1) - X * WcK l X (a - i)) * T i + WcK l X 1 * T a := by
      rw [sum_range_succ, show a + 1 - a = 1 by omega, mul_sum, ← sum_add_distrib]
      congr 1
      swap
      · rw [hT]; ring
      refine sum_congr rfl fun i hi => ?_
      have hia : i < a := mem_range.1 hi
      rw [show a + 1 - i = a - i + 1 by omega, hT]
      ring
    have hcorr : ∑ i ∈ range a, (WcK l X (a - i + 1) - X * WcK l X (a - i)) * T i =
        if a = 0 then 0 else (WcK l X 2 - X * WcK l X 1) * T (a - 1) := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0; simp
      · rw [if_neg hpos.ne']
        rw [sum_eq_single (a - 1)]
        · rw [show a - (a - 1) = 1 by omega]
        · intro i hi hne
          have hia : i < a := mem_range.1 hi
          rw [WcK_succ_sub l X (by omega : 2 ≤ a - i), zero_mul]
        · intro h; exact absurd (mem_range.2 (by omega)) h
    have hS : ∑ i ∈ range a, WcK l X (a - i) * X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) =
        X ^ (a + n) * rrK X μ n - X ^ (2 * a + n) * rrK X μ a * rrK X μ (a + n) := by
      rw [ih]; ring
    rw [hsum, hcorr, hS]
    simp only [hT]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp only [if_true, add_zero, Nat.zero_add, mul_zero, rrK_zero, show 1 + n = n + 1 by ring]
      linear_combination (-1 : K) * (stepK0 l X μ hμ0 hμ1 hrec hX n)
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      rw [if_neg (by omega), show c + 1 - 1 = c by omega]
      have h := stepKc l X μ hrec hX c n
      rw [show c + 1 + 1 = c + 2 by ring, show c + 1 + 1 + n = c + n + 2 by ring,
        show c + 1 + n = c + n + 1 by ring]
      simp only [show c + n + 1 + 1 = c + n + 2 by ring]
      linear_combination (-1 : K) * h

end Chol

end RamanujanTau.SvStripA
