/-
# The `s`-derivative of the local LDLᵀ (pure algebra, unconditional)

Notation of `QFProof.Chol` (`μ`, `rr`, `Wc`), plus (all divided by `log p`)

* `rd n = X l μ_n/(1+X)²` (`= ρ'_p(n)/log p`, `QFProof2.rhoP'_succ`);
* `wd e = −X ∂_X W_e` (explicit).

**`dchol_loc`**: `X^{a+n} rd_n = X^{2a+n}((rd_a − a ρ_a)ρ_{a+n} + ρ_a rd_{a+n})
  + Σ_{i<a} (wd_{a−i} + (a−2i) W_{a−i}) X^{n+2i} λ_i λ_{i+n}`.
-/
import RamanujanTau.QFProof.Chol

set_option autoImplicit false

namespace RamanujanTau.QFProof3

open Finset RamanujanTau.QFProof

section DChol

variable (l X : ℝ) (μ : ℕ → ℝ)

/-- `ρ'/log p` in `μ`-notation. -/
noncomputable def rd (n : ℕ) : ℝ := X * l * μ n / (1 + X) ^ 2

/-- `q' = d q/dX`. -/
noncomputable def qd : ℝ := 2 * (1 + X) - l ^ 2

/-- `c = (1−X)q/(1+X)` and `c' = dc/dX`. -/
noncomputable def cc : ℝ := (1 - X) * qq l X / (1 + X)
noncomputable def ccd : ℝ :=
  (-qq l X + (1 - X) * qd l X) / (1 + X) - (1 - X) * qq l X / (1 + X) ^ 2

/-- `wd e = −X ∂_X W_e`. -/
noncomputable def wd : ℕ → ℝ
  | 0 => 0
  | 1 => -X * (qq l X / (1 + X) ^ 2 + X * qd l X / (1 + X) ^ 2 - 2 * X * qq l X / (1 + X) ^ 3)
  | (e + 2) => -(((e + 2 : ℕ) : ℝ) * X ^ (e + 2) * cc l X + X ^ (e + 3) * ccd l X)

lemma Wc_two_add (e : ℕ) : Wc l X (e + 2) = X ^ (e + 2) * cc l X := by simp [Wc, cc]

lemma wd_diff {e : ℕ} (he : 2 ≤ e) (r : ℝ) :
    (wd l X (e + 1) + (r + 1) * Wc l X (e + 1)) - X * (wd l X e + r * Wc l X e) = 0 := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
  rw [show f + 2 + 1 = (f + 1) + 2 by ring]
  simp only [wd, Wc_two_add]
  push_cast
  ring

variable {l X μ}

lemma dstep0 (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n : ℕ) :
    X ^ (n + 1) * rd l X μ n = X ^ (n + 2) * ((rd l X μ 1 - rr X μ 1) * rr X μ (n + 1) +
      rr X μ 1 * rd l X μ (n + 1)) + (wd l X 1 + Wc l X 1) * (X ^ n * μ (n + 1)) := by
  have h2 : μ 2 = l := by rw [hrec 0, hμ0, hμ1]; ring
  have r1 : rr X μ 1 = l / (1 + X) := by rw [rr_succ, h2, hμ0]; ring
  rcases n with _ | m
  · simp only [Nat.zero_add, r1, hμ0, hμ1, rd, wd, Wc, qq, qd]
    field_simp
    ring
  · rw [r1, rr_succ]
    simp only [rd, wd, Wc, qq, qd, hμ1, hrec (m + 1), show m + 1 + 1 = m + 2 from rfl, hrec m]
    field_simp
    ring

lemma dstepc (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k) (hX : 1 + X ≠ 0) (c n : ℕ) :
    X ^ (c + 1 + 1 + n) * rd l X μ n =
      X ^ (2 * (c + 1 + 1) + n) * ((rd l X μ (c + 2) - ((c : ℝ) + 2) * rr X μ (c + 2)) *
        rr X μ (c + n + 2) + rr X μ (c + 2) * rd l X μ (c + n + 2)) +
      X * (X ^ (c + 1 + n) * rd l X μ n) -
      X * (X ^ (2 * (c + 1) + n) * ((rd l X μ (c + 1) - ((c : ℝ) + 1) * rr X μ (c + 1)) *
        rr X μ (c + n + 1) + rr X μ (c + 1) * rd l X μ (c + n + 1))) +
      ((wd l X 2 + (2 - (c : ℝ)) * Wc l X 2) - X * (wd l X 1 + (1 - (c : ℝ)) * Wc l X 1)) *
        (X ^ (n + 2 * c) * μ (c + 1) * μ (c + n + 1)) +
      (wd l X 1 + (-(c : ℝ)) * Wc l X 1) * (X ^ (n + 2 * (c + 1)) * μ (c + 2) * μ (c + n + 2)) := by
  rw [show c + 2 = (c + 1) + 1 by ring, rr_succ, rr_succ, show c + n + 2 = (c + n + 1) + 1 by ring,
    rr_succ, rr_succ]
  rw [show c + 1 + 2 = (c + 1) + 2 by ring, hrec (c + 1), show c + n + 1 + 2 = (c + n + 1) + 2 by ring,
    hrec (c + n + 1), show c + 1 + 1 = c + 2 by ring, show c + n + 1 + 1 = c + n + 2 by ring,
    hrec c, hrec (c + n)]
  simp only [rd, wd, Wc, qq, qd, cc, ccd]
  rw [hrec c, hrec (c + n)]
  field_simp
  ring

theorem dchol_loc (hμ0 : μ 0 = 0) (hμ1 : μ 1 = 1) (hrec : ∀ k, μ (k + 2) = l * μ (k + 1) - μ k)
    (hX : 1 + X ≠ 0) (n a : ℕ) :
    X ^ (a + n) * rd l X μ n =
      X ^ (2 * a + n) * ((rd l X μ a - (a : ℝ) * rr X μ a) * rr X μ (a + n) + rr X μ a * rd l X μ (a + n)) +
      ∑ i ∈ range a, (wd l X (a - i) + ((a : ℝ) - 2 * i) * Wc l X (a - i)) *
        X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) := by
  induction a with
  | zero => simp [rd, rr, hμ0]
  | succ a ih =>
    set T : ℕ → ℝ := fun i => X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) with hT
    set A : ℕ → ℝ := fun i => wd l X (a - i) + ((a : ℝ) - 2 * i) * Wc l X (a - i) with hA
    have hsum : ∑ i ∈ range (a + 1), (wd l X (a + 1 - i) + (((a + 1 : ℕ) : ℝ) - 2 * i) * Wc l X (a + 1 - i)) *
        X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) =
        X * ∑ i ∈ range a, A i * T i +
        ∑ i ∈ range a, ((wd l X (a - i + 1) + (((a : ℝ) - 2 * i) + 1) * Wc l X (a - i + 1)) - X * A i) * T i +
        (wd l X 1 + ((1 : ℝ) - a) * Wc l X 1) * T a := by
      rw [sum_range_succ, show a + 1 - a = 1 by omega, mul_sum, ← sum_add_distrib]
      congr 1
      swap
      · rw [hT]; push_cast; ring
      refine sum_congr rfl fun i hi => ?_
      have hia : i < a := mem_range.1 hi
      rw [show a + 1 - i = a - i + 1 by omega, hT]
      push_cast; ring
    have hcorr : ∑ i ∈ range a, ((wd l X (a - i + 1) + (((a : ℝ) - 2 * i) + 1) * Wc l X (a - i + 1)) -
        X * A i) * T i =
        if a = 0 then 0 else ((wd l X 2 + (((a : ℝ) - 2 * (a - 1 : ℕ)) + 1) * Wc l X 2) -
          X * (wd l X 1 + ((a : ℝ) - 2 * (a - 1 : ℕ)) * Wc l X 1)) * T (a - 1) := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0; simp
      · rw [if_neg hpos.ne', sum_eq_single (a - 1)]
        · rw [show a - (a - 1) = 1 by omega, hA]
          simp only [show a - (a - 1) = 1 by omega]
        · intro i hi hne
          have hia : i < a := mem_range.1 hi
          rw [hA]
          simp only
          rw [wd_diff l X (by omega : 2 ≤ a - i), zero_mul]
        · intro h; exact absurd (mem_range.2 (by omega)) h
    have hS : ∑ i ∈ range a, A i * T i = X ^ (a + n) * rd l X μ n -
        X ^ (2 * a + n) * ((rd l X μ a - (a : ℝ) * rr X μ a) * rr X μ (a + n) +
          rr X μ a * rd l X μ (a + n)) := by
      have : ∑ i ∈ range a, A i * T i = ∑ i ∈ range a, (wd l X (a - i) + ((a : ℝ) - 2 * i) * Wc l X (a - i)) *
          X ^ (n + 2 * i) * μ (i + 1) * μ (i + n + 1) :=
        sum_congr rfl fun i _ => by rw [hA, hT]; ring
      rw [this]; linarith [ih]
    rw [hsum, hcorr, hS]
    simp only [hT]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp only [if_true, add_zero, Nat.zero_add, mul_zero, rr_zero, Nat.cast_zero, Nat.cast_one,
        show 1 + n = n + 1 by ring, sub_zero, zero_mul]
      have h := dstep0 hμ0 hμ1 hrec hX n
      simp only [rd, hμ0, hμ1] at h ⊢
      linear_combination h
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      rw [if_neg (by omega), show c + 1 - 1 = c by omega]
      have h := dstepc hrec hX c n
      push_cast
      rw [show c + 1 + 1 = c + 2 by ring, show c + 1 + 1 + n = c + n + 2 by ring,
        show c + 1 + n = c + n + 1 by ring] at *
      linear_combination h

end DChol

end RamanujanTau.QFProof3
