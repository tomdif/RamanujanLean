/-
# From Riesz means to partial sums (nonnegative coefficients)

For `a : ℕ → ℝ` put `W a k x = ∑_{1 ≤ n ≤ x} aₙ (x − n)^k` (so `W a 0 N = ∑_{n ≤ N} aₙ`).
If `aₙ ≥ 0` and `W a (k+1) x = c x^{k+2}/(k+2) + O(x^{k+2−θ})`, then
`W a k x = c x^{k+1}/(k+1) + O(x^{k+1−θ/2})` (`riesz_step`): the elementary differencing
`(k+1) h W_k(x) ≤ W_{k+1}(x+h) − W_{k+1}(x) ≤ (k+1) h W_k(x+h)` with `h ≍ x^{1−θ/2}`.
Iterating (`riesz_descend`) gives a power-saving error for the partial sums.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Finset Real

/-- `W a k x = ∑_{1 ≤ n ≤ ⌊x⌋} aₙ (x − n)^k`. -/
noncomputable def W (a : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x - n) ^ k

/-- `(k+1) h u^k ≤ (u+h)^{k+1} − u^{k+1} ≤ (k+1) h (u+h)^k` for `u, h ≥ 0`. -/
lemma pow_succ_sub_bounds (k : ℕ) {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    (k + 1) * h * u ^ k ≤ (u + h) ^ (k + 1) - u ^ (k + 1) ∧
      (u + h) ^ (k + 1) - u ^ (k + 1) ≤ (k + 1) * h * (u + h) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : (u + h) ^ (k + 1 + 1) - u ^ (k + 1 + 1) =
        (u + h) * ((u + h) ^ (k + 1) - u ^ (k + 1)) + h * u ^ (k + 1) := by ring
    have hk : u ^ (k + 1) ≤ (u + h) ^ (k + 1) := pow_le_pow_left₀ hu (by linarith) _
    have huk : 0 ≤ u ^ k := pow_nonneg hu _
    push_cast
    rw [e]
    constructor
    · have : (u + h) * ((k + 1) * h * u ^ k) ≥ (k + 1) * h * u ^ (k + 1) := by
        rw [pow_succ]; nlinarith [mul_nonneg hh huk, mul_nonneg (mul_nonneg hh huk) hh]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ u + h)]
    · have : (u + h) * ((k + 1) * h * (u + h) ^ k) = (k + 1) * h * (u + h) ^ (k + 1) := by
        ring
      nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ u + h),
        mul_le_mul_of_nonneg_left hk hh]

lemma floor_mono_sub {x h : ℝ} (hh : 0 ≤ h) : ⌊x⌋₊ ≤ ⌊x + h⌋₊ :=
  Nat.floor_le_floor (by linarith)

/-- The differencing inequalities. -/
lemma W_diff_bounds (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (k : ℕ) {x h : ℝ} (hx : 0 ≤ x)
    (hh : 0 ≤ h) :
    (k + 1) * h * W a k x ≤ W a (k + 1) (x + h) - W a (k + 1) x ∧
      W a (k + 1) (x + h) - W a (k + 1) x ≤ (k + 1) * h * W a k (x + h) := by
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊x + h⌋₊ := Icc_subset_Icc le_rfl (floor_mono_sub hh)
  have split : W a (k + 1) (x + h) = ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ (k + 1) +
      ∑ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ (k + 1) := by
    unfold W; rw [← sum_sdiff hsub, add_comm]
  have split' : W a k (x + h) = ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ k +
      ∑ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ k := by
    unfold W; rw [← sum_sdiff hsub, add_comm]
  -- facts on the two ranges
  have hin : ∀ n ∈ Icc 1 ⌊x⌋₊, 0 ≤ x - n := by
    intro n hn
    have := (mem_Icc.1 hn).2
    have : (n : ℝ) ≤ x := (Nat.cast_le.2 this).trans (Nat.floor_le hx)
    linarith
  have hout : ∀ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, 0 ≤ x + h - n ∧ x + h - n ≤ h := by
    intro n hn
    rw [mem_sdiff, mem_Icc, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    have hn2 : (n : ℝ) ≤ x + h := (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith))
    have hn3 : ⌊x⌋₊ < n := by omega
    have : x < n := (Nat.floor_lt hx).1 hn3
    constructor <;> linarith
  rw [split]
  have eW : W a (k + 1) x = ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x - n) ^ (k + 1) := rfl
  rw [eW]
  constructor
  · -- lower bound
    have h1 : ∑ n ∈ Icc 1 ⌊x⌋₊, (k + 1) * h * (a n * (x - n) ^ k) ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, (a n * (x + h - n) ^ (k + 1) - a n * (x - n) ^ (k + 1)) := by
      apply sum_le_sum; intro n hn
      have b := (pow_succ_sub_bounds k (hin n hn) hh).1
      have e2 : x + h - n = (x - n) + h := by ring
      rw [e2]
      nlinarith [ha n]
    have h2 : 0 ≤ ∑ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ (k + 1) :=
      sum_nonneg fun n hn => mul_nonneg (ha n) (pow_nonneg (hout n hn).1 _)
    rw [sum_sub_distrib] at h1
    rw [W, mul_sum]
    linarith
  · -- upper bound
    have h1 : ∑ n ∈ Icc 1 ⌊x⌋₊, (a n * (x + h - n) ^ (k + 1) - a n * (x - n) ^ (k + 1)) ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, (k + 1) * h * (a n * (x + h - n) ^ k) := by
      apply sum_le_sum; intro n hn
      have b := (pow_succ_sub_bounds k (hin n hn) hh).2
      have e2 : x + h - n = (x - n) + h := by ring
      rw [e2]
      nlinarith [ha n]
    have h2 : ∑ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, a n * (x + h - n) ^ (k + 1) ≤
        ∑ n ∈ Icc 1 ⌊x + h⌋₊ \ Icc 1 ⌊x⌋₊, (k + 1) * h * (a n * (x + h - n) ^ k) := by
      apply sum_le_sum; intro n hn
      obtain ⟨p0, p1⟩ := hout n hn
      have : (x + h - n) ^ (k + 1) ≤ (k + 1) * h * (x + h - n) ^ k := by
        rw [pow_succ]
        have hk0 : 0 ≤ (x + h - n) ^ k := pow_nonneg p0 _
        have : (1:ℝ) ≤ k + 1 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
        nlinarith [mul_le_mul_of_nonneg_left p1 hk0, mul_nonneg hk0 hh]
      nlinarith [ha n]
    rw [sum_sub_distrib] at h1
    rw [split', mul_add, mul_sum, mul_sum]
    linarith

/-- The asymptotic statement for the `k`-th Riesz sum with saving `θ`. -/
def RieszAsymp (a : ℕ → ℝ) (c : ℝ) (k : ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 0 < x →
    |W a k x - c * x ^ (k + 1) / (k + 1)| ≤ C * x ^ ((k : ℝ) + 1 - θ)

lemma W_eq_zero_of_lt_one (a : ℕ → ℝ) (k : ℕ) {x : ℝ} (hx : x < 1) : W a k x = 0 := by
  unfold W
  have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 hx
  simp [this]

/-- One differencing step: saving `θ` for `W_{k+1}` gives saving `θ/2` for `W_k`. -/
theorem riesz_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 ≤ c) (k : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (H : RieszAsymp a c (k + 1) θ) : RieszAsymp a c k (θ / 2) := by
  obtain ⟨C, hC0⟩ := H
  have hC : ∀ y : ℝ, 0 < y →
      |W a (k + 1) y - c * y ^ (k + 2) / ((k:ℝ) + 2)| ≤ C * y ^ ((k:ℝ) + 2 - θ) := by
    intro y hy
    have := hC0 y hy
    have e1 : ((k + 1 : ℕ) : ℝ) + 1 = (k:ℝ) + 2 := by push_cast; ring
    rw [e1] at this
    exact this
  set e : ℝ := (k : ℝ) + 1 - θ / 2 with he
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0:ℝ) < k + 1 := by linarith
  -- a convenient constant
  set C' : ℝ := c / (k + 1) + c * 2 ^ k + 4 * |C| * 2 ^ (k + 2) / (k + 1) with hC'
  refine ⟨C', fun x hx => ?_⟩
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- small x: `W = 0`
    rw [W_eq_zero_of_lt_one a k hx1, zero_sub, abs_neg]
    have hxe : x ^ (k + 1) ≤ x ^ e := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge hx hx1.le
      push_cast; rw [he]; linarith
    have h1 : |c * x ^ (k + 1) / (k + 1)| = c / (k + 1) * x ^ (k + 1) := by
      rw [abs_of_nonneg (by positivity)]; ring
    rw [h1]
    have : c / (k + 1) ≤ C' := by
      rw [hC']; have : 0 ≤ c * 2 ^ k := by positivity
      have : 0 ≤ 4 * |C| * 2 ^ (k + 2) / (k + 1) := by positivity
      linarith
    calc c / (k + 1) * x ^ (k + 1) ≤ c / (k + 1) * x ^ e :=
          mul_le_mul_of_nonneg_left hxe (by positivity)
      _ ≤ C' * x ^ e := mul_le_mul_of_nonneg_right this (by positivity)
  · -- large x: difference with `h = x^{1-θ/2}/2`
    set h : ℝ := x ^ (1 - θ / 2) / 2 with hh
    have hxpos : 0 < x := hx
    have hpow1 : x ^ (1 - θ / 2) ≤ x := by
      calc x ^ (1 - θ / 2) ≤ x ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ = x := Real.rpow_one x
    have hh0 : 0 < h := by positivity
    have hhx : h ≤ x / 2 := by rw [hh]; linarith
    have hxh0 : 0 ≤ x - h := by linarith
    -- bounds from the hypothesis at the three points
    have hA := hC (x + h) (by linarith)
    have hB := hC x hx
    have hD := hC (x - h) (by linarith)
    have hdiff1 := W_diff_bounds a ha k hx.le hh0.le
    have hdiff2 := W_diff_bounds a ha k hxh0 hh0.le
    rw [sub_add_cancel] at hdiff2
    -- the error terms: `(x ± h)^{k+2-θ} ≤ 2^{k+2} x^{k+2-θ}`
    have hexp : (0:ℝ) ≤ (k:ℝ) + 2 - θ := by push_cast; linarith
    have hE : ∀ y : ℝ, 0 < y → y ≤ 2 * x →
        |C| * y ^ ((k:ℝ) + 2 - θ) ≤ |C| * 2 ^ (k + 2) * x ^ ((k:ℝ) + 2 - θ) := by
      intro y hy hy2
      have h2 : y ^ ((k:ℝ) + 2 - θ) ≤ (2 * x) ^ ((k:ℝ) + 2 - θ) :=
        Real.rpow_le_rpow hy.le hy2 hexp
      rw [Real.mul_rpow (by norm_num) hx.le] at h2
      have h3 : (2:ℝ) ^ ((k:ℝ) + 2 - θ) ≤ 2 ^ (k + 2) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast; linarith
      have : |C| * y ^ ((k:ℝ) + 2 - θ) ≤
          |C| * (2 ^ (k + 2) * x ^ ((k:ℝ) + 2 - θ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
      linarith
    set X : ℝ := x ^ ((k:ℝ) + 2 - θ) with hX
    have eA := hE (x + h) (by linarith) (by linarith)
    have eB := hE x hx (by linarith)
    have eD := hE (x - h) (by linarith) (by linarith)
    have absC : ∀ y : ℝ, C * y ≤ |C| * y ∨ y < 0 := fun y => by
      rcases lt_or_ge y 0 with hy | hy
      · right; exact hy
      · left; exact mul_le_mul_of_nonneg_right (le_abs_self C) hy
    have cA : C * (x + h) ^ ((k:ℝ) + 2 - θ) ≤ |C| * 2 ^ (k + 2) * X := by
      rcases absC ((x + h) ^ ((k:ℝ) + 2 - θ)) with h' | h'
      · linarith
      · exact absurd h' (not_lt.2 (by positivity))
    have cB : C * x ^ ((k:ℝ) + 2 - θ) ≤ |C| * 2 ^ (k + 2) * X := by
      rcases absC (x ^ ((k:ℝ) + 2 - θ)) with h' | h'
      · linarith
      · exact absurd h' (not_lt.2 (by positivity))
    have cD : C * (x - h) ^ ((k:ℝ) + 2 - θ) ≤ |C| * 2 ^ (k + 2) * X := by
      rcases absC ((x - h) ^ ((k:ℝ) + 2 - θ)) with h' | h'
      · linarith
      · exact absurd h' (not_lt.2 (by positivity))
    rw [abs_le] at hA hB hD
    -- polynomial main terms
    have pA := (pow_succ_sub_bounds (k + 1) hx.le hh0.le)
    have pD := (pow_succ_sub_bounds (k + 1) hxh0 hh0.le)
    rw [sub_add_cancel] at pD
    have pk1 := (pow_succ_sub_bounds k hx.le hh0.le).2
    have pk2 := (pow_succ_sub_bounds k hxh0 hh0.le).2
    rw [sub_add_cancel] at pk2
    -- `h (x+h)^k ≤ 2^k ...`
    have hxk : (x + h) ^ k ≤ 2 ^ k * x ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    -- the key comparisons, `X / h = 2 x^{e}` and `h x^k ≤ x^{e}`
    have hXh : X = 2 * h * x ^ e := by
      rw [hX, hh, he, mul_div_cancel₀ _ (two_ne_zero), ← Real.rpow_add hx]
      congr 1; push_cast; ring
    have hhxk : h * x ^ k ≤ x ^ e := by
      rw [hh, he, ← Real.rpow_natCast x k, div_mul_eq_mul_div, ← Real.rpow_add hx]
      have : x ^ (1 - θ / 2 + (k:ℝ)) = x ^ ((k:ℝ) + 1 - θ / 2) := by congr 1; ring
      rw [this]
      have : 0 ≤ x ^ ((k:ℝ) + 1 - θ / 2) := by positivity
      linarith
    have hxe0 : 0 ≤ x ^ e := by positivity
    have hkk : (k + 1 : ℝ) * h ≠ 0 := by positivity
    -- upper bound for `W_k(x)`
    have up : W a k x ≤ c * x ^ (k + 1) / (k + 1) + C' * x ^ e := by
      have h1 : (k + 1) * h * W a k x ≤
          c * (x + h) ^ (k + 2) / (k + 2) - c * x ^ (k + 2) / (k + 2) +
            2 * (|C| * 2 ^ (k + 2) * X) := by
        have := hdiff1.1
        linarith only [this, hA.1, hA.2, hB.1, hB.2, cA, cB]
      -- `c((x+h)^{k+2} - x^{k+2})/(k+2) ≤ c h (x+h)^{k+1}`
      have h2 : c * (x + h) ^ (k + 2) / (k + 2) - c * x ^ (k + 2) / (k + 2) ≤
          c * h * (x + h) ^ (k + 1) := by
        have := pA.2
        rw [show (k + 1 + 1) = k + 2 from rfl] at this
        have hk2 : (0:ℝ) < k + 2 := by linarith
        rw [← sub_div, div_le_iff₀ hk2, ← mul_sub]
        push_cast at this
        have : c * ((x + h) ^ (k + 2) - x ^ (k + 2)) ≤ c * ((k + 1 + 1) * h * (x + h) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left this hc
        linarith only [this]
      -- `(x+h)^{k+1} ≤ x^{k+1} + (k+1) h (x+h)^k`
      have h3 : c * h * (x + h) ^ (k + 1) ≤
          (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) + (k + 1) * h * (c * h * (2 ^ k * x ^ k)) := by
        have q : (x + h) ^ (k + 1) ≤ x ^ (k + 1) + (k + 1) * h * (2 ^ k * x ^ k) := by
          have p1 := pk1; push_cast at p1
          have p2 := mul_le_mul_of_nonneg_left hxk (by positivity : (0:ℝ) ≤ (k + 1) * h)
          linarith only [p1, p2]
        have e1 : (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) = c * h * x ^ (k + 1) := by
          field_simp
        rw [e1]
        have : c * h * (x + h) ^ (k + 1) ≤ c * h * (x ^ (k + 1) + (k + 1) * h * (2 ^ k * x ^ k)) :=
          mul_le_mul_of_nonneg_left q (by positivity)
        linarith only [this]
      have h4 : (k + 1) * h * W a k x ≤ (k + 1) * h * (c * x ^ (k + 1) / (k + 1) + C' * x ^ e) := by
        have t1 : (k + 1) * h * (c * h * (2 ^ k * x ^ k)) ≤ (k + 1) * h * (c * 2 ^ k * x ^ e) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := mul_le_mul_of_nonneg_left hhxk (by positivity : (0:ℝ) ≤ c * 2 ^ k)
          linarith only [this]
        have t2 : 2 * (|C| * 2 ^ (k + 2) * X) ≤ (k + 1) * h * (4 * |C| * 2 ^ (k + 2) / (k + 1) * x ^ e) := by
          rw [hXh]; apply le_of_eq; field_simp; ring
        have hsplit : (k + 1) * h * (c * x ^ (k + 1) / (k + 1) + C' * x ^ e) =
            (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) + (k + 1) * h * (c / (k + 1) * x ^ e) +
            (k + 1) * h * (c * 2 ^ k * x ^ e) +
            (k + 1) * h * (4 * |C| * 2 ^ (k + 2) / (k + 1) * x ^ e) := by rw [hC']; ring
        rw [hsplit]
        have hpos : 0 ≤ (k + 1) * h * (c / (k + 1) * x ^ e) := by positivity
        linarith only [h1, h2, h3, t1, t2, hpos]
      exact le_of_mul_le_mul_left h4 (by positivity)
    -- lower bound for `W_k(x)`
    have lo : c * x ^ (k + 1) / (k + 1) - C' * x ^ e ≤ W a k x := by
      have h1 : c * x ^ (k + 2) / (k + 2) - c * (x - h) ^ (k + 2) / (k + 2) -
            2 * (|C| * 2 ^ (k + 2) * X) ≤ (k + 1) * h * W a k x := by
        have := hdiff2.2
        linarith only [this, hD.1, hD.2, hB.1, hB.2, cD, cB]
      have h2 : c * h * (x - h) ^ (k + 1) ≤
          c * x ^ (k + 2) / (k + 2) - c * (x - h) ^ (k + 2) / (k + 2) := by
        have := pD.1
        have hk2 : (0:ℝ) < k + 2 := by linarith
        rw [← sub_div, le_div_iff₀ hk2, ← mul_sub]
        push_cast at this
        have : c * ((k + 1 + 1) * h * (x - h) ^ (k + 1)) ≤ c * (x ^ (k + 1 + 1) - (x - h) ^ (k + 1 + 1)) :=
          mul_le_mul_of_nonneg_left this hc
        linarith only [this]
      have h3 : (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) - (k + 1) * h * (c * h * x ^ k) ≤
          c * h * (x - h) ^ (k + 1) := by
        have q : x ^ (k + 1) - (k + 1) * h * x ^ k ≤ (x - h) ^ (k + 1) := by
          have := pk2; push_cast at this; linarith
        have e1 : (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) = c * h * x ^ (k + 1) := by
          field_simp
        rw [e1]
        have := mul_le_mul_of_nonneg_left q (by positivity : (0:ℝ) ≤ c * h)
        linarith only [this]
      have h4 : (k + 1) * h * (c * x ^ (k + 1) / (k + 1) - C' * x ^ e) ≤ (k + 1) * h * W a k x := by
        have t1 : (k + 1) * h * (c * h * x ^ k) ≤ (k + 1) * h * (c / (k + 1) * x ^ e) +
            (k + 1) * h * (c * 2 ^ k * x ^ e) := by
          have : c * h * x ^ k ≤ c * 2 ^ k * x ^ e := by
            have r1 := mul_le_mul_of_nonneg_left hhxk hc
            have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
            have r2 := mul_le_mul_of_nonneg_right h2k (mul_nonneg hc hxe0)
            linarith only [r1, r2]
          have hpos : 0 ≤ (k + 1) * h * (c / (k + 1) * x ^ e) := by positivity
          have r3 := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ (k + 1) * h)
          linarith only [hpos, r3]
        have t2 : 2 * (|C| * 2 ^ (k + 2) * X) ≤ (k + 1) * h * (4 * |C| * 2 ^ (k + 2) / (k + 1) * x ^ e) := by
          rw [hXh]; apply le_of_eq; field_simp; ring
        have hsplit : (k + 1) * h * (c * x ^ (k + 1) / (k + 1) - C' * x ^ e) =
            (k + 1) * h * (c * x ^ (k + 1) / (k + 1)) - (k + 1) * h * (c / (k + 1) * x ^ e) -
            (k + 1) * h * (c * 2 ^ k * x ^ e) -
            (k + 1) * h * (4 * |C| * 2 ^ (k + 2) / (k + 1) * x ^ e) := by rw [hC']; ring
        rw [hsplit]
        linarith only [h1, h2, h3, t1, t2]
      exact le_of_mul_le_mul_left h4 (by positivity)
    rw [abs_le]
    constructor <;> linarith only [up, lo]

/-- Iterating `riesz_step` `k` times. -/
theorem riesz_descend (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 ≤ c) :
    ∀ (k : ℕ) {θ : ℝ}, 0 < θ → θ ≤ 1 → RieszAsymp a c k θ → RieszAsymp a c 0 (θ / 2 ^ k) := by
  intro k
  induction k with
  | zero => intro θ _ _ H; simpa using H
  | succ k ih =>
    intro θ h0 h1 H
    have H' := riesz_step a ha hc k h0 h1 H
    have := ih (θ := θ / 2) (by positivity) (by linarith) H'
    rwa [div_div, ← pow_succ'] at this

/-- Partial sums from `RieszAsymp a c 0 θ`. -/
theorem partial_sum_of_riesz0 (a : ℕ → ℝ) {c θ : ℝ} (H : RieszAsymp a c 0 θ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, a n - c * N| ≤ C * (N : ℝ) ^ (1 - θ) := by
  obtain ⟨C, hC⟩ := H
  refine ⟨C, fun N hN => ?_⟩
  have := hC N (by exact_mod_cast hN)
  simp only [W, Nat.floor_natCast, sub_self, pow_zero, mul_one, CharP.cast_eq_zero, zero_add,
    pow_one, div_one] at this
  simpa using this

end RamanujanTau.RankinError
