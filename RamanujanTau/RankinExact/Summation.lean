/-
# Partial summation without an `ε`

The `ε` in `RankinLandau.landau_core` comes from Rankin's trick `n^{α−1} ≤ M^{α+ε} n^{−1−ε}`.
Here it is replaced by exact estimates, using only a **linear bound** `∑_{n≤N} bₙ ≤ L N`:

* `majorize`: if `∑_{n≤N} bₙ ≤ LN` for all `N` and `w ≥ 0` is nonincreasing,
  `∑_{n≤N} bₙ wₙ ≤ L ∑_{n≤N} wₙ` (Abel summation, as an induction);
* `sum_wS_le`: `∑_{1≤n≤M} n^{α−1} ≤ M^α/α` (`0 < α ≤ 1`);
* `sum_v_le`: `∑_{n≥1} max(n, R)^{σ−1} ≤ (1 + 1/q) M^σ`, `R = ⌊M⌋+1`, `q = −σ ≥ 1`.

Both elementary sums telescope via Bernoulli's inequality.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Real Finset

/-- **Abel summation as a majorisation.** -/
lemma majorize {b w : ℕ → ℝ} {L : ℝ} (hw : ∀ i, 0 ≤ w (i + 1))
    (hanti : ∀ i, w (i + 2) ≤ w (i + 1))
    (hB : ∀ N : ℕ, ∑ i ∈ range N, b (i + 1) ≤ L * N) (N : ℕ) :
    ∑ i ∈ range N, b (i + 1) * w (i + 1) ≤ L * ∑ i ∈ range N, w (i + 1) := by
  have key : ∀ N : ℕ, ∑ i ∈ range N, b (i + 1) * w (i + 1) +
      (L * N - ∑ i ∈ range N, b (i + 1)) * w (N + 1) ≤ L * ∑ i ∈ range N, w (i + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, sum_range_succ, sum_range_succ]
      have h1 := hB (N + 1)
      rw [sum_range_succ] at h1
      have hc : 0 ≤ L * ((N + 1 : ℕ) : ℝ) - (∑ i ∈ range N, b (i + 1) + b (N + 1)) := by
        linarith
      have hv : w (N + 1 + 1) ≤ w (N + 1) := hanti N
      have := mul_le_mul_of_nonneg_left hv hc
      push_cast at this hc ⊢
      nlinarith
  have h := key N
  have hc : 0 ≤ (L * N - ∑ i ∈ range N, b (i + 1)) * w (N + 1) :=
    mul_nonneg (by linarith [hB N]) (hw N)
  linarith

/-- Bernoulli, concave case: `α (x+1)^{α−1} ≤ (x+1)^α − x^α`. -/
lemma bern_conc {α x : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    α * (x + 1) ^ (α - 1) ≤ (x + 1) ^ α - x ^ α := by
  set u : ℝ := x + 1 with hu
  have hu0 : 0 < u := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / u)
    (by rw [neg_div, neg_le_neg_iff, div_le_one hu0]; linarith) hα0.le hα1
  have e : 1 + -1 / u = x / u := by field_simp; ring
  rw [e, Real.div_rpow hx hu0.le] at hb
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu0 α
  rw [div_le_iff₀ hua] at hb
  rw [Real.rpow_sub_one hu0.ne']
  have : (1 + α * (-1 / u)) * u ^ α = u ^ α - α * (u ^ α / u) := by field_simp; ring
  linarith

/-- Bernoulli, convex case: `q (x+1)^{σ−1} ≤ x^σ − (x+1)^σ` for `σ = −q ≤ −1`, `x > 0`. -/
lemma bern_conv {σ x : ℝ} (hσ : σ ≤ -1) (hx : 0 < x) :
    -σ * (x + 1) ^ (σ - 1) ≤ x ^ σ - (x + 1) ^ σ := by
  have hx1 : 0 < x + 1 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / x)
    (by have : 0 ≤ 1 / x := by positivity
        linarith) (p := -σ)
    (by linarith)
  have e1 : 1 + 1 / x = (x + 1) / x := by field_simp
  rw [e1] at hb
  -- `x^σ = (x+1)^σ ((x+1)/x)^{−σ}`
  have e2 : x ^ σ = (x + 1) ^ σ * ((x + 1) / x) ^ (-σ) := by
    rw [Real.div_rpow hx1.le hx.le, Real.rpow_neg hx1.le, Real.rpow_neg hx.le]
    have h1 : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hx1 σ
    have h2 : 0 < x ^ σ := Real.rpow_pos_of_pos hx σ
    field_simp
  have hpos : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hx1 σ
  have h3 : (x + 1) ^ σ * (1 + -σ * (1 / x)) ≤ x ^ σ := by
    rw [e2]; exact mul_le_mul_of_nonneg_left hb hpos.le
  have h4 : -σ * (x + 1) ^ (σ - 1) ≤ (x + 1) ^ σ * (-σ * (1 / x)) := by
    rw [Real.rpow_sub_one hx1.ne']
    have : (x + 1) ^ σ / (x + 1) ≤ (x + 1) ^ σ * (1 / x) := by
      rw [div_eq_mul_one_div]
      gcongr; linarith
    nlinarith
  nlinarith

/-- The small-`n` weight `wS(n) = n^{α−1}·[n ≤ M]`. -/
noncomputable def wS (α M : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ M then (n : ℝ) ^ (α - 1) else 0

/-- The large-`n` weight `wL(n) = n^{σ−1}·[n > M]`. -/
noncomputable def wL (σ M : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ M then 0 else (n : ℝ) ^ (σ - 1)

lemma wS_nonneg (α M : ℝ) (n : ℕ) : 0 ≤ wS α M n := by
  unfold wS; split_ifs <;> positivity

lemma wL_nonneg (σ M : ℝ) (n : ℕ) : 0 ≤ wL σ M n := by
  unfold wL; split_ifs <;> positivity

lemma wS_anti {α M : ℝ} (hα1 : α ≤ 1) (i : ℕ) : wS α M (i + 2) ≤ wS α M (i + 1) := by
  unfold wS
  by_cases h2 : ((i + 2 : ℕ) : ℝ) ≤ M
  · have h1 : ((i + 1 : ℕ) : ℝ) ≤ M := le_trans (by push_cast; linarith) h2
    rw [if_pos h2, if_pos h1]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  · rw [if_neg h2]; split_ifs <;> positivity

/-- `∑_{i<N} wS(i+1) ≤ M^α/α`. -/
lemma sum_wS_le {α M : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (N : ℕ) :
    ∑ i ∈ range N, wS α M (i + 1) ≤ M ^ α / α := by
  set F : ℕ → ℝ := fun i => (min (i : ℝ) M) ^ α / α with hF
  have hstep : ∀ i, wS α M (i + 1) ≤ F (i + 1) - F i := by
    intro i
    simp only [hF, wS]
    by_cases h : ((i + 1 : ℕ) : ℝ) ≤ M
    · rw [if_pos h, min_eq_left h, min_eq_left (le_trans (by push_cast; linarith) h)]
      have := bern_conc hα0 hα1 (Nat.cast_nonneg (α := ℝ) i)
      push_cast
      rw [← sub_div, le_div_iff₀ hα0]
      linarith
    · rw [if_neg h, sub_nonneg]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (le_min (Nat.cast_nonneg _) hM)
        (min_le_min_right _ (by push_cast; linarith)) hα0.le) hα0.le
  calc ∑ i ∈ range N, wS α M (i + 1) ≤ ∑ i ∈ range N, (F (i + 1) - F i) := sum_le_sum fun i _ => hstep i
    _ = F N - F 0 := sum_range_sub F N
    _ ≤ M ^ α / α := by
        simp only [hF, Nat.cast_zero]
        rw [min_eq_left hM, Real.zero_rpow hα0.ne', zero_div, sub_zero]
        exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (le_min (Nat.cast_nonneg _) hM)
          (min_le_right _ _) hα0.le) hα0.le

/-- The tail majorant `v(n) = max(n, R)^{σ−1}`, `R = ⌊M⌋₊ + 1`. -/
noncomputable def vT (σ M : ℝ) (n : ℕ) : ℝ := (max (n : ℝ) ((⌊M⌋₊ : ℝ) + 1)) ^ (σ - 1)

lemma vT_nonneg (σ M : ℝ) (n : ℕ) : 0 ≤ vT σ M n := by
  unfold vT; exact Real.rpow_nonneg (le_trans (by positivity) (le_max_right _ _)) _

lemma vT_anti {σ M : ℝ} (hσ : σ ≤ -1) (i : ℕ) : vT σ M (i + 2) ≤ vT σ M (i + 1) := by
  unfold vT
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by positivity) (le_max_right _ _))
    (max_le_max (by push_cast; linarith) le_rfl) (by linarith)

lemma wL_le_vT {σ M : ℝ} (hM : 0 ≤ M) (n : ℕ) : wL σ M n ≤ vT σ M n := by
  unfold wL vT
  split_ifs with h
  · exact Real.rpow_nonneg (le_trans (by positivity) (le_max_right _ _)) _
  · push Not at h
    have h1 : ⌊M⌋₊ < n := (Nat.floor_lt hM).2 h
    have h2 : (⌊M⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast h1
    rw [max_eq_left h2]

/-- `∑_{i<N} v(i+1) ≤ (1 + 1/q) M^σ` with `q = −σ`. -/
lemma sum_vT_le {σ M : ℝ} (hσ : σ ≤ -1) (hM : 0 < M) (N : ℕ) :
    ∑ i ∈ range N, vT σ M (i + 1) ≤ (1 + 1 / -σ) * M ^ σ := by
  set R : ℝ := (⌊M⌋₊ : ℝ) + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [Nat.cast_nonneg (α := ℝ) ⌊M⌋₊]
  have hR0 : 0 < R := by linarith
  have hMR : M ≤ R := by rw [hR]; exact (Nat.lt_floor_add_one M).le
  have hq : 0 < -σ := by linarith
  set G : ℕ → ℝ := fun i => if (i : ℝ) ≤ R then R ^ σ / -σ + (R - i) * R ^ (σ - 1)
    else (i : ℝ) ^ σ / -σ with hG
  have hGpow : ∀ i : ℕ, R ≤ i → G i = (i : ℝ) ^ σ / -σ := by
    intro i hi
    simp only [hG]
    split_ifs with h
    · have : (i : ℝ) = R := le_antisymm h hi
      rw [this]; ring
    · rfl
  have hstep : ∀ i, vT σ M (i + 1) ≤ G i - G (i + 1) := by
    intro i
    by_cases h : ((i + 1 : ℕ) : ℝ) ≤ R
    · have hi : (i : ℝ) ≤ R := le_trans (by push_cast; linarith) h
      simp only [vT, hG, if_pos h, if_pos hi]
      rw [max_eq_right h]
      push_cast; ring_nf; rfl
    · push Not at h
      -- `R` is an integer, so `i ≥ R`
      have hiR : R ≤ i := by
        have h' : (⌊M⌋₊ : ℝ) + 1 < (i : ℝ) + 1 := by push_cast at h; linarith
        have : ⌊M⌋₊ < i := by exact_mod_cast (by linarith : (⌊M⌋₊ : ℝ) < i)
        rw [hR]; exact_mod_cast this
      have hi0 : (0 : ℝ) < i := lt_of_lt_of_le hR0 hiR
      rw [hGpow i hiR, hGpow (i + 1) h.le]
      simp only [vT]
      rw [max_eq_left h.le]
      have := bern_conv hσ hi0
      push_cast
      rw [← sub_div, le_div_iff₀ hq]
      linarith
  have hGN : 0 ≤ G N := by
    simp only [hG]
    split_ifs with h
    · have : 0 ≤ (R - N) * R ^ (σ - 1) := mul_nonneg (by linarith) (by positivity)
      have : 0 ≤ R ^ σ / -σ := div_nonneg (by positivity) hq.le
      linarith
    · exact div_nonneg (by positivity) hq.le
  have hG0 : G 0 = (1 + 1 / -σ) * R ^ σ := by
    simp only [hG, Nat.cast_zero, if_pos hR0.le, sub_zero]
    rw [show R * R ^ (σ - 1) = R ^ σ by rw [Real.rpow_sub_one hR0.ne']; field_simp]
    ring
  calc ∑ i ∈ range N, vT σ M (i + 1) ≤ ∑ i ∈ range N, (G i - G (i + 1)) :=
        sum_le_sum fun i _ => hstep i
    _ = G 0 - G N := sum_range_sub' G N
    _ ≤ G 0 := by linarith
    _ = (1 + 1 / -σ) * R ^ σ := hG0
    _ ≤ (1 + 1 / -σ) * M ^ σ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hM hMR (by linarith))
          (by have : 0 < 1 / -σ := by positivity
              linarith)

end RamanujanTau.RankinExact
