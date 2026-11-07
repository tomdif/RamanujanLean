/-
# The Hermite limit polynomials and their real, simple, interlacing roots

* `cH k` : `c₀ = 1`, `c₁ = 0`, `c_{k+2} = −2(k+1) c_k`. These are the derivatives `(d/dy)^k e^{−y²}` at `0`.
* `H d = Σ_{k≤d} C(d,k) c_k X^{d−k}`. This is `H_d(X/2)` for the physicists' Hermite polynomial `H_d`:
  `H 6 = X⁶ − 30X⁴ + 180X² − 120`, the `T_6` of `docs/JENSEN_THRESHOLDS.md`.
* `derivative_H` : `H_{d+1}' = (d+1) H_d` (Appell property). `H_succ` : `H_{d+1} = X H_d − 2 H_d'`.
  `H_monic`, `natDegree_H`, `eval_H_neg` (parity).
* **`H_alternating`** : for every `d` there are `d+1` increasing points at which `H d` has strictly
  alternating signs `(−1)^{d−i}`. Proof: induction on `d`; the roots of `H_d` come from the IVT,
  `H_d = Π (X − rᵢ)`, so `H_d'(rᵢ)` has sign `(−1)^{d−1−i}`, and `H_{d+1}(rᵢ) = −2 H_d'(rᵢ)`.
* **`H_roots_interlace`** / `H_hyperbolic` : `H d` has `d` distinct real roots.
-/
import RamanujanTau.JensenThreshold.Basic
import Mathlib.Analysis.Polynomial.Basic

set_option autoImplicit false

namespace GORZ

open Polynomial Finset Filter

/-- Hermite moments `c_k = (d/dy)^k e^{−y²} |_{y=0}`. -/
def cH : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | k + 2 => -2 * (k + 1) * cH k

lemma cH_zero : cH 0 = 1 := rfl
lemma cH_one : cH 1 = 0 := rfl
lemma cH_add_two (k : ℕ) : cH (k + 2) = -2 * (k + 1) * cH k := rfl

lemma cH_odd (k : ℕ) : cH (2 * k + 1) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, cH_add_two, ih]; ring

lemma neg_one_pow_mul_cH (k : ℕ) : (-1 : ℝ) ^ k * cH k = cH k := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [Even.neg_one_pow ⟨m, rfl⟩, one_mul]
  · rw [cH_odd, mul_zero]

/-- `H d = Σ_{k≤d} C(d,k) c_k X^{d−k}` (`= H_d(X/2)`, physicists' Hermite). -/
noncomputable def H (d : ℕ) : ℝ[X] := ∑ k ∈ range (d + 1), C ((d.choose k : ℝ) * cH k) * X ^ (d - k)

lemma eval_H (d : ℕ) (x : ℝ) :
    (H d).eval x = ∑ k ∈ range (d + 1), (d.choose k : ℝ) * cH k * x ^ (d - k) := by
  simp [H, eval_finsetSum]

lemma H_eval_zero (d : ℕ) : (H d).eval 0 = cH d := by
  rw [eval_H, sum_eq_single d]
  · simp
  · intro b hb hbd
    simp only [mem_range] at hb
    rw [zero_pow (by omega), mul_zero]
  · intro h; simp at h

lemma H_zero : H 0 = 1 := by simp [H, cH_zero]

lemma derivative_H (d : ℕ) : derivative (H (d + 1)) = C ((d + 1 : ℝ)) * H d := by
  unfold H
  rw [derivative_sum, sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, mul_one, derivative_C, add_zero]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  rw [derivative_C_mul_X_pow, show d + 1 - k - 1 = d - k by omega, ← mul_assoc, ← C_mul]
  congr 2
  have h := Nat.choose_mul_succ_eq d k
  have h' : ((d + 1).choose k : ℝ) * ((d + 1 - k : ℕ) : ℝ) = (d.choose k : ℝ) * (d + 1) := by
    exact_mod_cast h.symm
  calc ((d + 1).choose k : ℝ) * cH k * ((d + 1 - k : ℕ) : ℝ)
      = ((d + 1).choose k * ((d + 1 - k : ℕ) : ℝ)) * cH k := by ring
    _ = _ := by rw [h']; ring

lemma eval_H_neg (d : ℕ) (x : ℝ) : (H d).eval (-x) = (-1) ^ d * (H d).eval x := by
  rw [eval_H, eval_H, Finset.mul_sum]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  have e : (-1 : ℝ) ^ d = (-1) ^ (d - k) * (-1) ^ k := by rw [← pow_add]; congr 1; omega
  rw [neg_pow, e]
  have := neg_one_pow_mul_cH k
  calc (d.choose k : ℝ) * cH k * ((-1) ^ (d - k) * x ^ (d - k))
      = (-1) ^ (d - k) * ((d.choose k : ℝ) * ((-1) ^ k * cH k) * x ^ (d - k)) := by rw [this]; ring
    _ = _ := by ring

/-- the He-type recursion `H_{d+1} = X H_d − 2 H_d'`. -/
theorem H_succ (d : ℕ) : H (d + 1) = X * H d - C 2 * derivative (H d) := by
  suffices h : ∀ d, H (d + 1) - X * H d + C 2 * derivative (H d) = 0 by
    have := h d; linear_combination this
  intro d
  induction d with
  | zero => simp [H, sum_range_succ, cH_zero, cH_one]
  | succ d ih =>
    set D := H (d + 2) - X * H (d + 1) + C 2 * derivative (H (d + 1))
    have hD : derivative D = 0 := by
      simp only [D, derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_C, zero_mul,
        zero_add, one_mul]
      rw [derivative_H (d + 1), derivative_H d]
      have e : C ((↑(d + 1) : ℝ) + 1) * H (d + 1) - (H (d + 1) + X * (C ((d : ℝ) + 1) * H d)) +
          C 2 * derivative (C ((d : ℝ) + 1) * H d) =
          C ((d : ℝ) + 1) * (H (d + 1) - X * H d + C 2 * derivative (H d)) := by
        rw [derivative_mul, derivative_C, zero_mul, zero_add]
        simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
        ring
      rw [e, ih, mul_zero]
    have hc := eq_C_of_derivative_eq_zero hD
    have h0 : D.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero]
      simp only [D, eval_add, eval_sub, eval_mul, eval_X, eval_C, zero_mul, sub_zero]
      rw [derivative_H d, eval_mul, eval_C, H_eval_zero, H_eval_zero, show d + 2 = d + 2 from rfl,
        cH_add_two]
      ring
    rw [hc, h0, C_0]

theorem H_monic_natDegree (d : ℕ) : (H d).Monic ∧ (H d).natDegree = d := by
  induction d with
  | zero => simp [H_zero]
  | succ d ih =>
    obtain ⟨hm, hdeg⟩ := ih
    have hXm : (X * H d).Monic := monic_X.mul hm
    have hXdeg : (X * H d).natDegree = d + 1 := by
      rw [monic_X.natDegree_mul hm, natDegree_X, hdeg, add_comm]
    have hlt : (C 2 * derivative (H d)).degree < (X * H d).degree := by
      have h1 : (C 2 * derivative (H d)).degree ≤ (derivative (H d)).degree := degree_mul_le_of_le (degree_C_le) le_rfl |>.trans (by simp)
      have h2 : (derivative (H d)).degree < (H d).degree := degree_derivative_lt hm.ne_zero
      have h3 : (H d).degree < (X * H d).degree := by
        rw [degree_eq_natDegree hm.ne_zero, degree_eq_natDegree hXm.ne_zero, hXdeg, hdeg]
        exact_mod_cast Nat.lt_succ_self d
      exact lt_of_le_of_lt h1 (h2.trans h3)
    rw [H_succ]
    refine ⟨hXm.sub_of_left hlt, ?_⟩
    by_cases h0 : C 2 * derivative (H d) = 0
    · rw [h0, sub_zero, hXdeg]
    rw [natDegree_sub_eq_left_of_natDegree_lt (natDegree_lt_natDegree h0 hlt), hXdeg]

lemma H_monic (d : ℕ) : (H d).Monic := (H_monic_natDegree d).1
lemma natDegree_H (d : ℕ) : (H d).natDegree = d := (H_monic_natDegree d).2

/-! ## Sign of the derivative of `Π (X − rⱼ)` at its roots -/

/-- For `r` strictly increasing on `[0, d)`, `(−1)^{d−1−i} P'(rᵢ) > 0` where `P = Π_{j<d} (X − rⱼ)`. -/
theorem prod_derivative_sign : ∀ (d : ℕ) (r : ℕ → ℝ), (∀ i j, i < j → j < d → r i < r j) →
    ∀ i < d, 0 < (-1 : ℝ) ^ (d - 1 - i) * (derivative (∏ j ∈ range d, (X - C (r j)))).eval (r i) := by
  intro d
  induction d with
  | zero => intro r _ i hi; omega
  | succ d ih =>
    intro r hr i hi
    rw [prod_range_succ, derivative_mul, eval_add, eval_mul, eval_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, eval_sub, eval_X, eval_C, eval_one,
      mul_one]
    rcases Nat.lt_or_ge i d with hid | hid
    · have h0 : (∏ j ∈ range d, (X - C (r j))).eval (r i) = 0 := by
        rw [eval_prod]; exact prod_eq_zero (mem_range.mpr hid) (by simp)
      rw [h0, add_zero]
      have := ih r (fun a b hab hb => hr a b hab (by omega)) i hid
      have hneg : r i - r d < 0 := by linarith [hr i d hid (by omega)]
      have e : (-1 : ℝ) ^ (d + 1 - 1 - i) = -((-1) ^ (d - 1 - i)) := by
        rw [show d + 1 - 1 - i = (d - 1 - i) + 1 by omega, pow_succ]; ring
      rw [e]; nlinarith
    · obtain rfl : i = d := by omega
      simp only [sub_self, mul_zero, zero_add, show i + 1 - 1 - i = 0 by omega, pow_zero, one_mul]
      rw [eval_prod]
      exact prod_pos fun j hj => by
        simp only [mem_range] at hj
        simp only [eval_sub, eval_X, eval_C, sub_pos]
        exact hr j i hj (by omega)

/-! ## Roots from sign alternation -/

theorem roots_of_alternating (P : ℝ[X]) (d : ℕ) (hm : P.Monic) (hdeg : P.natDegree = d) (y : ℕ → ℝ)
    (hy : ∀ i < d, y i < y (i + 1)) (hs : ∀ i < d, P.eval (y i) * P.eval (y (i + 1)) < 0) :
    ∃ r : ℕ → ℝ, (∀ i < d, y i < r i ∧ r i < y (i + 1)) ∧ (∀ i j, i < j → j < d → r i < r j) ∧
      P = ∏ i ∈ range d, (X - C (r i)) := by
  have hroot : ∀ i, ∃ r, i < d → (r ∈ Set.Ioo (y i) (y (i + 1)) ∧ P.eval r = 0) := by
    intro i
    by_cases hi : i < d
    · have hsi := hs i hi
      have hab := (hy i hi).le
      have hc : ContinuousOn (fun t => P.eval t) (Set.Icc (y i) (y (i + 1))) := P.continuous.continuousOn
      rcases lt_or_gt_of_ne (show P.eval (y i) ≠ 0 by intro h0; rw [h0, zero_mul] at hsi; exact lt_irrefl _ hsi)
        with hneg | hpos
      · have hp : 0 < P.eval (y (i + 1)) := by nlinarith
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hab hc ⟨hneg, hp⟩
        exact ⟨r, fun _ => ⟨hr, hr0⟩⟩
      · have hn : P.eval (y (i + 1)) < 0 := by nlinarith
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab hc ⟨hn, hpos⟩
        exact ⟨r, fun _ => ⟨hr, hr0⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose r hr using hroot
  have hmono : ∀ i j, i < j → j < d → r i < r j := by
    intro i j hij hj
    have h1 := (hr i (by omega)).1.2
    have h2 := (hr j hj).1.1
    have := JensenThreshold.le_of_strict_chain hy (i := i + 1) (j := j) (by omega) (by omega)
    linarith
  refine ⟨r, fun i hi => (hr i hi).1, hmono, ?_⟩
  have hQm : (∏ i ∈ range d, (X - C (r i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  apply eq_of_monic_of_dvd_of_natDegree_le hQm hm
  · apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      simp only [coe_range, Set.mem_Iio] at hi hj
      show IsCoprime (X - C (r i)) (X - C (r j))
      apply isCoprime_X_sub_C_of_isUnit_sub
      apply IsUnit.mk0; rw [sub_ne_zero]
      rcases lt_or_gt_of_ne hij with h | h
      · exact (hmono i j h hj).ne
      · exact (hmono j i h hi).ne'
    · intro i hi; rw [dvd_iff_isRoot]; exact (hr i (mem_range.mp hi)).2
  · rw [hdeg, natDegree_finsetProd_X_sub_C_eq_card, card_range]

lemma neg_one_pow_sq (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- **Hermite sign alternation**: `H d` takes strictly alternating signs `(−1)^{d−i}` at `d+1` increasing
points. (Milestone 1.) -/
theorem H_alternating (d : ℕ) : ∃ y : ℕ → ℝ, (∀ i < d, y i < y (i + 1)) ∧
    ∀ i ≤ d, 0 < (-1 : ℝ) ^ (d - i) * (H d).eval (y i) := by
  induction d with
  | zero =>
    refine ⟨fun _ => 0, fun i hi => absurd hi (by omega), fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp [H_zero]
  | succ d ih =>
    obtain ⟨y, hy, hys⟩ := ih
    have hs : ∀ i < d, (H d).eval (y i) * (H d).eval (y (i + 1)) < 0 := by
      intro i hi
      have h1 := hys i (by omega)
      have h2 := hys (i + 1) (by omega)
      have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - (i + 1))) := by
        rw [show d - i = (d - (i + 1)) + 1 by omega, pow_succ]; ring
      rw [e] at h1
      have h3 := neg_one_pow_sq (d - (i + 1))
      nlinarith [mul_pos h1 h2]
    obtain ⟨r, hr, hrm, hfac⟩ := roots_of_alternating (H d) d (H_monic d) (natDegree_H d) y hy hs
    have hder := prod_derivative_sign d r hrm
    have hval : ∀ i < d, 0 < (-1 : ℝ) ^ (d - i) * (H (d + 1)).eval (r i) := by
      intro i hi
      have h0 : (H d).eval (r i) = 0 := by
        rw [hfac, eval_prod]; exact prod_eq_zero (mem_range.mpr hi) (by simp)
      rw [H_succ, eval_sub, eval_mul, eval_X, h0, mul_zero, zero_sub, eval_mul, eval_C]
      have := hder i hi
      rw [← hfac] at this
      have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - 1 - i)) := by
        rw [show d - i = (d - 1 - i) + 1 by omega, pow_succ]; ring
      rw [e]; nlinarith
    have hdeg_pos : 0 < (H (d + 1)).degree := by
      rw [degree_eq_natDegree (H_monic _).ne_zero, natDegree_H]; exact_mod_cast Nat.succ_pos d
    have ht := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (H (d + 1)) hdeg_pos
      (by rw [(H_monic _).leadingCoeff]; norm_num)
    obtain ⟨Y, hY1, hY2⟩ :=
      ((ht.eventually_gt_atTop 0).and (eventually_gt_atTop (|y 0| + |y d| + 1))).exists
    have hY0 : 0 < Y := by have := abs_nonneg (y 0); have := abs_nonneg (y d); linarith
    have hyY : ∀ i ≤ d, -Y < y i ∧ y i < Y := by
      intro i hi
      have h0 := JensenThreshold.le_of_strict_chain hy (i := 0) (j := i) (by omega) hi
      have h1 := JensenThreshold.le_of_strict_chain hy (i := i) (j := d) hi le_rfl
      have := neg_abs_le (y 0); have := le_abs_self (y d); have := abs_nonneg (y 0)
      have := abs_nonneg (y d)
      constructor <;> linarith
    set z : ℕ → ℝ := fun i => if i = 0 then -Y else if i ≤ d then r (i - 1) else Y with hz
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      simp only [hz]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [if_true, show (0 + 1 ≠ 0) from by omega, if_false]
        split_ifs with h1
        · have := (hr 0 (by omega)).1; have := (hyY 0 (by omega)).1; simp; linarith
        · linarith
      · simp only [show i ≠ 0 by omega, show i + 1 ≠ 0 by omega, if_false]
        split_ifs with h1 h2 h2
        · rw [show i + 1 - 1 = i by omega]; exact hrm (i - 1) i (by omega) (by omega)
        · have := (hr (i - 1) (by omega)).2; have := (hyY d le_rfl).2
          rw [show i - 1 + 1 = i by omega] at *
          have := JensenThreshold.le_of_strict_chain hy (i := i) (j := d) (by omega) le_rfl
          linarith
        · omega
        · omega
    · intro i hi
      simp only [hz]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [if_true, Nat.sub_zero]
        rw [eval_H_neg, ← mul_assoc, neg_one_pow_sq, one_mul]; exact hY1
      · simp only [show i ≠ 0 by omega, if_false]
        split_ifs with h1
        · have := hval (i - 1) (by omega)
          rwa [show d + 1 - i = d - (i - 1) by omega]
        · obtain rfl : i = d + 1 := by omega
          simpa using hY1

/-- `H d` has `d` distinct real roots, interlaced by any alternation points. -/
theorem H_simple_roots (d : ℕ) : ∃ r : ℕ → ℝ, (∀ i j, i < j → j < d → r i < r j) ∧
    H d = ∏ i ∈ range d, (X - C (r i)) := by
  obtain ⟨y, hy, hys⟩ := H_alternating d
  have hs : ∀ i < d, (H d).eval (y i) * (H d).eval (y (i + 1)) < 0 := by
    intro i hi
    have h1 := hys i (by omega)
    have h2 := hys (i + 1) (by omega)
    have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - (i + 1))) := by
      rw [show d - i = (d - (i + 1)) + 1 by omega, pow_succ]; ring
    rw [e] at h1
    have h3 := neg_one_pow_sq (d - (i + 1))
    nlinarith [mul_pos h1 h2]
  obtain ⟨r, -, hrm, hfac⟩ := roots_of_alternating (H d) d (H_monic d) (natDegree_H d) y hy hs
  exact ⟨r, hrm, hfac⟩

theorem H_hyperbolic (d : ℕ) : JensenThreshold.Hyperbolic (H d) := by
  obtain ⟨y, hy, hys⟩ := H_alternating d
  refine JensenThreshold.hyperbolic_of_alternating (H d) d (natDegree_H d).le y hy fun i hi => ?_
  have h1 := hys i (by omega)
  have h2 := hys (i + 1) (by omega)
  have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - (i + 1))) := by
    rw [show d - i = (d - (i + 1)) + 1 by omega, pow_succ]; ring
  rw [e] at h1
  have h3 := neg_one_pow_sq (d - (i + 1))
  nlinarith [mul_pos h1 h2]

end GORZ
