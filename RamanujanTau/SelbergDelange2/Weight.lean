/-
# The weighted density bound (real-variable Selberg–Delange, step 2)

If `Σ_{n≤y} |f(n)| ≤ K y (1+log y)^{σ−1}` for `y ≥ 1` (`0 < σ < 1`), then

  `W(x) = Σ_{n≤x} |f(n)|/n · 1/(1 + log(x/n)) ≤ 2eK (1 + 1/σ + log(1+log x)) (2+log x)^{σ−1}`

(`weight_bound`).  Proof: split `n ≤ x` by `j = ⌊log(x/n)⌋`; the block `j` contributes
`≤ eK(1+t−j)^{σ−1}/(1+j)` (`t = log x`), and
`Σ_{j≤t} (1+t−j)^{σ−1}/(1+j) ≤ 2(2+t)^{σ−1}(1+log(1+t)) + (2/σ)(2+t)^{σ−1}`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange2

open Finset

/-- `Σ_{m<M} (m+1)^{σ−1} ≤ M^σ/σ` for `0 < σ ≤ 1` (Bernoulli). -/
lemma sum_rpow_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (M : ℕ) :
    ∑ m ∈ range M, ((m + 1 : ℕ) : ℝ) ^ (σ - 1) ≤ (M : ℝ) ^ σ / σ := by
  induction M with
  | zero => simp [Real.zero_rpow hσ0.ne']
  | succ M ih =>
    rw [sum_range_succ]
    have hM1 : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    -- (M)^σ ≤ (M+1)^σ − σ (M+1)^{σ−1}
    have hb : (M : ℝ) ^ σ ≤ ((M + 1 : ℕ) : ℝ) ^ σ - σ * ((M + 1 : ℕ) : ℝ) ^ (σ - 1) := by
      have hs : (-1 : ℝ) ≤ -1 / ((M + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hM1]; push_cast; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      have h := rpow_one_add_le_one_add_mul_self hs hσ0.le hσ1
      have e1 : (1 + -1 / ((M + 1 : ℕ) : ℝ)) = (M : ℝ) / ((M + 1 : ℕ) : ℝ) := by
        field_simp; push_cast; ring
      rw [e1, Real.div_rpow (Nat.cast_nonneg _) hM1.le] at h
      have hpos : 0 < ((M + 1 : ℕ) : ℝ) ^ σ := Real.rpow_pos_of_pos hM1 _
      rw [div_le_iff₀ hpos] at h
      have e2 : ((M + 1 : ℕ) : ℝ) ^ (σ - 1) = ((M + 1 : ℕ) : ℝ) ^ σ / ((M + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_sub_one hM1.ne']
      rw [e2]
      have : (1 + σ * (-1 / ((M + 1 : ℕ) : ℝ))) * ((M + 1 : ℕ) : ℝ) ^ σ =
          ((M + 1 : ℕ) : ℝ) ^ σ - σ * (((M + 1 : ℕ) : ℝ) ^ σ / ((M + 1 : ℕ) : ℝ)) := by
        field_simp
        ring
      linarith
    have : (M : ℝ) ^ σ / σ + ((M + 1 : ℕ) : ℝ) ^ (σ - 1) ≤ ((M + 1 : ℕ) : ℝ) ^ σ / σ := by
      rw [div_add' _ _ _ hσ0.ne', div_le_div_iff_of_pos_right hσ0]; linarith
    push_cast at this ih ⊢
    linarith

/-- The `j`-sum. -/
lemma j_sum_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ range (⌊t⌋₊ + 1), (1 + t - j) ^ (σ - 1) / (1 + j) ≤
      (2 * (1 + Real.log (1 + t)) + 2 / σ) * (2 + t) ^ (σ - 1) := by
  set J := ⌊t⌋₊ with hJ
  have hJt : (J : ℝ) ≤ t := Nat.floor_le ht
  have hJt' : t < J + 1 := Nat.lt_floor_add_one t
  have hs1 : σ - 1 < 0 := by linarith
  set A : ℝ := ((2 + t) / 2) ^ (σ - 1) with hA
  have hterm : ∀ j ∈ range (J + 1), (1 + t - j) ^ (σ - 1) / (1 + j) ≤
      A * (1 / (1 + j)) + 2 / (2 + t) * (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hjJr : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hpos : 0 < 1 + t - j := by linarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ 2 / (2 + t) * (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) := by positivity
    have hC0 : 0 ≤ A * (1 / (1 + j)) := by positivity
    rcases le_or_gt ((2 + t) / 2) (1 + t - j) with h | h
    · have : (1 + t - j) ^ (σ - 1) ≤ A :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h hs1.le
      have : (1 + t - j) ^ (σ - 1) / (1 + j) ≤ A * (1 / (1 + j)) := by
        rw [div_eq_mul_one_div]; gcongr
      linarith
    · have h1 : 1 / (1 + (j : ℝ)) ≤ 2 / (2 + t) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hcast : (((J - j + 1 : ℕ) : ℝ)) = J - j + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hjJ]; push_cast; ring
      have h2 : (1 + t - j) ^ (σ - 1) ≤ (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) := by
        rw [hcast]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hs1.le
      have h3 : (1 + t - j) ^ (σ - 1) / (1 + j) ≤ 2 / (2 + t) * (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
      linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  -- harmonic part
  have hH : ∑ j ∈ range (J + 1), 1 / (1 + (j : ℝ)) ≤ 1 + Real.log (1 + t) := by
    have e : ∑ j ∈ range (J + 1), 1 / (1 + (j : ℝ)) = (harmonic (J + 1) : ℝ) := by
      clear hterm
      induction (J + 1) with
      | zero => simp
      | succ M ih =>
        rw [sum_range_succ, ih, harmonic_succ]; push_cast; ring
    rw [e]
    refine (harmonic_le_one_add_log (J + 1)).trans ?_
    have : Real.log ((J + 1 : ℕ) : ℝ) ≤ Real.log (1 + t) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    linarith
  have hA2 : A ≤ 2 * (2 + t) ^ (σ - 1) := by
    rw [hA, Real.div_rpow (by linarith) (by norm_num)]
    rw [div_eq_mul_inv, mul_comm]
    have h2 : ((2 : ℝ) ^ (σ - 1))⁻¹ ≤ 2 := by
      rw [← Real.rpow_neg (by norm_num)]
      calc (2 : ℝ) ^ (-(σ - 1)) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have : 0 ≤ (2 + t) ^ (σ - 1) := by positivity
    nlinarith
  -- power part
  have hP : ∑ j ∈ range (J + 1), (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) ≤ (2 + t) ^ σ / σ := by
    have e : ∑ j ∈ range (J + 1), (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1) =
        ∑ m ∈ range (J + 1), (((m + 1 : ℕ) : ℝ)) ^ (σ - 1) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun m hm => ?_
      have : m < J + 1 := mem_range.1 hm
      congr 3; omega
    rw [e]
    refine (sum_rpow_le hσ0 hσ1.le (J + 1)).trans ?_
    gcongr
    push_cast; linarith
  have hpt : 0 < 2 + t := by linarith
  have hP2 : 2 / (2 + t) * ((2 + t) ^ σ / σ) = 2 / σ * (2 + t) ^ (σ - 1) := by
    rw [Real.rpow_sub_one hpt.ne']; field_simp
  have hA0 : 0 ≤ A := by positivity
  calc A * ∑ j ∈ range (J + 1), 1 / (1 + (j : ℝ)) +
        2 / (2 + t) * ∑ j ∈ range (J + 1), (((J - j + 1 : ℕ) : ℝ)) ^ (σ - 1)
      ≤ 2 * (2 + t) ^ (σ - 1) * (1 + Real.log (1 + t)) + 2 / (2 + t) * ((2 + t) ^ σ / σ) := by
        gcongr
    _ = _ := by rw [hP2]; ring

/-- **The weighted density bound.** -/
theorem weight_bound (f : ℕ → ℝ) {σ K : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hK : 0 ≤ K)
    (hC : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Ioc 0 ⌊y⌋₊, |f n| ≤ K * y * (1 + Real.log y) ^ (σ - 1))
    {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, |f n| / n / (1 + Real.log (x / n)) ≤
      Real.exp 1 * K * ((2 * (1 + Real.log (1 + Real.log x)) + 2 / σ) *
        (2 + Real.log x) ^ (σ - 1)) := by
  have hx0 : 0 < x := by linarith
  set t := Real.log x with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hx
  set J := ⌊t⌋₊ with hJ
  set jf : ℕ → ℕ := fun n => ⌊Real.log (x / n)⌋₊ with hjf
  have hmaps : ∀ n ∈ Ioc 0 ⌊x⌋₊, jf n ∈ range (J + 1) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.1 hn).1
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    rw [Real.log_div hx0.ne' hn0.ne']
    have := Real.log_nonneg hn1
    linarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ range (J + 1),
      ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j), |f n| / n / (1 + Real.log (x / n)) ≤
        Real.exp 1 * K * ((1 + t - j) ^ (σ - 1) / (1 + j)) := by
    intro j hj
    have hjJ : (j : ℝ) ≤ t := by
      have : j ≤ J := Nat.lt_succ_iff.1 (mem_range.1 hj)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le ht0)
    set y : ℝ := x * Real.exp (-j) with hy
    have hy1 : 1 ≤ y := by
      rw [hy, ← Real.exp_log hx0, ← Real.exp_add]
      exact Real.one_le_exp (by rw [← ht]; linarith)
    have hlogy : Real.log y = t - j := by
      rw [hy, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have hpt : ∀ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j),
        |f n| / n / (1 + Real.log (x / n)) ≤ (Real.exp (j + 1) / x / (1 + j)) * |f n| := by
      intro n hn
      obtain ⟨hn, hjn⟩ := mem_filter.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
      have hl0 : 0 ≤ Real.log (x / n) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.cast_le.2 (mem_Ioc.1 hn).2).trans (Nat.floor_le hx0.le)
      have h1 : (j : ℝ) ≤ Real.log (x / n) := by
        rw [← hjn]; exact Nat.floor_le hl0
      have h2 : Real.log (x / n) < j + 1 := by
        rw [← hjn]; exact Nat.lt_floor_add_one _
      have h3 : 1 / (n : ℝ) ≤ Real.exp (j + 1) / x := by
        have : x / n < Real.exp (j + 1) := by
          rw [← Real.exp_log (by positivity : 0 < x / n)]; exact Real.exp_lt_exp.mpr h2
        rw [div_lt_iff₀ hn0] at this
        rw [div_le_div_iff₀ hn0 hx0]; linarith
      have h4 : 1 / (1 + Real.log (x / n)) ≤ 1 / (1 + j) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hfa := abs_nonneg (f n)
      calc |f n| / n / (1 + Real.log (x / n)) = |f n| * (1 / n) * (1 / (1 + Real.log (x / n))) := by
            ring
        _ ≤ |f n| * (Real.exp (j + 1) / x) * (1 / (1 + j)) := by gcongr
        _ = _ := by ring
    have hsub : (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j) ⊆ Ioc 0 ⌊y⌋₊ := by
      intro n hn
      obtain ⟨hn, hjn⟩ := mem_filter.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
      have hl0 : 0 ≤ Real.log (x / n) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.cast_le.2 (mem_Ioc.1 hn).2).trans (Nat.floor_le hx0.le)
      have h1 : (j : ℝ) ≤ Real.log (x / n) := by
        rw [← hjn]; exact Nat.floor_le hl0
      refine mem_Ioc.2 ⟨(mem_Ioc.1 hn).1, Nat.le_floor ?_⟩
      have : Real.exp j ≤ x / n := by
        rw [← Real.exp_log (by positivity : 0 < x / n)]; exact Real.exp_le_exp.mpr h1
      rw [le_div_iff₀ hn0] at this
      rw [hy, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      linarith
    have hc0 : 0 ≤ Real.exp (j + 1) / x / (1 + j) := by positivity
    calc ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j), |f n| / n / (1 + Real.log (x / n))
        ≤ ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j), (Real.exp (j + 1) / x / (1 + j)) * |f n| :=
          sum_le_sum hpt
      _ = (Real.exp (j + 1) / x / (1 + j)) * ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n => jf n = j), |f n| := by
          rw [mul_sum]
      _ ≤ (Real.exp (j + 1) / x / (1 + j)) * ∑ n ∈ Ioc 0 ⌊y⌋₊, |f n| := by
          gcongr
          first | done | exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
      _ ≤ (Real.exp (j + 1) / x / (1 + j)) * (K * y * (1 + Real.log y) ^ (σ - 1)) := by
          gcongr; exact hC y hy1
      _ = Real.exp 1 * K * ((1 + t - j) ^ (σ - 1) / (1 + j)) := by
          rw [hlogy, hy]
          have e : Real.exp (j + 1) * Real.exp (-j) = Real.exp 1 := by
            rw [← Real.exp_add]; ring_nf
          field_simp
          all_goals (try rw [show (1 + (t - j)) = 1 + t - j by ring])
          all_goals linear_combination (K * (1 + t - j) ^ (σ - 1)) * e
  refine (sum_le_sum hblock).trans ?_
  rw [← mul_sum]
  have hE : 0 ≤ Real.exp 1 * K := by positivity
  exact mul_le_mul_of_nonneg_left (j_sum_le hσ0 hσ1 ht0) hE

end RamanujanTau.SelbergDelange2
