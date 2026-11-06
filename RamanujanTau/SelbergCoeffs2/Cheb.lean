/-
# Chebyshev bounds and summation by parts for `ΛR`

* `abel_Ioc`: `Σ_{n≤N} a_n w_n = Σ_{k≤N} (w_k − w_{k+1}) A(k) + w_{N+1} A(N)` (exact).
* `sum_mul_le_of_partial`: if `a ≥ 0`, `A(k) ≤ Bk` and `w` is non-increasing and `≥ 0`, then
  `Σ_{n≤N} a_n w_n ≤ B Σ_{n≤N} w_n`.
* `cheb_LamR`: `Σ_{n≤N} |ΛR(n)| ≤ B N` (Rankin–Selberg PNT `rs_PNT`; trivial bound on squares).
* `summable_LamR_nonprime`: `Σ_{n not prime} |ΛR(n)|/n < ∞` (repo's Weil-type bound
  `summable_vR_nonprime`, **no Deligne**).
* `LamR_prime`: `ΛR(p) = λ(p)² log p`.
-/
import RamanujanTau.SelbergCoeffs2.LogIdent

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs2

open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
open RamanujanTau.EdgeNonvanishing (lam)
open RamanujanTau.TauPNTUncond (vR vR_nonneg vR_prime rs_PNT summable_vR_nonprime)

noncomputable section

/-- **Summation by parts** on `Ioc 0 N`. -/
lemma abel_Ioc (a w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, a n * w n =
      ∑ k ∈ Ioc 0 N, (w k - w (k + 1)) * (∑ n ∈ Ioc 0 k, a n) +
        w (N + 1) * ∑ n ∈ Ioc 0 N, a n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), ih, sum_Ioc_succ_top (Nat.zero_le N),
      sum_Ioc_succ_top (Nat.zero_le N)]
    ring

lemma sum_mul_le_of_partial {a w : ℕ → ℝ} {B : ℝ} {N : ℕ} (_ha : ∀ n, 0 ≤ a n)
    (hA : ∀ k, k ≤ N → ∑ n ∈ Ioc 0 k, a n ≤ B * k)
    (hw : ∀ k, 1 ≤ k → k ≤ N → w (k + 1) ≤ w k) (hw0 : 0 ≤ w (N + 1)) :
    ∑ n ∈ Ioc 0 N, a n * w n ≤ B * ∑ n ∈ Ioc 0 N, w n := by
  have h1 := abel_Ioc (fun _ => (1 : ℝ)) w N
  simp only [one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one] at h1
  rw [abel_Ioc a w N, h1]
  have e1 : ∑ k ∈ Ioc 0 N, (w k - w (k + 1)) * (∑ n ∈ Ioc 0 k, a n) ≤
      ∑ k ∈ Ioc 0 N, B * ((w k - w (k + 1)) * k) := by
    refine sum_le_sum fun k hk => ?_
    have hk' := (mem_Ioc.mp hk).2
    have := mul_le_mul_of_nonneg_left (hA k hk') (sub_nonneg.mpr (hw k (mem_Ioc.mp hk).1 hk'))
    linarith
  have e2 : w (N + 1) * ∑ n ∈ Ioc 0 N, a n ≤ B * (w (N + 1) * N) := by
    have := mul_le_mul_of_nonneg_left (hA N le_rfl) hw0
    linarith
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by rw [mul_add, Finset.mul_sum]

/-! ## Bounds for `sqL` -/

lemma sqL_le_log (n : ℕ) : sqL n ≤ Real.log n := by
  unfold sqL
  split_ifs with h
  · refine vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | h0
    · rw [h0]; simp; exact Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast h0)
        (by exact_mod_cast Nat.sqrt_le_self n)
  · exact Real.log_natCast_nonneg n

lemma sum_sqL_le (N : ℕ) : ∑ n ∈ Ioc 0 N, sqL n ≤ N := by
  have hset : (Ioc 0 N).filter (fun n => Nat.sqrt n ^ 2 = n) =
      (Ioc 0 (Nat.sqrt N)).image (fun m => m ^ 2) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h0, hN⟩, hs⟩
      exact ⟨Nat.sqrt n, ⟨Nat.sqrt_pos.mpr h0, Nat.sqrt_le_sqrt hN⟩, hs⟩
    · rintro ⟨m, ⟨h0, hm⟩, rfl⟩
      refine ⟨⟨by positivity, ?_⟩, by rw [Nat.sqrt_eq']⟩
      calc m ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left hm 2
        _ ≤ N := Nat.sqrt_le' N
  have h1 : ∑ n ∈ Ioc 0 N, sqL n = ∑ n ∈ (Ioc 0 N).filter (fun n => Nat.sqrt n ^ 2 = n),
      vonMangoldt (Nat.sqrt n) := by
    rw [sum_filter]; rfl
  rw [h1, hset, sum_image (fun x _ y _ h => Nat.pow_left_injective two_ne_zero h)]
  simp only [Nat.sqrt_eq']
  set s := Nat.sqrt N
  calc ∑ m ∈ Ioc 0 s, vonMangoldt m ≤ ∑ m ∈ Ioc 0 s, (s : ℝ) := by
        refine sum_le_sum fun m hm => ?_
        rw [mem_Ioc] at hm
        refine vonMangoldt_le_log.trans ((Real.log_le_sub_one_of_pos (by
          exact_mod_cast hm.1)).trans ?_)
        have : (m : ℝ) ≤ s := by exact_mod_cast hm.2
        linarith
    _ = (s : ℝ) * s := by simp
    _ ≤ N := by
        have := Nat.sqrt_le' N
        rw [sq] at this
        exact_mod_cast this

lemma sum_vR_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ n ∈ Ioc 0 N, vR n ≤ B * N := by
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.mp ((rs_PNT.eventually (gt_mem_nhds
    (show (1 : ℝ) < 2 by norm_num)))))
  set S₀ := ∑ n ∈ range (N₀ + 1), vR n
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => vR_nonneg n
  refine ⟨4 + S₀, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : ∑ n ∈ Ioc 0 N, vR n ≤ ∑ n ∈ range (N + 1), vR n :=
    sum_le_sum_of_subset_of_nonneg (fun n hn => by
      rw [mem_Ioc] at hn; exact mem_range.mpr (by omega)) fun n _ _ => vR_nonneg n
  rcases le_or_gt N₀ (N + 1) with h | h
  · have := hN₀ (N + 1) h
    rw [div_lt_iff₀ (by positivity)] at this
    push_cast at this
    nlinarith
  · have : ∑ n ∈ range (N + 1), vR n ≤ S₀ :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun n _ _ => vR_nonneg n
    nlinarith

lemma abs_LamR_le (n : ℕ) : |LamR n| ≤ vR n + 2 * sqL n := by
  unfold LamR
  rw [abs_le]
  constructor <;> nlinarith [vR_nonneg n, sqL_nonneg n]

/-- **Chebyshev bound** `Σ_{n≤N} |ΛR(n)| ≤ BN` (unconditional). -/
theorem cheb_LamR : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ n ∈ Ioc 0 N, |LamR n| ≤ B * N := by
  obtain ⟨B, hB0, hB⟩ := sum_vR_le
  refine ⟨B + 2, by positivity, fun N => ?_⟩
  calc ∑ n ∈ Ioc 0 N, |LamR n| ≤ ∑ n ∈ Ioc 0 N, (vR n + 2 * sqL n) :=
        sum_le_sum fun n _ => abs_LamR_le n
    _ = ∑ n ∈ Ioc 0 N, vR n + 2 * ∑ n ∈ Ioc 0 N, sqL n := by rw [sum_add_distrib, mul_sum]
    _ ≤ B * N + 2 * N := by linarith [hB N, sum_sqL_le N]
    _ = (B + 2) * N := by ring

lemma sqL_prime {p : ℕ} (hp : p.Prime) : sqL p = 0 := by
  unfold sqL
  rw [if_neg]
  intro h
  have hd : Nat.sqrt p ∣ p := ⟨Nat.sqrt p, by rw [← sq]; exact h.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · rw [h1] at h; simp at h; exact hp.one_lt.ne h
  · rw [h1] at h
    have : p * p = p * 1 := by rw [← sq, h, mul_one]
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos this)

/-- `ΛR(p) = λ(p)² log p`. -/
lemma LamR_prime {p : ℕ} (hp : p.Prime) : LamR p = lam p ^ 2 * Real.log p := by
  rw [LamR, sqL_prime hp, vR_prime hp]; ring

lemma summable_sqL_div : Summable fun n : ℕ => sqL n / n := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective two_ne_zero
  refine (hinj.summable_iff (f := fun n : ℕ => sqL n / n) (fun n hn => by
    simp [sqL_zero_of_not hn])).mp ?_
  have hs : Summable fun m : ℕ => 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun m => div_nonneg (sqL_nonneg _) (Nat.cast_nonneg _))
    (fun m => ?_) hs
  simp only [Function.comp_apply, sqL_sq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : vonMangoldt m ≤ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 : (m : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring
    linarith [vonMangoldt_le_log (n := m)]
  have hm2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ (2 : ℝ) := by push_cast; norm_cast
  rw [hm2, div_le_iff₀ (by positivity)]
  calc vonMangoldt m ≤ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := hl
    _ = 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) * (m : ℝ) ^ (2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hm0]; norm_num

/-- The non-prime part of `ΛR(n)/n` is absolutely summable (**no Deligne**). -/
theorem summable_LamR_nonprime :
    Summable fun n : ℕ => (if n.Prime then 0 else |LamR n|) / n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_vR_nonprime.add (summable_sqL_div.mul_left 2))
  split_ifs with h
  · simp only [zero_div, zero_add]
    exact mul_nonneg (by norm_num) (div_nonneg (sqL_nonneg _) (Nat.cast_nonneg _))
  · rw [mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right (abs_LamR_le n) (Nat.cast_nonneg _)

end

end RamanujanTau.SelbergCoeffs2
