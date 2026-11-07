/-
# Mertens' first theorem for the Rankin–Selberg coefficients (unconditional)

    Σ_{n≤N} ΛR(n)/n = log N + O(1),        Σ_{p≤N} λ(p)² log p / p = log N + O(1).

Elementary (Mertens' proof): with `F(x) = Σ_{n≤x} λ(n)² = c x + O(x^{3/5})` (`rs_partial`,
from `RankinExact`) and `S(N) = Σ_{n≤N} λ(n)² log n`,

* `S(N) = c N log N + O(N)` (summation by parts against `F(k) ≤ Kk`);
* `S(N) = Σ_{d≤N} ΛR(d) F(N/d)` (`rsb_mul_log`) `= cN Σ_{d≤N} ΛR(d)/d + O(N^{3/5} Σ_{d≤N}|ΛR(d)|d^{−3/5})`
  and the last sum is `≪ N^{2/5}` by the Chebyshev bound `cheb_LamR`;
* the prime powers contribute `O(1)` by `summable_LamR_nonprime`.

No Deligne anywhere (prime powers are controlled by the repo's unconditional Weil-type bound).
-/
import RamanujanTau.SelbergCoeffs2.Cheb

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs2

open Finset Filter Topology ArithmeticFunction
open RamanujanTau.EdgeNonvanishing (lam rsb rsb_nonneg rsc rs_partial rs_partial_le)

noncomputable section

lemma Ioc_zero_eq_Icc_one (N : ℕ) : Ioc 0 N = Icc 1 N := by
  ext n; simp [mem_Ioc, mem_Icc]; omega

lemma rsc_pos : 0 < rsc := by
  unfold rsc
  have := RankinError.petNormSq_pos
  have hπ := Real.pi_pos
  positivity

/-- `Σ_{d≤N} d^{−3/5} ≤ (5/2) N^{2/5}`. -/
lemma sum_rpow_neg_le (N : ℕ) :
    ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 5 / 2 * (N : ℝ) ^ (2 / 5 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N)]
    set x : ℝ := ((N + 1 : ℕ) : ℝ)
    have hx : 1 ≤ x := by simp [x]
    have hx0 : 0 < x := by linarith
    -- Bernoulli: (1 − 1/x)^{2/5} ≤ 1 − (2/5)/x
    have hb := rpow_one_add_le_one_add_mul_self (s := -(1 / x)) (p := 2 / 5)
      (by rw [neg_le_neg_iff]; exact (div_le_one hx0).mpr hx) (by norm_num) (by norm_num)
    have e1 : (1 + -(1 / x)) = (N : ℝ) / x := by
      simp only [x]; push_cast; field_simp; ring
    rw [e1, Real.div_rpow (Nat.cast_nonneg _) hx0.le] at hb
    have hxp : 0 < x ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have e2 : x ^ (2 / 5 : ℝ) * (1 / x) = x ^ (-(3 / 5 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hx0]; norm_num
    have hN : (N : ℝ) ^ (2 / 5 : ℝ) ≤ x ^ (2 / 5 : ℝ) - 2 / 5 * x ^ (-(3 / 5 : ℝ)) := by
      rw [div_le_iff₀ hxp] at hb
      nlinarith
    linarith

/-- `S(N) = Σ λ(n)² log n` and `F(N) = Σ λ(n)²` over `Ioc 0 N`. -/
def SS (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, rsb n * Real.log n
def FF (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, rsb n

lemma FF_nonneg (N : ℕ) : 0 ≤ FF N := sum_nonneg fun n _ => rsb_nonneg n

lemma SS_le (N : ℕ) : SS N ≤ FF N * Real.log N := by
  unfold SS FF
  rw [sum_mul]
  refine sum_le_sum fun n hn => ?_
  rw [mem_Ioc] at hn
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hn.1)
    (by exact_mod_cast hn.2)) (rsb_nonneg n)

lemma log_succ_sub_le {k : ℕ} (hk : 1 ≤ k) : Real.log (k + 1 : ℕ) - Real.log k ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
  push_cast; field_simp; ring

lemma SS_ge : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, FF N * Real.log N - K * N ≤ SS N := by
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  refine ⟨K, hK0, fun N => ?_⟩
  have hab := abel_Ioc rsb (fun n => Real.log n) N
  have hF : ∀ k, FF k ≤ K * k := fun k => by rw [FF, Ioc_zero_eq_Icc_one]; exact hK k
  have h1 : ∀ k ∈ Ioc 0 N, -K ≤ (Real.log k - Real.log (k + 1 : ℕ)) * FF k := by
    intro k hk
    have hk1 := (mem_Ioc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hd := log_succ_sub_le hk1
    have hd0 : 0 ≤ Real.log (k + 1 : ℕ) - Real.log k :=
      sub_nonneg.mpr (Real.log_le_log hk0 (by push_cast; linarith))
    have : (Real.log (k + 1 : ℕ) - Real.log k) * FF k ≤ (1 / k) * (K * k) :=
      mul_le_mul hd (hF k) (FF_nonneg k) (by positivity)
    rw [show (1 / (k : ℝ)) * (K * k) = K by field_simp] at this
    linarith
  have h2 : -(K * N) ≤ ∑ k ∈ Ioc 0 N, (Real.log k - Real.log (k + 1 : ℕ)) * FF k := by
    have := sum_le_sum h1
    simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at this
    linarith
  have h3 : FF N * Real.log N ≤ Real.log (N + 1 : ℕ) * FF N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [FF]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (by exact_mod_cast hN)
      (by push_cast; linarith)) (FF_nonneg N)
  have hS : SS N = ∑ k ∈ Ioc 0 N, (Real.log k - Real.log (k + 1 : ℕ)) * FF k +
      Real.log (N + 1 : ℕ) * FF N := by
    rw [SS, hab]; rfl
  linarith

/-- `S(N) = Σ_{d≤N} ΛR(d) F(⌊N/d⌋)`. -/
lemma SS_eq (N : ℕ) : SS N = ∑ d ∈ Ioc 0 N, LamR d * FF (N / d) := by
  have h := sum_Ioc_mul_eq_sum_sum LamRA rsbA N
  simp only [LamRA_apply, rsbA_apply] at h
  rw [SS]; simp only [FF]; rw [← h]
  exact sum_congr rfl fun n _ => rsb_mul_log n

lemma FF_approx : ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < d → d ≤ N →
    |FF (N / d) - rsc * ((N : ℝ) / d)| ≤ C * ((N : ℝ) / d) ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial
  refine ⟨C + rsc, by linarith [rsc_pos], fun N d hd hdN => ?_⟩
  set m := N / d
  have hm1 : 1 ≤ m := Nat.div_pos hdN hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hmle : (m : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hmlt : (N : ℝ) / d < m + 1 := by
    rw [div_lt_iff₀ hd0]
    have := Nat.lt_div_mul_add (a := N) hd
    have h' : (N : ℝ) < (m : ℝ) * d + d := by exact_mod_cast this
    linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / d := le_trans (by exact_mod_cast hm1) hmle
  have hpow1 : 1 ≤ ((N : ℝ) / d) ^ (3 / 5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hmpow : (m : ℝ) ^ (3 / 5 : ℝ) ≤ ((N : ℝ) / d) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hmle (by norm_num)
  have h1 : |FF m - rsc * m| ≤ C * (m : ℝ) ^ (3 / 5 : ℝ) := by
    rw [FF, Ioc_zero_eq_Icc_one]; exact hC m hm1
  have h2 : |rsc * m - rsc * ((N : ℝ) / d)| ≤ rsc * ((N : ℝ) / d) ^ (3 / 5 : ℝ) := by
    rw [abs_le]; constructor <;> nlinarith [rsc_pos]
  calc |FF m - rsc * ((N : ℝ) / d)| ≤ |FF m - rsc * m| + |rsc * m - rsc * ((N : ℝ) / d)| := by
        have := abs_add_le (FF m - rsc * m) (rsc * m - rsc * ((N : ℝ) / d))
        rwa [show FF m - rsc * m + (rsc * m - rsc * ((N : ℝ) / d)) = FF m - rsc * ((N : ℝ) / d)
          by ring] at this
    _ ≤ C * ((N : ℝ) / d) ^ (3 / 5 : ℝ) + rsc * ((N : ℝ) / d) ^ (3 / 5 : ℝ) := by
        gcongr; exact h1.trans (mul_le_mul_of_nonneg_left hmpow hC0)
    _ = (C + rsc) * ((N : ℝ) / d) ^ (3 / 5 : ℝ) := by ring

/-- **Mertens I for `ΛR`**: `|Σ_{d≤N} ΛR(d)/d − log N| ≤ E` for all `N ≥ 1`. -/
theorem mertens1_LamR : ∃ E : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ d ∈ Ioc 0 N, LamR d / d - Real.log N| ≤ E := by
  obtain ⟨C, hC0, hC⟩ := FF_approx
  obtain ⟨B, hB0, hB⟩ := cheb_LamR
  obtain ⟨K, hK0, hK⟩ := SS_ge
  obtain ⟨C1, hC10, hC1⟩ := rs_partial
  have hc := rsc_pos
  refine ⟨(5 / 2 * C * B + K + 5 / 2 * C1) / rsc, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set Sg := ∑ d ∈ Ioc 0 N, LamR d / d
  -- (E): convolution side
  have hE : |SS N - rsc * N * Sg| ≤ 5 / 2 * C * B * N := by
    rw [SS_eq, mul_sum, ← sum_sub_distrib]
    have hterm : ∀ d ∈ Ioc 0 N, |LamR d * FF (N / d) - rsc * N * (LamR d / d)| ≤
        C * (N : ℝ) ^ (3 / 5 : ℝ) * (|LamR d| * (d : ℝ) ^ (-(3 / 5 : ℝ))) := by
      intro d hd
      rw [mem_Ioc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
      have e : LamR d * FF (N / d) - rsc * N * (LamR d / d) =
          LamR d * (FF (N / d) - rsc * ((N : ℝ) / d)) := by field_simp
      rw [e, abs_mul]
      have h := hC N d hd.1 hd.2
      have hdiv : ((N : ℝ) / d) ^ (3 / 5 : ℝ) = (N : ℝ) ^ (3 / 5 : ℝ) * (d : ℝ) ^ (-(3 / 5 : ℝ)) := by
        rw [Real.div_rpow hN0.le hd0.le, Real.rpow_neg hd0.le, div_eq_mul_inv]
      calc |LamR d| * |FF (N / d) - rsc * ((N : ℝ) / d)|
          ≤ |LamR d| * (C * ((N : ℝ) / d) ^ (3 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = _ := by rw [hdiv]; ring
    have hmaj : ∑ d ∈ Ioc 0 N, |LamR d| * (d : ℝ) ^ (-(3 / 5 : ℝ)) ≤
        B * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(3 / 5 : ℝ)) := by
      refine sum_mul_le_of_partial (fun n => abs_nonneg _) (fun k _ => hB k) ?_ (by positivity)
      intro k hk _
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      exact Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by norm_num)
    have hsr := sum_rpow_neg_le N
    have hNN : (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    calc |∑ d ∈ Ioc 0 N, (LamR d * FF (N / d) - rsc * N * (LamR d / d))|
        ≤ ∑ d ∈ Ioc 0 N, |LamR d * FF (N / d) - rsc * N * (LamR d / d)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 N, C * (N : ℝ) ^ (3 / 5 : ℝ) * (|LamR d| * (d : ℝ) ^ (-(3 / 5 : ℝ))) :=
          sum_le_sum hterm
      _ = C * (N : ℝ) ^ (3 / 5 : ℝ) * ∑ d ∈ Ioc 0 N, |LamR d| * (d : ℝ) ^ (-(3 / 5 : ℝ)) := by
          rw [mul_sum]
      _ ≤ C * (N : ℝ) ^ (3 / 5 : ℝ) * (B * (5 / 2 * (N : ℝ) ^ (2 / 5 : ℝ))) := by
          gcongr; exact hmaj.trans (mul_le_mul_of_nonneg_left hsr hB0)
      _ = 5 / 2 * C * B * ((N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ)) := by ring
      _ = 5 / 2 * C * B * N := by rw [hNN]
  -- (A,B): `S = cN log N + O(N)`
  have hlog : Real.log N ≤ 5 / 2 * (N : ℝ) ^ (2 / 5 : ℝ) := by
    have := Real.log_le_rpow_div hN0.le (by norm_num : (0 : ℝ) < 2 / 5)
    linarith [show (N : ℝ) ^ (2 / 5 : ℝ) / (2 / 5) = 5 / 2 * (N : ℝ) ^ (2 / 5 : ℝ) by ring]
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hFN : |FF N - rsc * N| ≤ C1 * (N : ℝ) ^ (3 / 5 : ℝ) := by
    rw [FF, Ioc_zero_eq_Icc_one]; exact hC1 N hN
  have hNN : (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hF2 : |FF N * Real.log N - rsc * N * Real.log N| ≤ 5 / 2 * C1 * N := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hlog0]
    calc |FF N - rsc * N| * Real.log N ≤ C1 * (N : ℝ) ^ (3 / 5 : ℝ) * (5 / 2 * (N : ℝ) ^ (2 / 5 : ℝ)) :=
          mul_le_mul hFN hlog hlog0 (by positivity)
      _ = 5 / 2 * C1 * ((N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ)) := by ring
      _ = 5 / 2 * C1 * N := by rw [hNN]
  have hSl := SS_le N
  have hSg := hK N
  have hmain : |rsc * N * (Sg - Real.log N)| ≤ (5 / 2 * C * B + K + 5 / 2 * C1) * N := by
    rw [abs_le] at hE hF2 ⊢
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by positivity : 0 < rsc * N)] at hmain
  rw [le_div_iff₀ hc]
  have : rsc * N * |Sg - Real.log N| ≤ ((5 / 2 * C * B + K + 5 / 2 * C1)) * N := hmain
  nlinarith

/-- **Mertens I for `λ(p)²`** (unconditional):
`|Σ_{p≤N} λ(p)² log p / p − log N| ≤ E` for all `N ≥ 1`. -/
theorem mertens1_prime : ∃ E : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 * Real.log p / p - Real.log N| ≤ E := by
  obtain ⟨E, hE⟩ := mertens1_LamR
  set M := ∑' n : ℕ, (if n.Prime then 0 else |LamR n|) / n
  refine ⟨E + M, fun N hN => ?_⟩
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime (fun d => LamR d / d)
  have hp : ∑ p ∈ (Ioc 0 N).filter Nat.Prime, LamR p / p =
      ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 * Real.log p / p :=
    sum_congr rfl fun p hp => by rw [LamR_prime (mem_filter.mp hp).2]
  have hnp : |∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), LamR d / d| ≤ M := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), |LamR d / d|
        = ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), (if d.Prime then 0 else |LamR d|) / d :=
          sum_congr rfl fun d hd => by
            rw [if_neg (mem_filter.mp hd).2, abs_div, Nat.abs_cast]
      _ ≤ M := summable_LamR_nonprime.sum_le_tsum _ (fun n _ => by positivity)
  have h := hE N hN
  rw [← hsplit, hp] at h
  rw [abs_le] at h hnp ⊢
  constructor <;> linarith

end

end RamanujanTau.SelbergCoeffs2
