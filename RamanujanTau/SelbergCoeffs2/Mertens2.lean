/-
# Mertens' second theorem for `λ(p)²` (unconditional)

    Σ_{p≤N} λ(p)²/p = log log N + c_Δ + o(1).

From Mertens I (`mertens1_prime`: `P(N) = Σ_{p≤N} λ(p)² log p/p = log N + R(N)`, `|R| ≤ E`) by
summation by parts against `w(k) = 1/log k`:

    Σ_{p≤N} λ(p)²/p = Σ_{k≤N} (w_k − w_{k+1}) P(k) + w_{N+1} P(N)
                    = log log (N+1) + Σ_{k≤N} h_k + P(N)/log(N+1),

with `h_k = (w_k − w_{k+1})P(k) − (log log(k+1) − log log k)`,
`|h_k| ≤ 1/(k² log²2) + E (w_k − w_{k+1})` summable.  Hence `c_Δ = 1 + Σ_k h_k`.
-/
import RamanujanTau.SelbergCoeffs2.Mertens1

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs2

open Finset Filter Topology
open RamanujanTau.EdgeNonvanishing (lam)

noncomputable section

/-- `P(N) = Σ_{p≤N} λ(p)² log p / p`. -/
def PP (N : ℕ) : ℝ := ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 * Real.log p / p
/-- `T(N) = Σ_{p≤N} λ(p)²/p`. -/
def TT (N : ℕ) : ℝ := ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p
/-- `w(k) = 1/log k`. -/
def ww (k : ℕ) : ℝ := 1 / Real.log k
/-- `log log k`. -/
def LL (k : ℕ) : ℝ := Real.log (Real.log k)

/-- The summand `h_k`. -/
def hh (k : ℕ) : ℝ := (ww k - ww (k + 1)) * PP k - (LL (k + 1) - LL k)

lemma PP_one : PP 1 = 0 := by
  simp [PP, Finset.filter_singleton, Nat.not_prime_one]

lemma TT_eq_abel (N : ℕ) :
    TT N = ∑ k ∈ Ioc 0 N, (ww k - ww (k + 1)) * PP k + ww (N + 1) * PP N := by
  set b : ℕ → ℝ := fun n => if n.Prime then lam n ^ 2 * Real.log n / n else 0
  have hb : ∀ k, ∑ n ∈ Ioc 0 k, b n = PP k := fun k => by rw [PP, sum_filter]
  have hab := abel_Ioc b ww N
  simp only [hb] at hab
  rw [← hab, TT, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  simp only [b, ww]
  split_ifs with hp
  · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp
  · simp

lemma sum_LL (N : ℕ) : ∑ k ∈ Ioc 0 N, (LL (k + 1) - LL k) = LL (N + 1) := by
  induction N with
  | zero => simp [LL]
  | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le N), ih]; ring

lemma TT_decomp (N : ℕ) :
    TT N - LL N = ∑ k ∈ Ioc 0 N, hh k + (LL (N + 1) - LL N) + ww (N + 1) * PP N := by
  rw [TT_eq_abel]
  simp only [hh]
  rw [sum_sub_distrib, sum_LL]
  ring

/-- Elementary log bounds: for `0 < a ≤ b`, `1 − a/b ≤ log b − log a ≤ b/a − 1`. -/
lemma log_sub_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 - a / b ≤ Real.log b - Real.log a ∧ Real.log b - Real.log a ≤ b / a - 1 := by
  have hb : 0 < b := ha.trans_le hab
  constructor
  · have := Real.log_le_sub_one_of_pos (show 0 < a / b by positivity)
    rw [Real.log_div ha.ne' hb.ne'] at this; linarith
  · have := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
    rw [Real.log_div hb.ne' ha.ne'] at this; linarith

lemma log_two_le_log {k : ℕ} (hk : 2 ≤ k) : Real.log 2 ≤ Real.log k :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hk)

/-- `|h_k| ≤ 1/(k² log² 2) + E (w_k − w_{k+1})` for `k ≥ 2`. -/
lemma abs_hh_le {E : ℝ} (hE : ∀ N : ℕ, 1 ≤ N → |PP N - Real.log N| ≤ E) {k : ℕ} (hk : 2 ≤ k) :
    |hh k| ≤ 1 / (Real.log 2 ^ 2 * (k : ℝ) ^ 2) + E * (ww k - ww (k + 1)) := by
  set L := Real.log k
  set L' := Real.log (k + 1 : ℕ)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ L := log_two_le_log hk
  have hL0 : 0 < L := hl2.trans_le hL
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLL' : L ≤ L' := Real.log_le_log hk0 (by push_cast; linarith)
  have hL'0 : 0 < L' := hL0.trans_le hLL'
  have hd : L' - L ≤ 1 / k := log_succ_sub_le (by omega)
  have hd0 : 0 ≤ L' - L := by linarith
  obtain ⟨lb, ub⟩ := log_sub_bounds hL0 hLL'
  set R := PP k - L
  have hR : |R| ≤ E := hE k (by omega)
  have hw : ww k - ww (k + 1) = (L' - L) / (L * L') := by
    simp only [ww]; rw [div_sub_div _ _ hL0.ne' hL'0.ne']; ring
  have hw0 : 0 ≤ ww k - ww (k + 1) := by rw [hw]; positivity
  have hdecomp : hh k = ((1 - L / L') - (Real.log L' - Real.log L)) + (ww k - ww (k + 1)) * R := by
    have hLLeq : LL (k + 1) - LL k = Real.log L' - Real.log L := rfl
    simp only [hh]
    have : PP k = L + R := by simp [R]
    rw [hLLeq, this, hw]
    field_simp
    ring
  have h1 : |(1 - L / L') - (Real.log L' - Real.log L)| ≤ (L' - L) ^ 2 / (L * L') := by
    have e : (L' / L - 1) - (1 - L / L') = (L' - L) ^ 2 / (L * L') := by field_simp
    rw [abs_le]; constructor <;> linarith
  have h2 : (L' - L) ^ 2 / (L * L') ≤ 1 / (Real.log 2 ^ 2 * (k : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (L' - L) ^ 2 * (k : ℝ) ^ 2 ≤ 1 := by
      have := mul_le_mul hd hd hd0 (by positivity)
      have e2 : 1 / (k : ℝ) * (1 / k) * (k : ℝ) ^ 2 = 1 := by field_simp
      nlinarith
    have hLL : Real.log 2 ^ 2 ≤ L * L' := by nlinarith
    nlinarith [sq_nonneg (L' - L), sq_nonneg (k : ℝ)]
  have h3 : |(ww k - ww (k + 1)) * R| ≤ E * (ww k - ww (k + 1)) := by
    rw [abs_mul, abs_of_nonneg hw0, mul_comm]
    exact mul_le_mul_of_nonneg_right hR hw0
  rw [hdecomp]
  calc _ ≤ |(1 - L / L') - (Real.log L' - Real.log L)| + |(ww k - ww (k + 1)) * R| := abs_add_le _ _
    _ ≤ _ := add_le_add (h1.trans h2) h3

lemma ww_antitone {k : ℕ} (hk : 2 ≤ k) : ww (k + 1) ≤ ww k := by
  have hL0 : 0 < Real.log k := (Real.log_pos (by norm_num)).trans_le (log_two_le_log hk)
  unfold ww
  exact one_div_le_one_div_of_le hL0 (Real.log_le_log (by exact_mod_cast (show 0 < k by omega))
    (by push_cast; linarith))

lemma summable_ww_diff : Summable fun k : ℕ => ww (k + 2) - ww (k + 3) := by
  refine summable_of_sum_range_le (c := ww 2) (fun k => sub_nonneg.mpr (ww_antitone (by omega)))
    (fun n => ?_)
  rw [Finset.sum_range_sub' (fun k => ww (k + 2)) n]
  have : 0 ≤ ww (n + 2) := by
    unfold ww; exact div_nonneg zero_le_one (Real.log_natCast_nonneg _)
  simp only [zero_add]; linarith

lemma summable_hh : Summable hh := by
  obtain ⟨E, hE⟩ := mertens1_prime
  have hE' : ∀ N : ℕ, 1 ≤ N → |PP N - Real.log N| ≤ E := hE
  rw [← summable_nat_add_iff 2]
  have hs1 : Summable fun k : ℕ => 1 / (Real.log 2 ^ 2 * ((k + 2 : ℕ) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff 2).mpr
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (1 / Real.log 2 ^ 2))
    refine this.congr fun k => ?_
    push_cast; field_simp
  refine Summable.of_norm_bounded (hs1.add (summable_ww_diff.mul_left E)) fun k => ?_
  rw [Real.norm_eq_abs]
  have := abs_hh_le hE' (k := k + 2) (by omega)
  simpa [add_assoc] using this

lemma tendsto_inv_nat_log : Tendsto (fun N : ℕ => 1 / (Real.log 2 * N)) atTop (𝓝 0) := by
  have := tendsto_const_div_atTop_nhds_zero_nat (1 / Real.log 2)
  refine this.congr fun N => ?_
  field_simp

lemma tendsto_LL_succ_sub : Tendsto (fun N : ℕ => LL (N + 1) - LL N) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_nat_log
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hL0 : 0 < Real.log N := (Real.log_pos (by norm_num)).trans_le (log_two_le_log hN)
    have h := (log_sub_bounds hL0 (Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
      (by push_cast; linarith : (N : ℝ) ≤ (N + 1 : ℕ)))).1
    have : 0 ≤ 1 - Real.log N / Real.log (N + 1 : ℕ) := by
      rw [sub_nonneg, div_le_one (hL0.trans_le (Real.log_le_log (by exact_mod_cast
        (show 0 < N by omega)) (by push_cast; linarith)))]
      exact Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by push_cast; linarith)
    simp only [LL]; linarith
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hL := log_two_le_log hN
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL0 : 0 < Real.log N := hl2.trans_le hL
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLL' : Real.log N ≤ Real.log (N + 1 : ℕ) := Real.log_le_log hN0 (by push_cast; linarith)
    have h := (log_sub_bounds hL0 hLL').2
    have hd := log_succ_sub_le (k := N) (by omega)
    simp only [LL]
    calc Real.log (Real.log (N + 1 : ℕ)) - Real.log (Real.log N)
        ≤ Real.log (N + 1 : ℕ) / Real.log N - 1 := h
      _ = (Real.log (N + 1 : ℕ) - Real.log N) / Real.log N := by field_simp
      _ ≤ (1 / N) / Real.log 2 := by
          apply div_le_div₀ (by positivity) hd hl2 hL
      _ = 1 / (Real.log 2 * N) := by field_simp

lemma tendsto_log_div_log_succ :
    Tendsto (fun N : ℕ => Real.log N / Real.log (N + 1 : ℕ)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 - Real.log N / Real.log (N + 1 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_inv_nat_log
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hL0 : 0 < Real.log N := (Real.log_pos (by norm_num)).trans_le (log_two_le_log hN)
      have hLL' : Real.log N ≤ Real.log (N + 1 : ℕ) := Real.log_le_log hN0 (by push_cast; linarith)
      rw [sub_nonneg, div_le_one (hL0.trans_le hLL')]; exact hLL'
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hL := log_two_le_log hN
      have hL0 : 0 < Real.log N := hl2.trans_le hL
      have hLL' : Real.log N ≤ Real.log (N + 1 : ℕ) := Real.log_le_log hN0 (by push_cast; linarith)
      have hd := log_succ_sub_le (k := N) (by omega)
      calc 1 - Real.log N / Real.log (N + 1 : ℕ)
          = (Real.log (N + 1 : ℕ) - Real.log N) / Real.log (N + 1 : ℕ) := by
            rw [sub_div, div_self (hL0.trans_le hLL').ne']
        _ ≤ (1 / N) / Real.log 2 := div_le_div₀ (by positivity) hd hl2 (hL.trans hLL')
        _ = 1 / (Real.log 2 * N) := by field_simp
  have := h.const_sub 1
  simpa using this

lemma tendsto_ww_PP : Tendsto (fun N : ℕ => ww (N + 1) * PP N) atTop (𝓝 1) := by
  obtain ⟨E, hE⟩ := mertens1_prime
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hR : Tendsto (fun N : ℕ => (PP N - Real.log N) / Real.log (N + 1 : ℕ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => E / Real.log (N + 1 : ℕ)) atTop (𝓝 0) :=
      hlog.const_div_atTop E
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hl : 0 < Real.log (N + 1 : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right (hE N hN) hl.le
  have := tendsto_log_div_log_succ.add hR
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hl : Real.log (N + 1 : ℕ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))).ne'
  simp only [ww]; field_simp; ring

/-- The Mertens constant for `λ(p)²`: `c_Δ = 1 + Σ_k h_k`. -/
def cMertens : ℝ := 1 + ∑' k, hh k

/-- **Mertens II for `L(Δ ⊗ Δ)`** (unconditional):
`Σ_{p≤N} λ(p)²/p − log log N → c_Δ`. -/
theorem mertens2 :
    Tendsto (fun N : ℕ => ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p - Real.log (Real.log N))
      atTop (𝓝 cMertens) := by
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Ioc 0 N, hh k) atTop (𝓝 (∑' k, hh k)) := by
    have h := (summable_hh.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    have h0 : hh 0 = 0 := by simp [hh, ww, LL, PP]
    induction N with
    | zero => simp [h0]
    | succ N ih => rw [sum_range_succ, ih, sum_Ioc_succ_top (Nat.zero_le N)]
  have := (hsum.add tendsto_LL_succ_sub).add tendsto_ww_PP
  rw [add_zero, add_comm (∑' k, hh k) 1] at this
  refine this.congr fun N => ?_
  have := TT_decomp N
  simp only [TT] at this
  simp only [LL] at this ⊢
  linarith

/-- **Uniform form**: `|Σ_{p≤N} λ(p)²/p − log log N| ≤ C` for all `N`. -/
theorem mertens2_bound : ∃ C : ℝ, ∀ N : ℕ,
    |∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p - Real.log (Real.log N)| ≤ C := by
  set a : ℕ → ℝ := fun N =>
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p - Real.log (Real.log N)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (mertens2.eventually (Metric.ball_mem_nhds cMertens one_pos))
  refine ⟨|cMertens| + 1 + ∑ n ∈ range N₀, |a n|, fun N => ?_⟩
  have h0 : 0 ≤ ∑ n ∈ range N₀, |a n| := sum_nonneg fun _ _ => abs_nonneg _
  rcases le_or_gt N₀ N with h | h
  · have := hN₀ N h
    rw [Real.dist_eq] at this
    have : |a N| ≤ |cMertens| + 1 := by
      have := abs_sub_abs_le_abs_sub (a N) cMertens; linarith
    show |a N| ≤ _
    linarith
  · have := single_le_sum (f := fun n => |a n|) (fun _ _ => abs_nonneg _) (mem_range.mpr h)
    show |a N| ≤ _
    linarith [abs_nonneg cMertens]

end

end RamanujanTau.SelbergCoeffs2
