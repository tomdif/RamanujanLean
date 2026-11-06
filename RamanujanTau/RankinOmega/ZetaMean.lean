/-
# Uniform mean square of `ζ` to the right of the critical line

    ∫_T^{2T} |ζ(u − it)|² dt ≤ C T          (3/4 ≤ u ≤ 1, T ≥ 1),

with `C` independent of `u` and `T`. Proof: approximate `ζ(u−it)` on `[T, 2T]` by the Dirichlet
polynomial `∑_{n≤N} n^{−u+it}`, `N = ⌈T^{4/3}⌉`, with error `≤ 6` (`ZetaApprox.norm_zeta_sub_le`), and
apply the weak Montgomery–Vaughan mean value theorem `MeanSquare.mv_poly`:
`∑ n^{−2u} ≤ ζ(3/2)`, `H_N ∑ n^{1−2u} ≪ N^{5/8} ≪ T^{5/6}`.
-/
import RamanujanTau.RankinOmega.ZetaApprox
import RamanujanTau.MeanSquare.Poly

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.MeanSquare (dpoly ex H H_le_one_add_log mv_poly continuous_dpoly)

/-- `x^r ≤ y` from `x^{rk} ≤ y^k`. -/
lemma rpow_le_of_pow_le {x y r : ℝ} {k : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hk : k ≠ 0)
    (h : x ^ (r * k) ≤ y ^ k) : x ^ r ≤ y := by
  have e : (x ^ r) ^ k = x ^ (r * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hx r) hy hk, e]
  exact h

/-- `∑_{n ≤ N} n^{−1/2} ≤ 2 √N`. -/
lemma sum_inv_sqrt_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set a := Real.sqrt N
    set b := Real.sqrt ((N + 1 : ℕ) : ℝ)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
    have hab : b ^ 2 = a ^ 2 + 1 := by
      simp only [a, b, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    have hle : a ≤ b := by nlinarith
    have : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb]; nlinarith
    linarith

/-- The Dirichlet polynomial `∑ n^{−u+it}` is the conjugate of `dpoly`. -/
lemma cpow_eq_conj_ex (n : ℕ) (hn : 1 ≤ n) (u t : ℝ) :
    (n : ℂ) ^ (-((u : ℂ) - t * I)) =
      ((((n : ℝ) ^ (-u) : ℝ)) : ℂ) * (starRingEnd ℂ) (ex (-Real.log n) t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [RamanujanTau.MeanSquare.conj_ex, neg_neg, ex, Complex.cpow_def_of_ne_zero hnc,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hn0.le,
    Real.rpow_def_of_pos hn0, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma norm_sum_cpow_eq (N : ℕ) (u t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((u : ℂ) - t * I))‖ =
      ‖dpoly (fun n => ((((n : ℝ) ^ (-u) : ℝ)) : ℂ)) N t‖ := by
  have e : ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((u : ℂ) - t * I)) =
      (starRingEnd ℂ) (dpoly (fun n => ((((n : ℝ) ^ (-u) : ℝ)) : ℂ)) N t) := by
    unfold dpoly
    rw [map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [cpow_eq_conj_ex n hn.1, map_mul, Complex.conj_ofReal]
  rw [e, Complex.norm_conj]

/-- **Uniform mean square of `ζ` on `3/4 ≤ Re s ≤ 1`, below the real axis.** -/
theorem zeta_mean_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 3 / 4 ≤ u → u ≤ 1 → ∀ T : ℝ, 1 ≤ T →
    ∫ t in T..2 * T, ‖riemannZeta ((u : ℂ) - t * I)‖ ^ 2 ≤ C * T := by
  have hsum32 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    Real.summable_nat_rpow.2 (by norm_num)
  set S32 : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ) with hS32
  have hS320 : 0 ≤ S32 := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨4 * S32 + 504, by positivity, fun u hu1 hu2 T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set v : ℝ := T ^ ((1 : ℝ) / 3) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hT (by norm_num)
  have hTv : T = v ^ 3 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  set N : ℕ := ⌈v ^ 4⌉₊ with hN
  have hNlo : v ^ 4 ≤ N := Nat.le_ceil _
  have hv4 : 1 ≤ v ^ 4 := one_le_pow₀ hv1
  have hNhi : (N : ℝ) ≤ 2 * v ^ 4 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ v ^ 4 by positivity)
    linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans hv4 hNlo
    exact_mod_cast this
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set b : ℕ → ℂ := fun n => ((((n : ℝ) ^ (-u) : ℝ)) : ℂ) with hb
  -- pointwise approximation
  have happrox : ∀ t ∈ Icc T (2 * T),
      ‖riemannZeta ((u : ℂ) - t * I)‖ ^ 2 ≤ 2 * ‖dpoly b N t‖ ^ 2 + 72 := by
    intro t ht
    set s : ℂ := (u : ℂ) - t * I with hs
    have hsre : s.re = u := by simp [hs]
    have hsim : s.im = -t := by simp [hs]
    have ht0 : 0 < t := by linarith [ht.1]
    have hE := norm_zeta_sub_le N hN1 (s := s) (by rw [hsre]; linarith) (by rw [hsim]; linarith)
    rw [hsre] at hE
    -- first error term
    have h1 : (N : ℝ) ^ (1 - u) / ‖s - 1‖ ≤ 2 := by
      have hs1 : T ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        have him : (s - 1).im = -t := by simp [hs]
        rw [him, abs_neg, abs_of_pos ht0] at this
        linarith [ht.1]
      have hp1 : (N : ℝ) ^ (1 - u) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      have hp2 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 * T := by
        refine rpow_le_of_pow_le hN0.le (by linarith) (k := 4) (by norm_num) ?_
        rw [show (1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one, hTv]
        have : v ^ 4 ≤ v ^ 12 := pow_le_pow_right₀ hv1 (by norm_num)
        nlinarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    -- second error term
    have h2 : ‖s‖ * ((N : ℝ) ^ (-u) / u) ≤ 4 := by
      have hsn : ‖s‖ ≤ 3 * T := by
        refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
        rw [hsre, hsim, abs_neg, abs_of_pos ht0, abs_of_pos (by linarith)]
        linarith [ht.2]
      have hp1 : (N : ℝ) ^ (-u) ≤ (N : ℝ) ^ (-(3 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      have hp2 : (N : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / T := by
        have hpos : 0 < (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hN0 _
        have hge : T ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by
          have h3 : (T ^ (4 : ℕ)) ≤ ((N : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) := by
            rw [← Real.rpow_natCast ((N : ℝ) ^ _), ← Real.rpow_mul hN0.le]
            rw [show (3 : ℝ) / 4 * ((4 : ℕ) : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast, hTv]
            calc (v ^ 3) ^ 4 = (v ^ 4) ^ 3 := by ring
              _ ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hNlo 3
          exact (pow_le_pow_iff_left₀ hT0.le hpos.le (by norm_num)).1 h3
        rw [show -(3 : ℝ) / 4 = -((3 : ℝ) / 4) by ring, Real.rpow_neg hN0.le, one_div]
        exact inv_anti₀ hT0 hge
      have hu0 : 0 < u := by linarith
      have hiu : 1 / u ≤ 4 / 3 := by rw [div_le_iff₀ hu0]; linarith
      have hNu0 : 0 ≤ (N : ℝ) ^ (-u) := Real.rpow_nonneg hN0.le _
      calc ‖s‖ * ((N : ℝ) ^ (-u) / u) = ‖s‖ * (N : ℝ) ^ (-u) * (1 / u) := by ring
        _ ≤ (3 * T) * (1 / T) * (4 / 3) := by
          gcongr
          exact hp1.trans hp2
        _ = 4 := by field_simp
    have hE6 : ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 6 := by linarith
    have hP := norm_sum_cpow_eq N u t
    rw [← hs] at hP
    have htri : ‖riemannZeta s‖ ≤ ‖dpoly b N t‖ + 6 := by
      have := norm_le_norm_add_norm_sub' (riemannZeta s) (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      rw [hP] at this
      linarith
    have h0 := norm_nonneg (riemannZeta s)
    have h0' := norm_nonneg (dpoly b N t)
    have := pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖dpoly b N t‖ - 6)]
  -- the mean value theorem
  have hmv := mv_poly b N (2 * T)
  have hdiag : ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 ≤ S32 := by
    calc ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(3 / 2) : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [Finset.mem_Icc] at hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
          simp only [hb, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
      _ ≤ S32 := hsum32.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hoff : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 ≤ 2 * Real.sqrt N := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_inv_sqrt_le N)
    simp only [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hn0 : (0 : ℝ) < n := by linarith
    simp only [hb, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.sqrt_eq_rpow, one_div,
      ← Real.rpow_neg hn0.le]
    calc (n : ℝ) * (n : ℝ) ^ (-u * ((2 : ℕ) : ℝ)) = (n : ℝ) ^ (1 + -u * ((2 : ℕ) : ℝ)) := by
          rw [Real.rpow_add hn0, Real.rpow_one]
      _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
  have hHW : 6 * H N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 ≤ 216 * T := by
    have hH : H N ≤ 9 * (N : ℝ) ^ ((1 : ℝ) / 8) := by
      have h1 := H_le_one_add_log N
      have h2 := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 8 by norm_num)
      have h3 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hNR (by norm_num)
      have : (N : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * (N : ℝ) ^ ((1 : ℝ) / 8) := by ring
      linarith
    have hW : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hsq : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have h58 : (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 * T := by
      rw [← Real.rpow_add hN0]
      refine rpow_le_of_pow_le hN0.le (by linarith) (k := 8) (by norm_num) ?_
      rw [show ((1 : ℝ) / 8 + 1 / 2) * ((8 : ℕ) : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast, hTv]
      calc (N : ℝ) ^ 5 ≤ (2 * v ^ 4) ^ 5 := pow_le_pow_left₀ hN0.le hNhi 5
        _ = 32 * v ^ 20 := by ring
        _ ≤ 256 * v ^ 24 := by
          have : v ^ 20 ≤ v ^ 24 := pow_le_pow_right₀ hv1 (by norm_num)
          have h0 : 0 ≤ v ^ 24 := by positivity
          linarith
        _ = (2 * v ^ 3) ^ 8 := by ring
    have hH0 : 0 ≤ H N := RamanujanTau.MeanSquare.H_nonneg N
    calc 6 * H N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2
        ≤ 6 * (9 * (N : ℝ) ^ ((1 : ℝ) / 8)) * (2 * Real.sqrt N) := by gcongr
      _ = 108 * ((N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hsq]; ring
      _ ≤ 108 * (2 * T) := by gcongr
      _ = 216 * T := by ring
  have hP02 : ∫ t in (0 : ℝ)..2 * T, ‖dpoly b N t‖ ^ 2 ≤ 2 * T * S32 + 216 * T := by
    have h1 := (abs_le.1 hmv).2
    have h2 : 2 * T * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 ≤ 2 * T * S32 := by gcongr
    linarith
  have hPc : Continuous fun t => ‖dpoly b N t‖ ^ 2 := ((continuous_dpoly b N).norm.pow 2)
  have hPT : ∫ t in T..2 * T, ‖dpoly b N t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..2 * T, ‖dpoly b N t‖ ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := T) (c := 2 * T)
      (hPc.intervalIntegrable _ _) (hPc.intervalIntegrable _ _)]
    have : 0 ≤ ∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0.le fun _ _ => by positivity
    linarith
  -- continuity of `ζ` on the segment
  have hζc : ContinuousOn (fun t : ℝ => ‖riemannZeta ((u : ℂ) - t * I)‖ ^ 2) (uIcc T (2 * T)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hne : (u : ℂ) - t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [ht.1]
    exact ((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (u : ℂ) - t * I) (x := t)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).norm.pow 2).continuousWithinAt
  have hPc1 : Continuous fun t => 2 * ‖dpoly b N t‖ ^ 2 := continuous_const.mul hPc
  have hPc2 : Continuous fun t => 2 * ‖dpoly b N t‖ ^ 2 + 72 := hPc1.add continuous_const
  calc ∫ t in T..2 * T, ‖riemannZeta ((u : ℂ) - t * I)‖ ^ 2
      ≤ ∫ t in T..2 * T, (2 * ‖dpoly b N t‖ ^ 2 + 72) := by
        refine intervalIntegral.integral_mono_on (by linarith) (hζc.intervalIntegrable)
          (hPc2.intervalIntegrable _ _) happrox
    _ = 2 * (∫ t in T..2 * T, ‖dpoly b N t‖ ^ 2) + 72 * T := by
        have e1 := intervalIntegral.integral_add (μ := volume) (a := T) (b := 2 * T)
          (hPc1.intervalIntegrable _ _) (intervalIntegrable_const (c := (72 : ℝ)))
        have e2 := intervalIntegral.integral_const_mul (μ := volume) (a := T) (b := 2 * T) (2 : ℝ)
          (fun t => ‖dpoly b N t‖ ^ 2)
        rw [e1, e2, intervalIntegral.integral_const]
        simp only [smul_eq_mul]; ring
    _ ≤ 2 * (2 * T * S32 + 216 * T) + 72 * T := by linarith [hPT.trans hP02]
    _ = (4 * S32 + 504) * T := by ring

end RamanujanTau.RankinOmega
