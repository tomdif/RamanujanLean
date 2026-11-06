/-
# The `L²`-truncated Voronoi formula (weight `2m`): parameters and the limit

`voronoi_L2`: for `0 < θ ≤ 1/4`,

    X^{−(2m+1/2)} ∫_X^{2X} (S(x) − V_{⌊X^θ⌋}(x))² dx → 0,

with `h = X^{7/32}` (smoothing), `M = ⌊X^{5/8}⌋` (cut of the smoothed dual series) and `r = 12`
— the same parameters as for `τ`: every exponent is shifted by the same amount `m − 6`.
-/
import RamanujanTau.VoronoiTruncGeneral.Assembly

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology

variable {m : ℕ} {a : ℕ → ℝ}

lemma sq_bco (n : ℕ) : bco m a n ^ 2 = a n ^ 2 * (n : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) := by
  unfold bco
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-((m : ℝ) + 1 / 4))) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 2; push_cast; ring

lemma summable_bco_sq (hd : VData m a) : Summable fun n => bco m a n ^ 2 := by
  have := hd.summable_sq (β := 2 * (m : ℝ) + 1 / 2) (by linarith)
  refine this.congr fun n => ?_
  rw [sq_bco]

lemma cast_two_mul_sub_one (hm : 1 ≤ m) : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma wt_eq (hm : 1 ≤ m) (y : ℝ) (hy : 0 ≤ y) : (y ^ ((m : ℝ) - 1 / 4)) ^ 2 = wt (2 * m - 1) y := by
  unfold wt
  rw [← Real.rpow_natCast (y ^ ((m : ℝ) - 1 / 4)) 2, ← Real.rpow_mul hy, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast y (2 * m - 1), ← Real.rpow_add' hy (by
      rw [cast_two_mul_sub_one hm]; have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      exact ne_of_gt (by linarith)),
    cast_two_mul_sub_one hm]
  congr 1; push_cast; ring

lemma Vth_sub (N M : ℕ) (hNM : N ≤ M) (x : ℝ) :
    Vth m a M x - Vth m a N x = x ^ ((m : ℝ) - 1 / 4) / (π * √2) *
      ∑ n ∈ Finset.Ioc N M, bco m a n * Real.cos (th n x) := by
  unfold Vth
  rw [← mul_sub]
  congr 1
  rw [TauPartialSums.Icc_one_eq_Ioc, TauPartialSums.Icc_one_eq_Ioc,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNM]
  ring

lemma two_mul_sub_one_add_one (hm : 1 ≤ m) : 2 * m - 1 + 1 = 2 * m := by omega

/-- The mean-value bound for the block `N < n ≤ M`. -/
lemma mv_tail (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) {N M : ℕ} (hNM : N ≤ M) :
    ∫ x in X..3 * X, (Vth m a M x - Vth m a N x) ^ 2 ≤
      1 / (2 * π ^ 2) * ((1 / 2) * (∑ n ∈ Finset.Ioc N M, bco m a n ^ 2) * (∫ x in X..3 * X, wt (2 * m - 1) x) +
        (3 * X) ^ (2 * m) * √(M : ℝ) * (2 * Hs M + 1) * ∑ n ∈ Finset.Ioc N M, bco m a n ^ 2) := by
  have hF : ∀ n ∈ Finset.Ioc N M, 1 ≤ n ∧ n ≤ M := by
    intro n hn; obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn; exact ⟨by omega, h2⟩
  have hmv := mean_value (p := 2 * m - 1) (Finset.Ioc N M) hF (bco m a) (a := X) (b := 3 * X) hX (by linarith)
  rw [two_mul_sub_one_add_one hd.one_le] at hmv
  have e : ∀ x ∈ Set.uIcc X (3 * X), (Vth m a M x - Vth m a N x) ^ 2 =
      1 / (2 * π ^ 2) * (wt (2 * m - 1) x * (∑ n ∈ Finset.Ioc N M, bco m a n * Real.cos (th n x)) ^ 2) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [Vth_sub N M hNM, mul_pow, div_pow, wt_eq hd.one_le x hx0, mul_pow, Real.sq_sqrt (by norm_num)]
    field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul]
  gcongr
  have h2 := sub_le_iff_le_add'.1 (abs_le.1 hmv).2
  exact h2


/-! ### Bounds in terms of `X` -/

/-- Tail of `Σ bₙ²`. -/
noncomputable def tl (m : ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑' k : ℕ, bco m a (k + (N + 1)) ^ 2

lemma sum_Ioc_le_tl (hd : VData m a) (N M : ℕ) : ∑ n ∈ Finset.Ioc N M, bco m a n ^ 2 ≤ tl m a N := by
  have hs := (summable_nat_add_iff (N + 1)).2 (summable_bco_sq hd)
  unfold tl
  have e : ∑ n ∈ Finset.Ioc N M, bco m a n ^ 2 = ∑ k ∈ Finset.range (M - N), bco m a (k + (N + 1)) ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
    simp only [tsub_zero]
    rw [show Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    rw [show M + 1 - (N + 1) = M - N by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2; ring
  rw [e]
  exact hs.sum_le_tsum _ fun k _ => sq_nonneg _

lemma tendsto_tl : Tendsto (tl m a) atTop (𝓝 0) := by
  have := tendsto_sum_nat_add (f := fun n => bco m a n ^ 2)
  have h2 := this.comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun N => ?_
  simp only [Function.comp, tl]

lemma rpow_le_of_le {X u v : ℝ} (hX : 1 ≤ X) (huv : u ≤ v) : X ^ u ≤ X ^ v :=
  Real.rpow_le_rpow_of_exponent_le hX huv

lemma rpow_nat_eq {X : ℝ} (hX : 0 < X) (u : ℝ) (k : ℕ) : (X ^ u) ^ k = X ^ (u * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]

lemma floor_rpow_le {X u : ℝ} (hX : 0 < X) : ((⌊X ^ u⌋₊ : ℕ) : ℝ) ≤ X ^ u :=
  Nat.floor_le (Real.rpow_nonneg hX.le _)

lemma rpow_lt_floor_add_one {X u : ℝ} : X ^ u < ((⌊X ^ u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _

lemma pow_eq_rpow (X : ℝ) (k : ℕ) : X ^ k = X ^ (k : ℝ) := (Real.rpow_natCast X k).symm

/-- `B₂ ≤ A₂ X^{m−5/16}` with `h = X^{7/32}`, `M = ⌊X^{5/8}⌋`. -/
lemma B2_bound (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) :
    B2 m a X (X ^ (7 / 32 : ℝ)) ⌊X ^ (5 / 8 : ℝ)⌋₊ ≤
      (CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) +
        CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4)) * X ^ ((m : ℝ) - 5 / 16) := by
  have hX0 : 0 < X := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hd.one_le
  set M := ⌊X ^ (5 / 8 : ℝ)⌋₊
  have hCK := CK_nonneg m
  have hCT := CT_nonneg m
  have hS1 := St_nonneg (a := a) ((m : ℝ) + 5 / 8)
  have hS2 := St_nonneg (a := a) ((m : ℝ) + 3 / 4)
  unfold B2
  have hM1 : (M : ℝ) ^ (1 / 8 : ℝ) ≤ X ^ (5 / 64 : ℝ) := by
    calc (M : ℝ) ^ (1 / 8 : ℝ) ≤ (X ^ (5 / 8 : ℝ)) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (floor_rpow_le hX0) (by norm_num)
      _ = X ^ (5 / 64 : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num
  have t1 : CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * ((M : ℝ) ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 5 / 8)) ≤
      CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) * X ^ ((m : ℝ) - 5 / 16) := by
    rw [Real.mul_rpow (by norm_num) hX0.le]
    calc CK m * (3 ^ ((m : ℝ) - 1 / 2) * X ^ ((m : ℝ) - 1 / 2)) * ((M : ℝ) ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 5 / 8))
        ≤ CK m * (3 ^ ((m : ℝ) - 1 / 2) * X ^ ((m : ℝ) - 1 / 2)) * (X ^ (5 / 64 : ℝ) * St a ((m : ℝ) + 5 / 8)) := by
          gcongr
      _ = CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) * (X ^ ((m : ℝ) - 1 / 2) * X ^ (5 / 64 : ℝ)) := by
          ring
      _ ≤ CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) * X ^ ((m : ℝ) - 5 / 16) := by
          gcongr
          rw [← Real.rpow_add hX0]
          exact rpow_le_of_le hX (by linarith)
  have hh : ((X ^ (7 / 32 : ℝ)) ^ 12)⁻¹ = X ^ (-(21 / 8) : ℝ) := by
    rw [rpow_nat_eq hX0, Real.rpow_neg hX0.le]; norm_num
  have hM2 : ((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) ≤ X ^ (-(55 / 16) : ℝ) := by
    have hpos : 0 < X ^ (5 / 8 : ℝ) := by positivity
    calc ((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) ≤ (X ^ (5 / 8 : ℝ)) ^ (-(11 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hpos rpow_lt_floor_add_one.le (by norm_num)
      _ = X ^ (-(55 / 16) : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num
  have t2 : ((X ^ (7 / 32 : ℝ)) ^ 12)⁻¹ * (CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
      (((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4))) ≤
      CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4) * X ^ ((m : ℝ) - 5 / 16) := by
    rw [hh, mul_pow, pow_eq_rpow X (m + 6)]
    calc X ^ (-(21 / 8) : ℝ) * (CT m / π ^ 12 * (3 ^ (m + 6) * X ^ ((m + 6 : ℕ) : ℝ)) * X ^ (-(1 / 4) : ℝ) *
          (((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4)))
        ≤ X ^ (-(21 / 8) : ℝ) * (CT m / π ^ 12 * (3 ^ (m + 6) * X ^ ((m + 6 : ℕ) : ℝ)) * X ^ (-(1 / 4) : ℝ) *
          (X ^ (-(55 / 16) : ℝ) * St a ((m : ℝ) + 3 / 4))) := by gcongr
      _ = CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4) *
          (X ^ (-(21 / 8) : ℝ) * X ^ ((m + 6 : ℕ) : ℝ) * X ^ (-(1 / 4) : ℝ) * X ^ (-(55 / 16) : ℝ)) := by ring
      _ = CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4) * X ^ ((m : ℝ) - 5 / 16) := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 2; push_cast; ring
  calc _ ≤ CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) * X ^ ((m : ℝ) - 5 / 16) +
        CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4) * X ^ ((m : ℝ) - 5 / 16) := add_le_add t1 t2
    _ = _ := by ring

/-- `B₄ ≤ A₄ X^{m−9/32}` with `h = X^{7/32}`, `N = ⌊X^θ⌋`, `θ ≤ 1/4`. -/
lemma B4_bound {X θ : ℝ} (hX : 1 ≤ X) (hθ : θ ≤ 1 / 4) :
    B4 m a X (X ^ (7 / 32 : ℝ)) ⌊X ^ θ⌋₊ ≤
      1 / (π * √2) * (((m : ℝ) + 2 * π) * St a ((m : ℝ) + 3 / 4)) * 3 ^ ((m : ℝ) - 3 / 4) * 12 *
        X ^ ((m : ℝ) - 9 / 32) := by
  have hX0 : 0 < X := by linarith
  have hS := St_nonneg (a := a) ((m : ℝ) + 3 / 4)
  unfold B4
  have hN : ((⌊X ^ θ⌋₊ : ℕ) : ℝ) ≤ X ^ (1 / 4 : ℝ) :=
    (floor_rpow_le hX0).trans (rpow_le_of_le hX hθ)
  rw [Real.mul_rpow (by norm_num) hX0.le]
  calc 1 / (π * √2) * (((m : ℝ) + 2 * π) * (((⌊X ^ θ⌋₊ : ℕ) : ℝ) * St a ((m : ℝ) + 3 / 4))) *
        (3 ^ ((m : ℝ) - 3 / 4) * X ^ ((m : ℝ) - 3 / 4)) * (12 * X ^ (7 / 32 : ℝ))
      ≤ 1 / (π * √2) * (((m : ℝ) + 2 * π) * (X ^ (1 / 4 : ℝ) * St a ((m : ℝ) + 3 / 4))) *
        (3 ^ ((m : ℝ) - 3 / 4) * X ^ ((m : ℝ) - 3 / 4)) * (12 * X ^ (7 / 32 : ℝ)) := by gcongr
    _ = 1 / (π * √2) * (((m : ℝ) + 2 * π) * St a ((m : ℝ) + 3 / 4)) * 3 ^ ((m : ℝ) - 3 / 4) * 12 *
        (X ^ (1 / 4 : ℝ) * X ^ ((m : ℝ) - 3 / 4) * X ^ (7 / 32 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 2; ring

lemma T1_bound {X : ℝ} (hX : 1 ≤ X) {Bq : ℝ} (hBq0 : 0 ≤ Bq)
    (hBq : ∀ K : ℕ, ∑ n ∈ Finset.Icc 1 K, a n ^ 2 ≤ Bq * (K : ℝ) ^ (2 * m)) :
    (12 * X ^ (7 / 32 : ℝ) + 1) * (12 * X ^ (7 / 32 : ℝ)) *
      ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 ≤ 288 * Bq * 3 ^ (2 * m) * X ^ (2 * (m : ℝ) + 7 / 16) := by
  have hX0 : 0 < X := by linarith
  have hh1 : 1 ≤ X ^ (7 / 32 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hK : ((⌊3 * X⌋₊ : ℕ) : ℝ) ≤ 3 * X := Nat.floor_le (by linarith)
  have hS : ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 ≤ Bq * (3 * X) ^ (2 * m) :=
    (hBq _).trans (by gcongr)
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfac : (12 * X ^ (7 / 32 : ℝ) + 1) * (12 * X ^ (7 / 32 : ℝ)) ≤ 288 * X ^ (7 / 16 : ℝ) := by
    have : X ^ (7 / 16 : ℝ) = (X ^ (7 / 32 : ℝ)) ^ 2 := by rw [rpow_nat_eq hX0]; norm_num
    rw [this]; nlinarith
  calc (12 * X ^ (7 / 32 : ℝ) + 1) * (12 * X ^ (7 / 32 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2
      ≤ 288 * X ^ (7 / 16 : ℝ) * (Bq * (3 * X) ^ (2 * m)) := by gcongr
    _ = 288 * Bq * 3 ^ (2 * m) * (X ^ (7 / 16 : ℝ) * X ^ ((2 * m : ℕ) : ℝ)) := by
        rw [mul_pow, pow_eq_rpow X (2 * m)]; ring
    _ = _ := by rw [← Real.rpow_add hX0]; congr 2; push_cast; ring

lemma Hs_bound {X : ℝ} (hX : 1 ≤ X) {M : ℕ} (hM : (M : ℝ) ≤ X) :
    2 * Hs M + 1 ≤ 35 * X ^ (1 / 16 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have h1 : 1 ≤ X ^ (1 / 16 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hlog : Real.log X ≤ 16 * X ^ (1 / 16 : ℝ) := by
    have := Real.log_le_rpow_div hX0.le (ε := 1 / 16) (by norm_num)
    linarith [show X ^ (1 / 16 : ℝ) / (1 / 16) = 16 * X ^ (1 / 16 : ℝ) by ring]
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hH : Hs M ≤ 1 + Real.log X := by
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · simp [Hs]; linarith
    · refine (Hs_le_log M).trans ?_
      have : Real.log M ≤ Real.log X := Real.log_le_log (by exact_mod_cast hM0) hM
      linarith
  nlinarith

lemma integral_wt_le (hm : 1 ≤ m) {X : ℝ} (hX : 1 ≤ X) :
    ∫ x in X..3 * X, wt (2 * m - 1) x ≤ 2 * 3 ^ (2 * (m : ℝ) - 1 / 2) * X ^ (2 * (m : ℝ) + 1 / 2) := by
  have hX0 : 0 < X := by linarith
  have hb : ∀ x ∈ Set.Icc X (3 * X), wt (2 * m - 1) x ≤ wt (2 * m - 1) (3 * X) := by
    intro x hx
    unfold wt
    have hx0 : 0 ≤ x := by linarith [hx.1]
    gcongr
    · exact hx.2
    · exact hx.2
  have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : X ≤ 3 * X)
    ((continuous_wt _).intervalIntegrable _ _)
    ((continuous_const (y := wt (2 * m - 1) (3 * X))).intervalIntegrable _ _) hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  refine this.trans (le_of_eq ?_)
  rw [← wt_eq hm _ (by linarith), ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
    Real.mul_rpow (by norm_num) hX0.le]
  have e : (2 * (m : ℝ) + 1 / 2) = 1 + ((m : ℝ) - 1 / 4) * ((2 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_add hX0, Real.rpow_one]
  have e2 : ((m : ℝ) - 1 / 4) * ((2 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 / 2 := by push_cast; ring
  rw [e2]; ring

lemma mv_bound (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) {N : ℕ} (hNM : N ≤ ⌊X ^ (5 / 8 : ℝ)⌋₊) :
    ∫ x in X..3 * X, (Vth m a ⌊X ^ (5 / 8 : ℝ)⌋₊ x - Vth m a N x) ^ 2 ≤
      1 / (2 * π ^ 2) * (3 ^ (2 * (m : ℝ) - 1 / 2) + 35 * 3 ^ (2 * m)) * tl m a N *
        X ^ (2 * (m : ℝ) + 1 / 2) := by
  have hX0 : 0 < X := by linarith
  set M := ⌊X ^ (5 / 8 : ℝ)⌋₊
  have hM : (M : ℝ) ≤ X ^ (5 / 8 : ℝ) := floor_rpow_le hX0
  have hMX : (M : ℝ) ≤ X := hM.trans (by simpa using rpow_le_of_le hX (show (5 / 8 : ℝ) ≤ 1 by norm_num))
  refine (mv_tail hd hX hNM).trans ?_
  set T := ∑ n ∈ Finset.Ioc N M, bco m a n ^ 2
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hTl : T ≤ tl m a N := sum_Ioc_le_tl hd N M
  have hwt := integral_wt_le hd.one_le hX
  have hoff : (3 * X) ^ (2 * m) * √(M : ℝ) * (2 * Hs M + 1) ≤
      35 * 3 ^ (2 * m) * X ^ (2 * (m : ℝ) + 1 / 2) := by
    have hs : √(M : ℝ) ≤ X ^ (5 / 16 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (M : ℝ) ^ (1 / 2 : ℝ) ≤ (X ^ (5 / 8 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hM (by norm_num)
        _ = X ^ (5 / 16 : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num
    have hH := Hs_bound hX hMX
    have hH0 : 0 ≤ 2 * Hs M + 1 := by have := Hs_nonneg M; linarith
    calc (3 * X) ^ (2 * m) * √(M : ℝ) * (2 * Hs M + 1) ≤
          (3 * X) ^ (2 * m) * X ^ (5 / 16 : ℝ) * (35 * X ^ (1 / 16 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hH hH0 (by positivity)
      _ = 35 * 3 ^ (2 * m) * (X ^ ((2 * m : ℕ) : ℝ) * X ^ (5 / 16 : ℝ) * X ^ (1 / 16 : ℝ)) := by
          rw [mul_pow, pow_eq_rpow X (2 * m)]; ring
      _ = 35 * 3 ^ (2 * m) * X ^ (2 * (m : ℝ) + 3 / 8) := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 2; push_cast; ring
      _ ≤ 35 * 3 ^ (2 * m) * X ^ (2 * (m : ℝ) + 1 / 2) :=
          mul_le_mul_of_nonneg_left (rpow_le_of_le hX (by linarith)) (by positivity)
  have hp : 0 < 1 / (2 * π ^ 2) := by positivity
  calc 1 / (2 * π ^ 2) * ((1 / 2) * T * (∫ x in X..3 * X, wt (2 * m - 1) x) +
        (3 * X) ^ (2 * m) * √(M : ℝ) * (2 * Hs M + 1) * T)
      ≤ 1 / (2 * π ^ 2) * ((1 / 2) * T * (2 * 3 ^ (2 * (m : ℝ) - 1 / 2) * X ^ (2 * (m : ℝ) + 1 / 2)) +
          35 * 3 ^ (2 * m) * X ^ (2 * (m : ℝ) + 1 / 2) * T) := by gcongr
    _ = 1 / (2 * π ^ 2) * (3 ^ (2 * (m : ℝ) - 1 / 2) + 35 * 3 ^ (2 * m)) * T * X ^ (2 * (m : ℝ) + 1 / 2) := by
        ring
    _ ≤ _ := by gcongr


lemma tl_nonneg (N : ℕ) : 0 ≤ tl m a N := tsum_nonneg fun _ => sq_nonneg _

lemma B2_nonneg {X h : ℝ} (hX : 0 ≤ X) (hh : 0 ≤ h) (M : ℕ) : 0 ≤ B2 m a X h M := by
  unfold B2
  have := CK_nonneg m; have := CT_nonneg m
  have := St_nonneg (a := a) ((m : ℝ) + 5 / 8); have := St_nonneg (a := a) ((m : ℝ) + 3 / 4)
  positivity

lemma B4_nonneg {X h : ℝ} (hX : 0 ≤ X) (hh : 0 ≤ h) (N : ℕ) : 0 ≤ B4 m a X h N := by
  unfold B4; have := St_nonneg (a := a) ((m : ℝ) + 3 / 4); positivity

/-- **The dyadic `L²` bound with explicit decay.** -/
theorem voronoi_L2_bound (hd : VData m a) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 144 ≤ X →
      ∫ x in Ioc X (2 * X), (Sre a x - Vth m a ⌊X ^ θ⌋₊ x) ^ 2 ≤
        C * X ^ (2 * (m : ℝ) + 1 / 2) * (X ^ (-(1 / 16) : ℝ) + tl m a ⌊X ^ θ⌋₊) := by
  obtain ⟨Bq, hBq0, hBq⟩ := hd.rankin
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hd.one_le
  set C1 := 288 * Bq * 3 ^ (2 * m)
  set A2 := CK m * 3 ^ ((m : ℝ) - 1 / 2) * St a ((m : ℝ) + 5 / 8) +
    CT m / π ^ 12 * 3 ^ (m + 6) * St a ((m : ℝ) + 3 / 4)
  set A4 := 1 / (π * √2) * (((m : ℝ) + 2 * π) * St a ((m : ℝ) + 3 / 4)) * 3 ^ ((m : ℝ) - 3 / 4) * 12
  set A3 := 1 / (2 * π ^ 2) * (3 ^ (2 * (m : ℝ) - 1 / 2) + 35 * 3 ^ (2 * m))
  have hC1 : 0 ≤ C1 := by positivity
  have hA3 : 0 ≤ A3 := by positivity
  refine ⟨4 * (C1 + A2 ^ 2 + A4 ^ 2 + A3), by positivity, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  set h := X ^ (7 / 32 : ℝ) with hhdef
  have hh : 0 < h := by positivity
  have h12 : 12 * h ≤ X := by
    have hs : 12 ≤ X ^ (25 / 32 : ℝ) := by
      have : (12 : ℝ) = (144 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (144 : ℝ) = 12 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]
      calc (144 : ℝ) ^ (1 / 2 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
        _ ≤ X ^ (25 / 32 : ℝ) := rpow_le_of_le hX1 (by norm_num)
    calc 12 * h ≤ X ^ (25 / 32 : ℝ) * X ^ (7 / 32 : ℝ) := by
          rw [hhdef]; exact mul_le_mul_of_nonneg_right hs (by positivity)
      _ = X := by rw [← Real.rpow_add hX0]; norm_num
  set N := ⌊X ^ θ⌋₊
  set M := ⌊X ^ (5 / 8 : ℝ)⌋₊
  have hNM : N ≤ M := Nat.floor_le_floor (rpow_le_of_le hX1 (by linarith))
  have hmain := L2_main hd (N := N) (M := M) hX1 hh h12
  have hT1 := T1_bound hX1 hBq0 hBq
  have hB2 := B2_bound hd hX1
  have hB4 := B4_bound (a := a) (m := m) (θ := θ) hX1 hθ
  have hmv := mv_bound hd hX1 hNM
  have hB2' : X * B2 m a X h M ^ 2 ≤ A2 ^ 2 * X ^ (2 * (m : ℝ) + 7 / 16) := by
    have h0 := B2_nonneg (a := a) (m := m) hX0.le hh.le M
    have : B2 m a X h M ^ 2 ≤ (A2 * X ^ ((m : ℝ) - 5 / 16)) ^ 2 := pow_le_pow_left₀ h0 hB2 2
    calc X * B2 m a X h M ^ 2 ≤ X * (A2 * X ^ ((m : ℝ) - 5 / 16)) ^ 2 := by gcongr
      _ = A2 ^ 2 * (X ^ (1 : ℝ) * (X ^ ((m : ℝ) - 5 / 16)) ^ 2) := by rw [Real.rpow_one]; ring
      _ = A2 ^ 2 * X ^ (2 * (m : ℝ) + 3 / 8) := by
          rw [rpow_nat_eq hX0, ← Real.rpow_add hX0]; congr 2; push_cast; ring
      _ ≤ A2 ^ 2 * X ^ (2 * (m : ℝ) + 7 / 16) :=
          mul_le_mul_of_nonneg_left (rpow_le_of_le hX1 (by linarith)) (sq_nonneg _)
  have hB4' : X * B4 m a X h N ^ 2 ≤ A4 ^ 2 * X ^ (2 * (m : ℝ) + 7 / 16) := by
    have h0 := B4_nonneg (a := a) (m := m) hX0.le hh.le N
    have : B4 m a X h N ^ 2 ≤ (A4 * X ^ ((m : ℝ) - 9 / 32)) ^ 2 := pow_le_pow_left₀ h0 hB4 2
    calc X * B4 m a X h N ^ 2 ≤ X * (A4 * X ^ ((m : ℝ) - 9 / 32)) ^ 2 := by gcongr
      _ = A4 ^ 2 * (X ^ (1 : ℝ) * (X ^ ((m : ℝ) - 9 / 32)) ^ 2) := by rw [Real.rpow_one]; ring
      _ = A4 ^ 2 * X ^ (2 * (m : ℝ) + 7 / 16) := by
          rw [rpow_nat_eq hX0, ← Real.rpow_add hX0]; congr 2; push_cast; ring
  have hsplit : X ^ (2 * (m : ℝ) + 7 / 16) = X ^ (2 * (m : ℝ) + 1 / 2) * X ^ (-(1 / 16) : ℝ) := by
    rw [← Real.rpow_add hX0]; congr 1; ring
  have htl := tl_nonneg (m := m) (a := a) N
  have hXn : 0 ≤ X ^ (-(1 / 16) : ℝ) := by positivity
  have hX25 : 0 ≤ X ^ (2 * (m : ℝ) + 1 / 2) := by positivity
  refine hmain.trans ?_
  rw [hsplit] at hT1 hB2' hB4'
  have hA2 : 0 ≤ A2 ^ 2 := sq_nonneg _
  have hA4 : 0 ≤ A4 ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hC1 hX25) hXn, mul_nonneg (mul_nonneg hA2 hX25) hXn,
    mul_nonneg (mul_nonneg hA4 hX25) hXn, mul_nonneg (mul_nonneg hA3 hX25) htl,
    mul_nonneg (mul_nonneg hC1 hX25) htl, mul_nonneg (mul_nonneg hA2 hX25) htl,
    mul_nonneg (mul_nonneg hA4 hX25) htl, mul_nonneg (mul_nonneg hA3 hX25) hXn]

/-- **The `L²`-truncated Voronoi formula** (internal form). -/
theorem voronoi_L2 (hd : VData m a) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X => (∫ x in X..2 * X, (Sre a x - Vth m a ⌊X ^ θ⌋₊ x) ^ 2) / X ^ (2 * (m : ℝ) + 1 / 2))
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := voronoi_L2_bound hd hθ0 hθ
  have hg : Tendsto (fun X : ℝ => C * (X ^ (-(1 / 16) : ℝ) + tl m a ⌊X ^ θ⌋₊)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => X ^ (-(1 / 16) : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h2 : Tendsto (fun X : ℝ => tl m a ⌊X ^ θ⌋₊) atTop (𝓝 0) :=
      tendsto_tl.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ0))
    simpa using (h1.add h2).const_mul C
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop 0] with X hX
    apply div_nonneg _ (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  · filter_upwards [eventually_ge_atTop 144] with X hX
    have hX0 : 0 < X := by linarith
    rw [intervalIntegral.integral_of_le (by linarith), div_le_iff₀ (by positivity)]
    have := hC X hX
    linarith [this]

end RamanujanTau.VoronoiTruncGeneral
