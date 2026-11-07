/-
# Exact `Ω±(x^{23/4})` in every dyadic interval

`tau_omega_plus_dyadic`: for every `c < 1/(2π√2)` and all large `X` there is `x ∈ [X, 2X]` with
`S(x) > c x^{23/4}`; `tau_omega_minus_dyadic`: likewise `S(x) < −c x^{23/4}`.

Proof (Ingham's positive-kernel trick on the first Voronoi coefficient `b₁ = τ(1) = 1`): integrate
`S(x) x^{−23/4} (1 ± cos θ₁(x)) ≥ 0`-weighted over `[X, 2X]`.  The Voronoi main term contributes
`± X/(2π√2) + O(X^{5/8})` (all other frequencies are killed by one integration by parts), and the
remainder `D = S − V_N` contributes `≤ ηX + X·d(X)/η` with `d(X) = X^{−25/2}∫D² → 0`
(`voronoi_L2`).  A one-sided bound `S ≤ c x^{23/4}` on `[X,2X]` would give `≤ c(X + O(√X))`.
-/
import RamanujanTau.VoronoiTruncGeneral.Cramer

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology

variable {m : ℕ} {a : ℕ → ℝ}

/-- One integration by parts with weight `1`. -/
lemma abs_integral_cos_le {δ φ a b : ℝ} (hδ : δ ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    |∫ y in a..b, Real.cos (4 * π * δ * √y + φ)| ≤ √b / (π * |δ|) := by
  have hδπ : 2 * π * δ ≠ 0 := mul_ne_zero (by positivity) hδ
  set F : ℝ → ℝ := fun y => √y * Real.sin (4 * π * δ * √y + φ) / (2 * π * δ) with hF
  set g : ℝ → ℝ := fun y => Real.sin (4 * π * δ * √y + φ) / (4 * π * δ * √y) with hg
  have hd : ∀ y ∈ Set.uIcc a b, HasDerivAt F (g y + Real.cos (4 * π * δ * √y + φ)) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hs : HasDerivAt (fun y => √y) (1 / (2 * √y)) y := by
      have := Real.hasDerivAt_sqrt hy0.ne'; simpa using this
    have h1 : HasDerivAt (fun y => 4 * π * δ * √y + φ) (4 * π * δ * (1 / (2 * √y))) y :=
      (hs.const_mul (4 * π * δ)).add_const φ
    have h2 := (hs.mul h1.sin).div_const (2 * π * δ)
    convert h2 using 1
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    simp only [hg]
    field_simp
    ring
  have hgc : ContinuousOn g (Set.uIcc a b) := by
    rw [uIcc_of_le hab]
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hg]
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    exact mul_ne_zero (mul_ne_zero (by positivity) hδ) hsy.ne'
  have hcc : Continuous fun y => Real.cos (4 * π * δ * √y + φ) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hgc.intervalIntegrable).add (hcc.intervalIntegrable _ _))
  rw [intervalIntegral.integral_add hgc.intervalIntegrable (hcc.intervalIntegrable _ _)] at hint
  have e : ∫ y in a..b, Real.cos (4 * π * δ * √y + φ) = F b - F a - ∫ y in a..b, g y := by linarith
  rw [e]
  have h2pd : |2 * π * δ| = 2 * π * |δ| := by rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hFb : |F b| ≤ √b / (2 * π * |δ|) := by
    simp only [hF]
    rw [abs_div, h2pd, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    calc √b * |Real.sin (4 * π * δ * √b + φ)| ≤ √b * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = √b := mul_one _
  have hFa : |F a| ≤ √a / (2 * π * |δ|) := by
    simp only [hF]
    rw [abs_div, h2pd, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    calc √a * |Real.sin (4 * π * δ * √a + φ)| ≤ √a * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = √a := mul_one _
  have hG : |∫ y in a..b, g y| ≤ (√b - √a) / (2 * π * |δ|) := by
    have hb : ∀ y ∈ Set.Icc a b, |g y| ≤ 1 / (4 * π * |δ| * √y) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      have hsy : 0 < √y := Real.sqrt_pos.2 hy0
      simp only [hg]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π), abs_of_pos hsy]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    have h1 := intervalIntegral.abs_integral_le_integral_abs (f := g) (μ := volume) hab
    have hgc' : ContinuousOn (fun y => |g y|) (Set.uIcc a b) := hgc.abs
    have hbc : ContinuousOn (fun y => 1 / (4 * π * |δ| * √y)) (Set.uIcc a b) := by
      rw [uIcc_of_le hab]
      intro y hy
      have hsy : 0 < √y := Real.sqrt_pos.2 (lt_of_lt_of_le ha hy.1)
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const (by fun_prop) ?_)
      have : 0 < |δ| := abs_pos.2 hδ
      positivity
    have h2 := intervalIntegral.integral_mono_on (μ := volume) hab hgc'.intervalIntegrable
      hbc.intervalIntegrable hb
    have h3 : ∫ y in a..b, 1 / (4 * π * |δ| * √y) = (√b - √a) / (2 * π * |δ|) := by
      have hd2 : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y => √y / (2 * π * |δ|)) (1 / (4 * π * |δ| * √y)) y := by
        intro y hy
        rw [uIcc_of_le hab] at hy
        have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
        have := (Real.hasDerivAt_sqrt hy0.ne').div_const (2 * π * |δ|)
        convert this using 1
        have : 0 < |δ| := abs_pos.2 hδ
        have hsy : 0 < √y := Real.sqrt_pos.2 hy0
        field_simp; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hbc.intervalIntegrable]
      ring
    linarith
  have hab' : √a ≤ √b := Real.sqrt_le_sqrt hab
  have hδ0 : 0 < |δ| := abs_pos.2 hδ
  calc |F b - F a - ∫ y in a..b, g y| ≤ |F b| + |F a| + |∫ y in a..b, g y| := by
        have := abs_sub (F b - F a) (∫ y in a..b, g y)
        have := abs_sub (F b) (F a)
        linarith
    _ ≤ √b / (2 * π * |δ|) + √a / (2 * π * |δ|) + (√b - √a) / (2 * π * |δ|) := by linarith
    _ = √b / (π * |δ|) := by field_simp; ring


lemma th_one (x : ℝ) : th 1 x = 4 * π * 1 * √x - π / 4 := by unfold th; simp

/-- The positive kernel `ρ_s(x) = 1 + s cos θ₁(x)`. -/
noncomputable def rho (s x : ℝ) : ℝ := 1 + s * Real.cos (th 1 x)

lemma rho_nonneg {s : ℝ} (hs : s = 1 ∨ s = -1) (x : ℝ) : 0 ≤ rho s x := by
  unfold rho
  rcases hs with rfl | rfl
  · linarith [Real.neg_one_le_cos (th 1 x)]
  · linarith [Real.cos_le_one (th 1 x)]

lemma rho_le_two {s : ℝ} (hs : s = 1 ∨ s = -1) (x : ℝ) : rho s x ≤ 2 := by
  unfold rho
  rcases hs with rfl | rfl
  · linarith [Real.cos_le_one (th 1 x)]
  · linarith [Real.neg_one_le_cos (th 1 x)]

lemma continuous_rho (s : ℝ) : Continuous (rho s) := by
  unfold rho; exact continuous_const.add (continuous_const.mul (Real.continuous_cos.comp (continuous_th 1)))

/-- `∫_X^{2X} cos θₙ · ρ_s = s [n=1] X/2 + O(√X)`. -/
lemma term_int {n : ℕ} (hn : 1 ≤ n) {X : ℝ} (hX : 0 < X) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    |(∫ x in X..2 * X, Real.cos (th n x) * rho s x) - (if n = 1 then s * X / 2 else 0)| ≤
      3 * √(2 * X) / π := by
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hsn : 1 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]; simpa using (Nat.one_le_cast.2 hn)
  have hXX : X ≤ 2 * X := by linarith
  have e : ∀ x, Real.cos (th n x) * rho s x = Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) +
      s / 2 * Real.cos (4 * π * (√(n : ℝ) - 1) * √x + 0) +
      s / 2 * Real.cos (4 * π * (√(n : ℝ) + 1) * √x + (-(π / 2))) := by
    intro x
    unfold rho
    rw [th_one, mul_add, mul_one, mul_left_comm, cos_mul_cos']
    unfold th; ring_nf
  have c1 : Continuous fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) := by fun_prop
  have c2 : Continuous fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) - 1) * √x + 0) := by fun_prop
  have c3 : Continuous fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) + 1) * √x + (-(π / 2))) := by fun_prop
  simp_rw [e]
  rw [intervalIntegral.integral_add
      (f := fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) +
        s / 2 * Real.cos (4 * π * (√(n : ℝ) - 1) * √x + 0))
      (g := fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) + 1) * √x + (-(π / 2))))
      ((c1.add c2).intervalIntegrable _ _) (c3.intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))))
      (g := fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) - 1) * √x + 0))
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  set A := ∫ x in X..2 * X, Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4)))
  set Bm := ∫ x in X..2 * X, Real.cos (4 * π * (√(n : ℝ) - 1) * √x + 0)
  set Bp := ∫ x in X..2 * X, Real.cos (4 * π * (√(n : ℝ) + 1) * √x + (-(π / 2)))
  set Q := √(2 * X) / π
  have hQ : 0 ≤ Q := by positivity
  have iA : |A| ≤ Q := by
    have i1 := abs_integral_cos_le (δ := √(n : ℝ)) (φ := -(π / 4)) (by positivity) hX hXX
    rw [abs_of_pos (by positivity : (0 : ℝ) < √(n : ℝ))] at i1
    refine i1.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith [Real.pi_pos]
  have iBp : |Bp| ≤ Q / 2 := by
    have i3 := abs_integral_cos_le (δ := √(n : ℝ) + 1) (φ := -(π / 2)) (by positivity) hX hXX
    rw [abs_of_pos (by positivity : (0 : ℝ) < √(n : ℝ) + 1)] at i3
    refine i3.trans ?_
    rw [show Q / 2 = √(2 * X) / (2 * π) by simp only [Q]; ring]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith [Real.pi_pos]
  have hsA : |s / 2 * Bp| ≤ Q / 4 := by
    rw [abs_mul, abs_div, hs1, abs_two]; linarith
  by_cases h1 : n = 1
  · subst h1
    rw [if_pos rfl]
    have hBm : Bm = X := by
      simp only [Bm, Nat.cast_one, Real.sqrt_one, sub_self, mul_zero, zero_mul, zero_add,
        Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
      ring
    rw [hBm]
    have e2 : A + s / 2 * X + s / 2 * Bp - s * X / 2 = A + s / 2 * Bp := by ring
    rw [e2]
    calc |A + s / 2 * Bp| ≤ |A| + |s / 2 * Bp| := abs_add_le _ _
      _ ≤ Q + Q / 4 := add_le_add iA hsA
      _ ≤ 3 * √(2 * X) / π := by simp only [Q]; rw [mul_div_assoc]; linarith
  · rw [if_neg h1, sub_zero]
    have hn2 : 2 ≤ n := by omega
    have hsn2 : √2 ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn2)
    have hs2 : (7 / 5 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hδ : 2 / 5 ≤ √(n : ℝ) - 1 := by linarith
    have iBm : |Bm| ≤ 5 / 2 * Q := by
      have i2 := abs_integral_cos_le (δ := √(n : ℝ) - 1) (φ := 0) (by linarith) hX hXX
      rw [abs_of_pos (by linarith : (0 : ℝ) < √(n : ℝ) - 1)] at i2
      refine i2.trans ?_
      have : √(2 * X) / (π * (√(n : ℝ) - 1)) = Q * (1 / (√(n : ℝ) - 1)) := by
        simp only [Q]; field_simp
      rw [this, mul_comm (5 / 2 : ℝ)]
      apply mul_le_mul_of_nonneg_left _ hQ
      rw [div_le_iff₀ (by linarith)]; linarith
    have hsB : |s / 2 * Bm| ≤ 5 / 4 * Q := by
      rw [abs_mul, abs_div, hs1, abs_two]; linarith
    calc |A + s / 2 * Bm + s / 2 * Bp| ≤ |A| + |s / 2 * Bm| + |s / 2 * Bp| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Q + 5 / 4 * Q + Q / 4 := add_le_add (add_le_add iA hsB) hsA
      _ ≤ 3 * √(2 * X) / π := by simp only [Q]; rw [mul_div_assoc]; linarith


lemma bco_one (h1 : a 1 = 1) : bco m a 1 = 1 := by simp [bco, h1]

/-- The main-term integral against the kernel. -/
lemma main_int (h1 : a 1 = 1) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : 1 ≤ N) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    |(∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho s x) - s * X / 2| ≤
      (∑ n ∈ Finset.Icc 1 N, |bco m a n|) * (3 * √(2 * X) / π) := by
  have hX0 : 0 < X := by linarith
  have hc : ∀ n : ℕ, Continuous fun x => bco m a n * Real.cos (th n x) * rho s x := fun n =>
    (continuous_const.mul (Real.continuous_cos.comp (continuous_th n))).mul (continuous_rho s)
  have e1 : ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho s x =
      ∑ n ∈ Finset.Icc 1 N, bco m a n * ∫ x in X..2 * X, Real.cos (th n x) * rho s x := by
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum (f := fun n x => bco m a n * Real.cos (th n x) * rho s x)
      (fun n _ => (hc n).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show bco m a n * Real.cos (th n x) * rho s x = bco m a n * (Real.cos (th n x) * rho s x)
    ring
  have e2 : s * X / 2 = ∑ n ∈ Finset.Icc 1 N, bco m a n * (if n = 1 then s * X / 2 else 0) := by
    rw [Finset.sum_eq_single 1 (fun n _ hn => by rw [if_neg hn, mul_zero])
      (fun h => absurd (Finset.mem_Icc.2 ⟨le_rfl, hN⟩) h), if_pos rfl, bco_one h1, one_mul]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (term_int (Finset.mem_Icc.1 hn).1 hX0 hs) (abs_nonneg _)

lemma Vth_mul_rpow (N : ℕ) {x : ℝ} (hx : 0 < x) :
    Vth m a N x * x ^ (-((m : ℝ) - 1 / 4)) = 1 / (π * √2) * ∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x) := by
  unfold Vth
  have : x ^ ((m : ℝ) - 1 / 4) * x ^ (-((m : ℝ) - 1 / 4)) = 1 := by
    rw [← Real.rpow_add hx]; simp
  calc x ^ ((m : ℝ) - 1 / 4) / (π * √2) * (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * x ^ (-((m : ℝ) - 1 / 4))
      = (x ^ ((m : ℝ) - 1 / 4) * x ^ (-((m : ℝ) - 1 / 4))) / (π * √2) *
          ∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x) := by ring
    _ = _ := by rw [this]


lemma sum_abs_bco_le (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Icc 1 ⌊X ^ (1 / 4 : ℝ)⌋₊, |bco m a n| ≤ X ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 3 / 4) := by
  have hX0 : 0 < X := by linarith
  have h := head_sum_le hd (β := (m : ℝ) + 3 / 4) (γ := (m : ℝ) + 1 / 4) (by linarith) (by linarith) ⌊X ^ (1 / 4 : ℝ)⌋₊
  have e : ∑ n ∈ Finset.Icc 1 ⌊X ^ (1 / 4 : ℝ)⌋₊, |bco m a n| =
      ∑ n ∈ Finset.Icc 1 ⌊X ^ (1 / 4 : ℝ)⌋₊, |a n| * (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    unfold bco
    have : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos this _)]
  rw [e]
  refine h.trans ?_
  gcongr
  · exact St_nonneg _
  · rw [show (m : ℝ) + 3 / 4 - ((m : ℝ) + 1 / 4) = 1 / 2 by ring]
    calc (((⌊X ^ (1 / 4 : ℝ)⌋₊ : ℕ) : ℝ)) ^ (1 / 2 : ℝ) ≤ (X ^ (1 / 4 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (floor_rpow_le hX0) (by norm_num)
      _ = X ^ (1 / 8 : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num

set_option maxHeartbeats 1000000 in
/-- **Core of the `Ω±` argument.** -/
theorem omega_core (hd : VData m a) (ha1 : a 1 = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop, ∃ x ∈ Icc X (2 * X), c * x ^ ((m : ℝ) - 1 / 4) < s * Sre a x := by
  set g := 1 / (2 * π * √2) - c with hg
  have hg0 : 0 < g := by linarith
  set η := g / 4 with hη
  have hη0 : 0 < η := by positivity
  set St7 := St a ((m : ℝ) + 3 / 4)
  have hSt7 : 0 ≤ St7 := St_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hd.one_le
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  -- the eventual smallness conditions
  have hdd := tendsto_d hd
  have ev1 := (tendsto_order.1 hdd).2 (g * η / 4) (by positivity)
  have hr1 : Tendsto (fun X : ℝ => 3 * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 8)).const_mul (3 * St7 / π ^ 2)
  have ev2 := (tendsto_order.1 hr1).2 (g / 4) (by positivity)
  have hr2 : Tendsto (fun X : ℝ => c * √2 / π * X ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (c * √2 / π)
  have ev3 := (tendsto_order.1 hr2).2 (g / 4) (by positivity)
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 1] with X h1 h2 h3 hX
  by_contra hcon
  push Not at hcon
  have hX0 : 0 < X := by linarith
  set N := ⌊X ^ (1 / 4 : ℝ)⌋₊
  have hN : 1 ≤ N := by
    rw [Nat.one_le_floor_iff]; exact Real.one_le_rpow hX (by norm_num)
  set w : ℝ → ℝ := fun x => x ^ (-((m : ℝ) - 1 / 4)) with hw
  have hwm : Measurable w := measurable_id.pow_const _
  have hwle : ∀ x, X ≤ x → w x ≤ 1 := fun x hx =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hw0 : ∀ x, X ≤ x → 0 ≤ w x := fun x hx => Real.rpow_nonneg (by linarith) _
  have hwx : ∀ x, X ≤ x → x ^ ((m : ℝ) - 1 / 4) * w x = 1 := fun x hx => by
    show x ^ ((m : ℝ) - 1 / 4) * x ^ (-((m : ℝ) - 1 / 4)) = 1
    rw [← Real.rpow_add (by linarith)]; simp
  have hρm : Measurable (rho s) := (continuous_rho s).measurable
  have hρ0 := rho_nonneg hs
  have hρ2 := rho_le_two hs
  -- integrability
  set K := ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊, |a n|
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set fS : ℝ → ℝ := fun x => s * Sre a x * w x * rho s x
  set fV : ℝ → ℝ := fun x => s * Vth m a N x * w x * rho s x
  have hfS : IntegrableOn fS (Ioc X (2 * X)) := by
    refine integrableOn_bounded_meas (((measurable_const.mul measurable_Sre).mul hwm).mul hρm)
      (K := K * 2) fun x hx => ?_
    show |s * Sre a x * w x * rho s x| ≤ K * 2
    rw [abs_mul, abs_mul, abs_mul, hs1, one_mul, abs_of_nonneg (hw0 x hx.1.le),
      abs_of_nonneg (hρ0 x)]
    have h1 := abs_Sre_le (a := a) hx.2
    have h2 := hwle x hx.1.le
    have h3 := hρ2 x
    have : |Sre a x| * w x ≤ K * 1 := mul_le_mul h1 h2 (hw0 x hx.1.le) hK0
    nlinarith [abs_nonneg (Sre a x), hρ0 x, hw0 x hx.1.le]
  have hwc : ContinuousOn w (Icc X (2 * X)) :=
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by simp; linarith [hx.1]))
  have hfVc : ContinuousOn fV (Icc X (2 * X)) :=
    ((continuousOn_const.mul (continuous_Vth hd.one_le N).continuousOn).mul hwc).mul (continuous_rho s).continuousOn
  have hfV : IntegrableOn fV (Ioc X (2 * X)) :=
    (hfVc.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  -- upper bound from the one-sided hypothesis
  have hcos1 : |∫ x in X..2 * X, Real.cos (th 1 x)| ≤ √(2 * X) / π := by
    have := abs_integral_cos_le (δ := 1) (φ := -(π / 4)) one_ne_zero hX0 (by linarith : X ≤ 2 * X)
    simp only [abs_one, mul_one] at this
    have e : ∀ x, th 1 x = 4 * π * √x + -(π / 4) := by intro x; unfold th; simp; ring
    simp_rw [e]; exact this
  have hρint : ∫ x in Ioc X (2 * X), rho s x ≤ X + √(2 * X) / π := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    unfold rho
    rw [intervalIntegral.integral_add (f := fun _ => (1 : ℝ)) (g := fun x => s * Real.cos (th 1 x))
      intervalIntegrable_const
      ((continuous_const.mul (Real.continuous_cos.comp (continuous_th 1))).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, mul_one]
    have : s * ∫ x in X..2 * X, Real.cos (th 1 x) ≤ √(2 * X) / π := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, hs1, one_mul]; exact hcos1
    linarith
  have hupper : ∫ x in Ioc X (2 * X), fS x ≤ c * (X + √(2 * X) / π) := by
    have hcρ : IntegrableOn (fun x => c * rho s x) (Ioc X (2 * X)) :=
      (((continuous_rho s).const_mul c).continuousOn.integrableOn_Icc (μ := volume)).mono_set
        Ioc_subset_Icc_self
    calc ∫ x in Ioc X (2 * X), fS x ≤ ∫ x in Ioc X (2 * X), c * rho s x := by
          refine setIntegral_mono_on hfS hcρ measurableSet_Ioc fun x hx => ?_
          have h := hcon x ⟨hx.1.le, hx.2⟩
          simp only [fS]
          have hwr : 0 ≤ w x * rho s x := mul_nonneg (hw0 x hx.1.le) (hρ0 x)
          calc s * Sre a x * w x * rho s x = (s * Sre a x) * (w x * rho s x) := by ring
            _ ≤ (c * x ^ ((m : ℝ) - 1 / 4)) * (w x * rho s x) := mul_le_mul_of_nonneg_right h hwr
            _ = c * rho s x * (x ^ ((m : ℝ) - 1 / 4) * w x) := by ring
            _ = c * rho s x := by rw [hwx x hx.1.le, mul_one]
      _ = c * ∫ x in Ioc X (2 * X), rho s x := integral_const_mul _ _
      _ ≤ c * (X + √(2 * X) / π) := mul_le_mul_of_nonneg_left hρint hc0
  -- the main-term part
  set E := (∑ n ∈ Finset.Icc 1 N, |bco m a n|) * (3 * √(2 * X) / π)
  have hE := main_int (m := m) ha1 hX N hN hs
  have hVint : ∫ x in Ioc X (2 * X), fV x = s * (1 / (π * √2)) *
      ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho s x := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [fV]
    have := Vth_mul_rpow (m := m) (a := a) N (show 0 < x by linarith [hx.1])
    calc s * Vth m a N x * w x * rho s x = s * (Vth m a N x * x ^ (-((m : ℝ) - 1 / 4))) * rho s x := by
          simp only [hw]; ring
      _ = _ := by rw [this]; ring
  have hVlow : (1 / (π * √2)) * (X / 2 - E) ≤ ∫ x in Ioc X (2 * X), fV x := by
    rw [hVint]
    set J := ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho s x
    have h1 : s * J ≥ X / 2 - E := by
      have : |s * J - X / 2| ≤ E := by
        have e : s * J - X / 2 = s * (J - s * X / 2) := by
          have : s * (J - s * X / 2) = s * J - (s * s) * X / 2 := by ring
          rw [this, hss]; ring
        rw [e, abs_mul, hs1, one_mul]; exact hE
      linarith [(abs_le.1 this).1]
    have hp : 0 < 1 / (π * √2) := by positivity
    calc 1 / (π * √2) * (X / 2 - E) ≤ 1 / (π * √2) * (s * J) := mul_le_mul_of_nonneg_left h1 hp.le
      _ = s * (1 / (π * √2)) * J := by ring
  -- the remainder part
  set dX := (∫ x in Ioc X (2 * X), (Sre a x - Vth m a N x) ^ 2) / X ^ (2 * (m : ℝ) + 1 / 2)
  have hD : |∫ x in Ioc X (2 * X), (fS x - fV x)| ≤ η * X + X * dX / η := by
    have hDi := integrableOn_D_sq (a := a) hd.one_le N X (2 * X)
    have hbd : ∀ x ∈ Ioc X (2 * X), |fS x - fV x| ≤
        η + (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) / η := by
      intro x hx
      have hxX : X ≤ x := hx.1.le
      have e : fS x - fV x = s * (Sre a x - Vth m a N x) * w x * rho s x := by simp only [fS, fV]; ring
      rw [e, abs_mul, abs_mul, abs_mul, hs1, one_mul, abs_of_nonneg (hw0 x hxX), abs_of_nonneg (hρ0 x)]
      set aa := |Sre a x - Vth m a N x| * w x
      have ha : 0 ≤ aa := mul_nonneg (abs_nonneg _) (hw0 x hxX)
      have hw2 : w x ^ 2 ≤ X ^ (-(2 * (m : ℝ) - 1 / 2)) := by
        simp only [hw]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
          show -((m : ℝ) - 1 / 4) * ((2 : ℕ) : ℝ) = -(2 * (m : ℝ) - 1 / 2) by push_cast; ring]
        exact Real.rpow_le_rpow_of_nonpos hX0 hxX (by linarith)
      have ha2 : aa ^ 2 ≤ (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) := by
        simp only [aa]; rw [mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      have hamgm : 2 * aa ≤ η + aa ^ 2 / η := by
        rw [div_eq_mul_inv]
        have hi : η * η⁻¹ = 1 := mul_inv_cancel₀ hη0.ne'
        nlinarith [sq_nonneg (aa - η), inv_pos.2 hη0, mul_nonneg (sq_nonneg (aa - η)) (inv_nonneg.2 hη0.le)]
      calc |Sre a x - Vth m a N x| * w x * rho s x ≤ aa * 2 := by
            simp only [aa]; exact mul_le_mul_of_nonneg_left (hρ2 x) ha
        _ = 2 * aa := by ring
        _ ≤ η + aa ^ 2 / η := hamgm
        _ ≤ η + (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) / η := by gcongr
    have hRi : IntegrableOn (fun x => η + (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) / η) (Ioc X (2 * X)) :=
      (integrableOn_const (by simp) (by simp)).add ((hDi.mul_const _).div_const _)
    calc |∫ x in Ioc X (2 * X), (fS x - fV x)| ≤ ∫ x in Ioc X (2 * X), |fS x - fV x| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in Ioc X (2 * X), (η + (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) / η) :=
          setIntegral_mono_on (hfS.sub hfV).abs hRi measurableSet_Ioc hbd
      _ = η * X + X * dX / η := by
          have hc1 : IntegrableOn (fun _ : ℝ => η) (Ioc X (2 * X)) := integrableOn_const (by simp) (by simp)
          rw [integral_add (f := fun _ => η) (g := fun x => (Sre a x - Vth m a N x) ^ 2 * X ^ (-(2 * (m : ℝ) - 1 / 2)) / η)
            hc1 ((hDi.mul_const _).div_const _),
            setIntegral_const, integral_div, integral_mul_const]
          rw [Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]
          have hXp : 0 < X ^ (2 * (m : ℝ) + 1 / 2) := by positivity
          have e : X ^ (-(2 * (m : ℝ) - 1 / 2)) = X / X ^ (2 * (m : ℝ) + 1 / 2) := by
            rw [Real.rpow_neg hX0.le, eq_div_iff hXp.ne']
            rw [show (2 * (m : ℝ) + 1 / 2) = 1 + (2 * (m : ℝ) - 1 / 2) by ring, Real.rpow_add hX0, Real.rpow_one]
            have : 0 < X ^ (2 * (m : ℝ) - 1 / 2) := by positivity
            field_simp
          rw [e]; simp only [dX]; ring
  -- combine
  have hsplitS : ∫ x in Ioc X (2 * X), fS x =
      (∫ x in Ioc X (2 * X), fV x) + ∫ x in Ioc X (2 * X), (fS x - fV x) := by
    rw [integral_sub hfS hfV]; ring
  have hkey : 1 / (π * √2) * (X / 2 - E) - (η * X + X * dX / η) ≤ c * (X + √(2 * X) / π) := by
    have := (abs_le.1 hD).1
    linarith
  -- bounds on the error terms, divided by X
  have hEX : E / (π * √2) ≤ g / 4 * X := by
    have hsb := sum_abs_bco_le hd hX
    have hEb : E ≤ X ^ (1 / 8 : ℝ) * St7 * (3 * √(2 * X) / π) :=
      mul_le_mul_of_nonneg_right hsb (by positivity)
    have h2' : 3 * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ) * X ≤ g / 4 * X := by
      exact mul_le_mul_of_nonneg_right h2.le hX0.le
    have e : X ^ (1 / 8 : ℝ) * St7 * (3 * √(2 * X) / π) / (π * √2) =
        3 * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ) * X := by
      have hA : X ^ (1 / 8 : ℝ) * √X = X ^ (5 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]; norm_num
      have hB : X ^ (-(3 / 8) : ℝ) * X = X ^ (5 / 8 : ℝ) := by
        rw [← Real.rpow_add_one hX0.ne']; norm_num
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) X]
      have h2s : (0 : ℝ) < √2 := by positivity
      have e1 : X ^ (1 / 8 : ℝ) * St7 * (3 * (√2 * √X) / π) / (π * √2) =
          3 * St7 / π ^ 2 * (X ^ (1 / 8 : ℝ) * √X) := by
        field_simp
      rw [e1, hA, mul_assoc, hB]
    calc E / (π * √2) ≤ X ^ (1 / 8 : ℝ) * St7 * (3 * √(2 * X) / π) / (π * √2) :=
          div_le_div_of_nonneg_right hEb (by positivity)
      _ = _ := e
      _ ≤ _ := h2'
  have hcX : c * (√(2 * X) / π) ≤ g / 4 * X := by
    have h3' := mul_le_mul_of_nonneg_right h3.le hX0.le
    have e : c * √2 / π * X ^ (-(1 / 2) : ℝ) * X = c * (√(2 * X) / π) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow X]
      have : X ^ (-(1 / 2) : ℝ) * X = X ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add_one hX0.ne']; norm_num
      calc c * √2 / π * X ^ (-(1 / 2) : ℝ) * X = c * √2 / π * (X ^ (-(1 / 2) : ℝ) * X) := by ring
        _ = _ := by rw [this]; ring
    linarith
  have hdX : X * dX / η < g / 4 * X := by
    have : dX / η < g / 4 := by rw [div_lt_iff₀ hη0]; linarith
    have := mul_lt_mul_of_pos_left this hX0
    calc X * dX / η = X * (dX / η) := by ring
      _ < X * (g / 4) := this
      _ = g / 4 * X := by ring
  have hmain : 1 / (π * √2) * (X / 2) = (c + g) * X := by
    rw [hg]; field_simp; ring
  have : 1 / (π * √2) * (X / 2 - E) = (c + g) * X - E / (π * √2) := by
    rw [mul_sub, hmain]; ring
  rw [this] at hkey
  have hηX : η * X = g / 4 * X := by rw [hη]
  have hexp : c * (X + √(2 * X) / π) = c * X + c * (√(2 * X) / π) := by ring
  have hexp2 : (c + g) * X = c * X + g * X := by ring
  rw [hexp, hexp2] at hkey
  linarith


/-- **`Ω₊(x^{23/4})` in every dyadic interval**: for `c < 1/(2π√2)` and all large `X` there is
`x ∈ [X, 2X]` with `S(x) > c x^{23/4}`. -/
theorem omega_plus (hd : VData m a) (ha1 : a 1 = 1) {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop, ∃ x ∈ Icc X (2 * X), c * x ^ ((m : ℝ) - 1 / 4) < Sre a x := by
  rcases le_or_gt 0 c with hc0 | hc0
  · filter_upwards [omega_core hd ha1 (Or.inl rfl) hc0 hc] with X ⟨x, hx, h⟩
    exact ⟨x, hx, by linarith⟩
  · have hp : (0 : ℝ) < 1 / (2 * π * √2) := by positivity
    filter_upwards [omega_core hd ha1 (Or.inl rfl) le_rfl hp, eventually_gt_atTop 0] with X ⟨x, hx, h⟩ hX
    refine ⟨x, hx, ?_⟩
    have : 0 ≤ x ^ ((m : ℝ) - 1 / 4) := Real.rpow_nonneg (by linarith [hx.1]) _
    nlinarith

/-- **`Ω₋(x^{23/4})` in every dyadic interval**: for `c < 1/(2π√2)` and all large `X` there is
`x ∈ [X, 2X]` with `S(x) < −c x^{23/4}`. -/
theorem omega_minus (hd : VData m a) (ha1 : a 1 = 1) {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop, ∃ x ∈ Icc X (2 * X), Sre a x < -c * x ^ ((m : ℝ) - 1 / 4) := by
  rcases le_or_gt 0 c with hc0 | hc0
  · filter_upwards [omega_core hd ha1 (Or.inr rfl) hc0 hc] with X ⟨x, hx, h⟩
    exact ⟨x, hx, by linarith⟩
  · have hp : (0 : ℝ) < 1 / (2 * π * √2) := by positivity
    filter_upwards [omega_core hd ha1 (Or.inr rfl) le_rfl hp, eventually_gt_atTop 0] with X ⟨x, hx, h⟩ hX
    refine ⟨x, hx, ?_⟩
    have : 0 ≤ x ^ ((m : ℝ) - 1 / 4) := Real.rpow_nonneg (by linarith [hx.1]) _
    nlinarith

end RamanujanTau.VoronoiTruncGeneral
