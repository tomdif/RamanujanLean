/-
# A mean-value theorem for `Σ cₙ cos(4π√(ny) − π/4)` with weight `y^p√y`

Generalizes `VoronoiTrunc/MeanValue.lean` (`p = 11`) to every `p`; the bound becomes
`b^{p+1} √M (2 H_M + 1) Σ cₙ²`.  The original statement (for `p = 11`) follows.

`mean_value`: for a finite set `F ⊆ [1, M]` of integers, real `cₙ` and `1 ≤ a ≤ b`,

    |∫_a^b y^{11}√y (Σ_{n∈F} cₙ cos(4π√n√y − π/4))² dy − ½ (Σ cₙ²) ∫_a^b y^{11}√y dy|
        ≤ b^{12} √M (2 H_M + 1) Σ cₙ²,

`H_M` the harmonic number.  Off-diagonal terms are bounded by one integration by parts
(`abs_integral_w_cos_le`: `|∫_a^b y^{11}√y cos(4πδ√y + φ)| ≤ b^{12}/(π|δ|)`), then by the
Schur test with `1/|√m−√n| ≤ 2√M/|m−n|` and `Σ_{n≠m} 1/|m−n| ≤ 2H_M`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Real MeasureTheory Set Filter Topology

variable (p : ℕ)

/-- The weight `w_p(y) = y^p √y` (`= y^{p+1/2}`; `p = 2m − 1` for weight `2m`). -/
noncomputable def wt (y : ℝ) : ℝ := y ^ p * √y

lemma continuous_wt : Continuous (wt p) := by unfold wt; fun_prop

variable {p}

/-- **One integration by parts.** -/
theorem abs_integral_w_cos_le {δ φ a b : ℝ} (hδ : δ ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    |∫ y in a..b, (wt p y) * Real.cos (4 * π * δ * √y + φ)| ≤ b ^ (p + 1) / (π * |δ|) := by
  have hδπ : 2 * π * δ ≠ 0 := mul_ne_zero (by positivity) hδ
  set F : ℝ → ℝ := fun y => y ^ (p + 1) * Real.sin (4 * π * δ * √y + φ) / (2 * π * δ) with hF
  set g : ℝ → ℝ := fun y => (p + 1) * y ^ p * Real.sin (4 * π * δ * √y + φ) / (2 * π * δ) with hg
  have hd : ∀ y ∈ Set.uIcc a b, HasDerivAt F (g y + (wt p y) * Real.cos (4 * π * δ * √y + φ)) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hs : HasDerivAt (fun y => √y) (1 / (2 * √y)) y := by
      have := Real.hasDerivAt_sqrt hy0.ne'
      simpa using this
    have h1 : HasDerivAt (fun y => 4 * π * δ * √y + φ) (4 * π * δ * (1 / (2 * √y))) y :=
      (hs.const_mul (4 * π * δ)).add_const φ
    have h2 := ((hasDerivAt_pow (p + 1) y).mul h1.sin).div_const (2 * π * δ)
    convert h2 using 1
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    have hsq : √y * √y = y := Real.mul_self_sqrt hy0.le
    rw [Nat.add_sub_cancel]
    push_cast
    simp only [hg, wt]
    field_simp
    rw [show y ^ (p + 1) = y ^ p * (√y * √y) by rw [hsq]; ring]
    ring
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hwc : Continuous fun y => (wt p y) * Real.cos (4 * π * δ * √y + φ) := by
    unfold wt; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hgc.add hwc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hgc.intervalIntegrable _ _) (hwc.intervalIntegrable _ _)] at hint
  have e : ∫ y in a..b, (wt p y) * Real.cos (4 * π * δ * √y + φ) = F b - F a - ∫ y in a..b, g y := by
    linarith
  rw [e]
  have hπδ : 0 < π * |δ| := by positivity
  have hFb : |F b| ≤ b ^ (p + 1) / (2 * π * |δ|) := by
    simp only [hF, abs_div, abs_mul, abs_pow]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos Real.pi_pos,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ b)]
    gcongr
    calc b ^ (p + 1) * |Real.sin (4 * π * δ * √b + φ)| ≤ b ^ (p + 1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (pow_nonneg (by linarith) _)
      _ = b ^ (p + 1) := mul_one _
  have hFa : |F a| ≤ a ^ (p + 1) / (2 * π * |δ|) := by
    simp only [hF, abs_div, abs_mul, abs_pow]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos Real.pi_pos, abs_of_pos ha]
    gcongr
    calc a ^ (p + 1) * |Real.sin (4 * π * δ * √a + φ)| ≤ a ^ (p + 1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (pow_nonneg ha.le _)
      _ = a ^ (p + 1) := mul_one _
  have hG : |∫ y in a..b, g y| ≤ (b ^ (p + 1) - a ^ (p + 1)) / (2 * π * |δ|) := by
    have hb : ∀ y ∈ Set.Icc a b, |g y| ≤ (p + 1) * y ^ p / (2 * π * |δ|) := by
      intro y hy
      have hy0 : 0 ≤ y := by linarith [hy.1]
      have h12 : 0 ≤ (p + 1) * y ^ p := by positivity
      have hn : |(p + 1) * y ^ p * Real.sin (4 * π * δ * √y + φ)| ≤ (p + 1) * y ^ p := by
        rw [abs_mul, abs_of_nonneg h12]
        nlinarith [Real.abs_sin_le_one (4 * π * δ * √y + φ), abs_nonneg (Real.sin (4 * π * δ * √y + φ))]
      have hd2 : |2 * π * δ| = 2 * π * |δ| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      simp only [hg]
      rw [abs_div, hd2]
      exact div_le_div_of_nonneg_right hn (by positivity)
    have h1 := intervalIntegral.abs_integral_le_integral_abs (f := g) (μ := volume) hab
    have h2 : ∫ y in a..b, |g y| ≤ ∫ y in a..b, (p + 1) * y ^ p / (2 * π * |δ|) :=
      intervalIntegral.integral_mono_on hab (hgc.abs.intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop) hb
    have h3 : ∫ y in a..b, (p + 1) * y ^ p / (2 * π * |δ|) = (b ^ (p + 1) - a ^ (p + 1)) / (2 * π * |δ|) := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
      field_simp
    linarith
  have hb12 : a ^ (p + 1) ≤ b ^ (p + 1) := pow_le_pow_left₀ ha.le hab (p + 1)
  calc |F b - F a - ∫ y in a..b, g y| ≤ |F b| + |F a| + |∫ y in a..b, g y| := by
        have := abs_sub (F b - F a) (∫ y in a..b, g y)
        have := abs_sub (F b) (F a)
        linarith
    _ ≤ b ^ (p + 1) / (2 * π * |δ|) + a ^ (p + 1) / (2 * π * |δ|) + (b ^ (p + 1) - a ^ (p + 1)) / (2 * π * |δ|) := by
        linarith
    _ = b ^ (p + 1) / (π * |δ|) := by field_simp; ring


/-! ### Combinatorial sums -/

/-- `Hs M = Σ_{k=1}^M 1/k` (harmonic number). -/
noncomputable def Hs (M : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 M, (1 / (k : ℝ))

lemma Hs_nonneg (M : ℕ) : 0 ≤ Hs M := Finset.sum_nonneg fun _ _ => by positivity

lemma Hs_le_log (M : ℕ) : Hs M ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at h
  unfold Hs
  convert h using 1
  push_cast; simp [one_div]

lemma sum_inv_sqrt_le (M : ℕ) : ∑ n ∈ Finset.Icc 1 M, (1 / √(n : ℝ)) ≤ 2 * √(M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have h1 : 0 ≤ √(M : ℝ) := Real.sqrt_nonneg _
    have h2 : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have h3 : √(M : ℝ) ≤ √((M : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hs : √((M : ℝ) + 1) * √((M : ℝ) + 1) = (M : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
    have hs' : √(M : ℝ) * √(M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by positivity)
    have key : 1 / √((M : ℝ) + 1) ≤ 2 * √((M : ℝ) + 1) - 2 * √(M : ℝ) := by
      rw [div_le_iff₀ h2]
      nlinarith [sq_nonneg (√((M : ℝ) + 1) - √(M : ℝ))]
    linarith

lemma sum_inv_dist_le {M m : ℕ} (hm : m ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (if n = m then 0 else 1 / |(m : ℝ) - n|) ≤ 2 * Hs M := by
  classical
  have hsplit : ∀ n ∈ Finset.Icc 1 M, (if n = m then 0 else 1 / |(m : ℝ) - n|) =
      (if n < m then 1 / ((m - n : ℕ) : ℝ) else 0) + (if m < n then 1 / ((n - m : ℕ) : ℝ) else 0) := by
    intro n _
    rcases lt_trichotomy n m with h | h | h
    · rw [if_neg h.ne, if_pos h, if_neg (by omega), add_zero, Nat.cast_sub h.le,
        abs_of_pos (by have : (n : ℝ) < m := by exact_mod_cast h
                       linarith)]
    · subst h; simp
    · rw [if_neg h.ne', if_neg (by omega), if_pos h, zero_add, Nat.cast_sub h.le,
        abs_of_neg (by have : (m : ℝ) < n := by exact_mod_cast h
                       linarith), neg_sub]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, two_mul]
  apply add_le_add
  · rw [← Finset.sum_filter]
    rw [← Finset.sum_image (s := (Finset.Icc 1 M).filter (· < m)) (g := fun n => m - n)
      (f := fun k : ℕ => 1 / (k : ℝ)) (by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hx hy
        simp only at hxy; omega)]
    unfold Hs
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨n, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]; omega
  · rw [← Finset.sum_filter]
    rw [← Finset.sum_image (s := (Finset.Icc 1 M).filter (m < ·)) (g := fun n => n - m)
      (f := fun k : ℕ => 1 / (k : ℝ)) (by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hx hy
        simp only at hxy; omega)]
    unfold Hs
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨n, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]; omega


/-! ### The mean value theorem -/

/-- The Voronoi phase `θₙ(y) = 4π√n√y − π/4`. -/
noncomputable def th (n : ℕ) (y : ℝ) : ℝ := 4 * π * √(n : ℝ) * √y - π / 4

lemma continuous_th (n : ℕ) : Continuous (th n) := by unfold th; fun_prop

lemma cos_mul_cos' (A B : ℝ) : Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The off-diagonal majorant. -/
noncomputable def Kmn (p M : ℕ) (b : ℝ) (m n : ℕ) : ℝ :=
  b ^ (p + 1) / (2 * π) * ((if n = m then 0 else 2 * √(M : ℝ) / |(m : ℝ) - n|) + 1 / (√(m : ℝ) + √(n : ℝ)))

lemma Kmn_symm (M : ℕ) (b : ℝ) (m n : ℕ) : Kmn p M b m n = Kmn p M b n m := by
  unfold Kmn
  congr 2
  · by_cases h : n = m
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]
  · rw [add_comm]

lemma Kmn_nonneg (M : ℕ) {b : ℝ} (hb : 0 ≤ b) (m n : ℕ) : 0 ≤ Kmn p M b m n := by
  unfold Kmn
  have : 0 ≤ (if n = m then (0 : ℝ) else 2 * √(M : ℝ) / |(m : ℝ) - n|) := by
    split_ifs <;> positivity
  positivity

lemma abs_I_sub_le {M : ℕ} {m n : ℕ} (hm : 1 ≤ m ∧ m ≤ M) (hn : 1 ≤ n ∧ n ≤ M) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∫ y in a..b, (wt p y) * (Real.cos (th m y) * Real.cos (th n y))) -
        (if m = n then (1 / 2) * ∫ y in a..b, (wt p y) else 0)| ≤ Kmn p M b m n := by
  have ha0 : 0 < a := by linarith
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm.1)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn.1)
  have e : ∀ y, (wt p y) * (Real.cos (th m y) * Real.cos (th n y)) =
      (1 / 2) * ((wt p y) * Real.cos (4 * π * (√(m : ℝ) - √(n : ℝ)) * √y + 0)) +
      (1 / 2) * ((wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(n : ℝ)) * √y + (-(π / 2)))) := by
    intro y; rw [cos_mul_cos']; unfold th; ring_nf
  have hc1 : Continuous fun y => (wt p y) * Real.cos (4 * π * (√(m : ℝ) - √(n : ℝ)) * √y + 0) := by
    unfold wt; fun_prop
  have hc2 : Continuous fun y => (wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(n : ℝ)) * √y + (-(π / 2))) := by
    unfold wt; fun_prop
  simp_rw [e]
  rw [intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
      ((hc2.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the "+" frequency
  have h2 := abs_integral_w_cos_le (p := p) (δ := √(m : ℝ) + √(n : ℝ)) (φ := -(π / 2)) (by positivity) ha0 hab
  rw [abs_of_pos (by positivity : 0 < √(m : ℝ) + √(n : ℝ))] at h2
  have hb12 : 0 ≤ b ^ (p + 1) := pow_nonneg (by linarith) _
  unfold Kmn
  by_cases hmn : m = n
  · subst hmn
    simp only [if_true, sub_self, mul_zero, zero_mul, add_zero, Real.cos_zero, mul_one]
    set A := ∫ y in a..b, (wt p y)
    set B := ∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(m : ℝ)) * √y + -(π / 2))
    have e2 : (1 / 2) * A + (1 / 2) * B - (1 / 2) * A = (1 / 2) * B := by ring
    rw [e2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * |B| ≤ 1 / 2 * (b ^ (p + 1) / (π * (√(m : ℝ) + √(m : ℝ)))) := by gcongr
      _ = b ^ (p + 1) / (2 * π) * (0 + 1 / (√(m : ℝ) + √(m : ℝ))) := by field_simp; ring
  · rw [if_neg hmn, if_neg (Ne.symm hmn), sub_zero]
    have hne : √(m : ℝ) - √(n : ℝ) ≠ 0 := by
      intro h
      have : √(m : ℝ) = √(n : ℝ) := by linarith
      have := congrArg (· ^ 2) this
      simp only [Real.sq_sqrt (Nat.cast_nonneg _)] at this
      exact hmn (by exact_mod_cast this)
    have h1 := abs_integral_w_cos_le (p := p) (δ := √(m : ℝ) - √(n : ℝ)) (φ := 0) hne ha0 hab
    -- 1/|√m − √n| ≤ 2√M/|m − n|
    have hkey : 1 / |√(m : ℝ) - √(n : ℝ)| ≤ 2 * √(M : ℝ) / |(m : ℝ) - n| := by
      have hmn' : (m : ℝ) - n = (√(m : ℝ) - √(n : ℝ)) * (√(m : ℝ) + √(n : ℝ)) := by
        rw [show (√(m : ℝ) - √(n : ℝ)) * (√(m : ℝ) + √(n : ℝ)) = √(m : ℝ) ^ 2 - √(n : ℝ) ^ 2 by ring,
          Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      have hM1 : √(m : ℝ) ≤ √(M : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hm.2)
      have hM2 : √(n : ℝ) ≤ √(M : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn.2)
      have hpos : 0 < |√(m : ℝ) - √(n : ℝ)| := abs_pos.2 hne
      rw [hmn', abs_mul, abs_of_pos (by positivity : 0 < √(m : ℝ) + √(n : ℝ)),
        div_le_div_iff₀ hpos (by positivity)]
      nlinarith
    have e3 : (1 / 2) * (∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) - √(n : ℝ)) * √y + 0)) +
        (1 / 2) * ∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(n : ℝ)) * √y + -(π / 2)) =
        (1 / 2) * (∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) - √(n : ℝ)) * √y + 0)) +
        (1 / 2) * ∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(n : ℝ)) * √y + -(π / 2)) := rfl
    have hπ : 0 < π := Real.pi_pos
    calc _ ≤ (1 / 2) * |∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) - √(n : ℝ)) * √y + 0)| +
          (1 / 2) * |∫ y in a..b, (wt p y) * Real.cos (4 * π * (√(m : ℝ) + √(n : ℝ)) * √y + -(π / 2))| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ (1 / 2) * (b ^ (p + 1) / (π * |√(m : ℝ) - √(n : ℝ)|)) +
          (1 / 2) * (b ^ (p + 1) / (π * (√(m : ℝ) + √(n : ℝ)))) := by gcongr
      _ = b ^ (p + 1) / (2 * π) * (1 / |√(m : ℝ) - √(n : ℝ)| + 1 / (√(m : ℝ) + √(n : ℝ))) := by
          field_simp
      _ ≤ b ^ (p + 1) / (2 * π) * (2 * √(M : ℝ) / |(m : ℝ) - n| + 1 / (√(m : ℝ) + √(n : ℝ))) := by
          gcongr

lemma sum_Kmn_le {M : ℕ} (F : Finset ℕ) (hF : ∀ n ∈ F, 1 ≤ n ∧ n ≤ M) {b : ℝ} (hb : 0 ≤ b)
    {m : ℕ} (hm : m ≤ M) :
    ∑ n ∈ F, Kmn p M b m n ≤ b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1) := by
  have hsub : F ⊆ Finset.Icc 1 M := fun n hn => Finset.mem_Icc.2 (hF n hn)
  unfold Kmn
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 : ∑ n ∈ F, (if n = m then (0 : ℝ) else 2 * √(M : ℝ) / |(m : ℝ) - n|) ≤
      2 * √(M : ℝ) * (2 * Hs M) := by
    calc ∑ n ∈ F, (if n = m then (0 : ℝ) else 2 * √(M : ℝ) / |(m : ℝ) - n|)
        ≤ ∑ n ∈ Finset.Icc 1 M, (if n = m then (0 : ℝ) else 2 * √(M : ℝ) / |(m : ℝ) - n|) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by split_ifs <;> positivity)
      _ = 2 * √(M : ℝ) * ∑ n ∈ Finset.Icc 1 M, (if n = m then (0 : ℝ) else 1 / |(m : ℝ) - n|) := by
          rw [Finset.mul_sum]; congr 1; funext n; split_ifs <;> ring
      _ ≤ 2 * √(M : ℝ) * (2 * Hs M) := by gcongr; exact sum_inv_dist_le hm
  have h2 : ∑ n ∈ F, 1 / (√(m : ℝ) + √(n : ℝ)) ≤ 2 * √(M : ℝ) := by
    calc ∑ n ∈ F, 1 / (√(m : ℝ) + √(n : ℝ)) ≤ ∑ n ∈ F, 1 / √(n : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (hF n hn).1)
          exact one_div_le_one_div_of_le this (by linarith [Real.sqrt_nonneg (m : ℝ)])
      _ ≤ ∑ n ∈ Finset.Icc 1 M, 1 / √(n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 * √(M : ℝ) := sum_inv_sqrt_le M
  have hb12 : 0 ≤ b ^ (p + 1) := by positivity
  have hπ : 1 ≤ π := by linarith [Real.two_le_pi]
  calc b ^ (p + 1) / (2 * π) * (∑ n ∈ F, (if n = m then (0 : ℝ) else 2 * √(M : ℝ) / |(m : ℝ) - n|) +
        ∑ n ∈ F, 1 / (√(m : ℝ) + √(n : ℝ)))
      ≤ b ^ (p + 1) / (2 * π) * (2 * √(M : ℝ) * (2 * Hs M) + 2 * √(M : ℝ)) := by gcongr
    _ = b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1) / π := by field_simp
    _ ≤ b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1) := by
        apply div_le_self (by have := Hs_nonneg M; positivity) hπ

/-- **Mean value theorem** for Voronoi-type cosine sums. -/
theorem mean_value {M : ℕ} (F : Finset ℕ) (hF : ∀ n ∈ F, 1 ≤ n ∧ n ≤ M) (c : ℕ → ℝ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∫ y in a..b, (wt p y) * (∑ n ∈ F, c n * Real.cos (th n y)) ^ 2) -
        (1 / 2) * (∑ n ∈ F, c n ^ 2) * ∫ y in a..b, (wt p y)| ≤
      b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1) * ∑ n ∈ F, c n ^ 2 := by
  have hb : 0 ≤ b := by linarith
  have hcont : ∀ m n : ℕ, Continuous fun y => (wt p y) * (Real.cos (th m y) * Real.cos (th n y)) :=
    fun m n => (continuous_wt p).mul ((Real.continuous_cos.comp (continuous_th m)).mul
      (Real.continuous_cos.comp (continuous_th n)))
  have e1 : ∀ y, (wt p y) * (∑ n ∈ F, c n * Real.cos (th n y)) ^ 2 =
      ∑ m ∈ F, ∑ n ∈ F, c m * c n * ((wt p y) * (Real.cos (th m y) * Real.cos (th n y))) := by
    intro y
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [e1]
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (hcont m n))]
  have e2 : ∀ m ∈ F, ∫ y in a..b, ∑ n ∈ F, c m * c n * ((wt p y) * (Real.cos (th m y) * Real.cos (th n y))) =
      ∑ n ∈ F, c m * c n * ∫ y in a..b, (wt p y) * (Real.cos (th m y) * Real.cos (th n y)) := by
    intro m _
    rw [intervalIntegral.integral_finsetSum
      (f := fun n y => c m * c n * ((wt p y) * (Real.cos (th m y) * Real.cos (th n y)))) (fun n _ =>
      ((continuous_const.mul (hcont m n)).intervalIntegrable _ _))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl e2]
  set J := ∫ y in a..b, (wt p y)
  have e3 : (1 / 2) * (∑ n ∈ F, c n ^ 2) * J =
      ∑ m ∈ F, ∑ n ∈ F, c m * c n * (if m = n then (1 / 2) * J else 0) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m (fun n _ hn => by rw [if_neg (Ne.symm hn), mul_zero])
      (fun h => absurd hm h), if_pos rfl]
    ring
  rw [e3, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  set D := fun m n => (∫ y in a..b, (wt p y) * (Real.cos (th m y) * Real.cos (th n y))) -
    (if m = n then (1 / 2) * J else 0)
  have hD : ∀ m ∈ F, ∀ n ∈ F, |D m n| ≤ Kmn p M b m n :=
    fun m hm n hn => abs_I_sub_le (hF m hm) (hF n hn) ha hab
  calc |∑ m ∈ F, ∑ n ∈ F, c m * c n * D m n|
      ≤ ∑ m ∈ F, ∑ n ∈ F, |c m| * |c n| * Kmn p M b m n := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [abs_mul, abs_mul]
        gcongr
        exact hD m hm n hn
    _ ≤ ∑ m ∈ F, ∑ n ∈ F, ((c m ^ 2 + c n ^ 2) / 2) * Kmn p M b m n := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
        gcongr
        · exact Kmn_nonneg M hb m n
        · nlinarith [sq_nonneg (|c m| - |c n|), sq_abs (c m), sq_abs (c n)]
    _ = ∑ m ∈ F, c m ^ 2 * ∑ n ∈ F, Kmn p M b m n := by
        have hsym : ∑ m ∈ F, ∑ n ∈ F, c n ^ 2 * Kmn p M b m n = ∑ m ∈ F, ∑ n ∈ F, c m ^ 2 * Kmn p M b m n := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
          rw [Kmn_symm]
        have : ∑ m ∈ F, ∑ n ∈ F, ((c m ^ 2 + c n ^ 2) / 2) * Kmn p M b m n =
            (1 / 2) * ∑ m ∈ F, ∑ n ∈ F, c m ^ 2 * Kmn p M b m n +
            (1 / 2) * ∑ m ∈ F, ∑ n ∈ F, c n ^ 2 * Kmn p M b m n := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
        rw [this, hsym]
        rw [show ∀ X : ℝ, (1 / 2) * X + (1 / 2) * X = X from fun X => by ring]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ F, c m ^ 2 * (b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        gcongr
        exact sum_Kmn_le F hF hb (hF m hm).2
    _ = b ^ (p + 1) * √(M : ℝ) * (2 * Hs M + 1) * ∑ n ∈ F, c n ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring

end RamanujanTau.VoronoiTruncGeneral
