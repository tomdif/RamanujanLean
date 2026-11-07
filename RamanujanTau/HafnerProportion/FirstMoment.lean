/-
# The mollified first moment (Selberg's (H1)), unconditionally

For a mollifier `M(s) = Σ_{1≤n≤y} b(n) n^{11/2−s}` with `b(1) = 1`, `|b(n)| ≤ β n^η`
(`0 ≤ η ≤ 1`) and `y^{2+2η} ≤ T^{1/4}`, and all `0 ≤ a ≤ c ≤ 3T`, `T ≥ T₀(β,η)`:

    ∫_a^c |L(Δ,6+iu)| |M(6+iu)|² du ≥ (c − a)/2 − T/8.

Proof: Cauchy's theorem for the entire function `F = L·M²` on `[6, σ₁] × [a, c]`.  On the far
line `σ₁ = 9 + k₀`, `|L − 1| ≤ 1/32` and `|M − 1| ≤ 1/32` uniformly in `y` (the tail
`Σ_{n≥2} |b(n)| n^{11/2−σ₁} ≤ β 2^{−k₀} Σ n^{−2}`), so `|F − 1| ≤ 1/2`.  The horizontal sides are
`≪ T^{1/2+1/8} · β² y^{2+2η} ≤ T^{7/8}` by `tauL_right_half_bound` and `|M(σ+iv)| ≤ β y^{1+η}`.
Since `|LM²| = |L||M|² = |ZH| wM` on the line, this is a lower bound for `∫ |ZH| wM`.
-/
import RamanujanTau.HafnerProportion.Hardy

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HardyZeros RamanujanTau.HardyCount
open scoped Real Interval

lemma norm_Mc_term (b : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖b n * (n : ℂ) ^ ((11 / 2 : ℂ) - s)‖ = ‖b n‖ * (n : ℝ) ^ (11 / 2 - s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  congr 2
  simp

/-- `|M(s)| ≤ β y^{1+η}` for `Re s ≥ 6`. -/
lemma norm_Mc_le {b : ℕ → ℂ} {y : ℕ} {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hy : 1 ≤ y)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) {s : ℂ} (hs : 6 ≤ s.re) :
    ‖Mc b y s‖ ≤ β * (y : ℝ) ^ (1 + η) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hterm : ∀ n ∈ Finset.Icc 1 y, ‖b n * (n : ℂ) ^ ((11 / 2 : ℂ) - s)‖ ≤ β * (y : ℝ) ^ η := by
    intro n hn
    obtain ⟨hn1, hny⟩ := Finset.mem_Icc.mp hn
    rw [norm_Mc_term b (by omega) s]
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hny' : (n : ℝ) ≤ y := by exact_mod_cast hny
    have hp : (n : ℝ) ^ (11 / 2 - s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
    have hp0 : 0 ≤ (n : ℝ) ^ (11 / 2 - s.re) := by positivity
    have hbn : ‖b n‖ ≤ β * (y : ℝ) ^ η :=
      (hb n).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hny' hη0) hβ)
    calc ‖b n‖ * (n : ℝ) ^ (11 / 2 - s.re) ≤ ‖b n‖ * 1 :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ β * (y : ℝ) ^ η := by rw [mul_one]; exact hbn
  unfold Mc
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Real.rpow_add hy0, Real.rpow_one]
  rw [show y + 1 - 1 = y by omega]
  ring_nf
  rfl

/-- `|M(s) − 1| ≤ β 2^{−k₀}` on `Re s = 9 + k₀`, uniformly in `y`. -/
lemma norm_Mc_sub_one_le {b : ℕ → ℂ} {y : ℕ} {β η : ℝ} (hβ : 0 ≤ β) (hη1 : η ≤ 1)
    (hy : 1 ≤ y) (hb1 : b 1 = 1) (hb : ∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) (k₀ : ℕ) {s : ℂ}
    (hs : s.re = 7 + ((k₀ + 2 : ℕ) : ℝ)) :
    ‖Mc b y s - 1‖ ≤ β * (1 / 2) ^ k₀ := by
  unfold Mc
  rw [Finset.Icc_eq_cons_Ioc hy, Finset.sum_cons, hb1]
  simp only [Nat.cast_one, Complex.one_cpow, mul_one, add_sub_cancel_left]
  have hterm : ∀ n ∈ Finset.Ioc 1 y, ‖b n * (n : ℂ) ^ ((11 / 2 : ℂ) - s)‖ ≤
      β * (1 / 2) ^ k₀ * ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Ioc.mp hn
    rw [norm_Mc_term b (by omega) s, hs]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ n := by linarith
    have hnp : (0 : ℝ) < n := by linarith
    have hpow : (n : ℝ) ^ η * (n : ℝ) ^ (11 / 2 - (7 + ((k₀ + 2 : ℕ) : ℝ))) ≤
        (1 / 2) ^ k₀ * ((n : ℝ) ^ 2)⁻¹ := by
      rw [← Real.rpow_add hnp]
      have hex : η + (11 / 2 - (7 + ((k₀ + 2 : ℕ) : ℝ))) ≤ -(((k₀ + 2 : ℕ) : ℝ)) := by
        push_cast; linarith
      refine (Real.rpow_le_rpow_of_exponent_le hn1' hex).trans ?_
      rw [Real.rpow_neg hnp.le, Real.rpow_natCast, pow_add, mul_inv, mul_comm]
      have h2 : ((n : ℝ) ^ k₀)⁻¹ ≤ (1 / 2) ^ k₀ := by
        rw [one_div, inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hn2 k₀)
      have h3 : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
      nlinarith
    calc ‖b n‖ * (n : ℝ) ^ (11 / 2 - (7 + ((k₀ + 2 : ℕ) : ℝ)))
        ≤ β * (n : ℝ) ^ η * (n : ℝ) ^ (11 / 2 - (7 + ((k₀ + 2 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (hb n) (by positivity)
      _ = β * ((n : ℝ) ^ η * (n : ℝ) ^ (11 / 2 - (7 + ((k₀ + 2 : ℕ) : ℝ)))) := by ring
      _ ≤ β * ((1 / 2) ^ k₀ * ((n : ℝ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hpow hβ
      _ = β * (1 / 2) ^ k₀ * ((n : ℝ) ^ 2)⁻¹ := by ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsq : ∑ n ∈ Finset.Ioc 1 y, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := y) one_ne_zero hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ)⁻¹ := by positivity
    simp only [Nat.cast_one, inv_one] at this
    linarith
  have h0 : 0 ≤ β * (1 / 2 : ℝ) ^ k₀ := by positivity
  nlinarith

lemma norm_mul_sq_sub_one_le {x z : ℂ} (hx : ‖x - 1‖ ≤ 1 / 32) (hz : ‖z - 1‖ ≤ 1 / 32) :
    ‖x * z ^ 2 - 1‖ ≤ 1 / 2 := by
  have hz1 : ‖z‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' z 1  -- ‖z‖ ≤ ‖1‖ + ‖z - 1‖
    rw [norm_one] at this; linarith
  have hz2 : ‖z + 1‖ ≤ 3 := by
    have := norm_add_le z 1
    rw [norm_one] at this; linarith
  have e : x * z ^ 2 - 1 = (x - 1) * z ^ 2 + (z - 1) * (z + 1) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_pow]
  have h1 : ‖x - 1‖ * ‖z‖ ^ 2 ≤ 1 / 32 * 4 := by
    have : ‖z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg z]
    exact mul_le_mul hx this (by positivity) (by norm_num)
  have h2 : ‖z - 1‖ * ‖z + 1‖ ≤ 1 / 32 * 3 := mul_le_mul hz hz2 (norm_nonneg _) (by norm_num)
  linarith

/-- **Mollified first moment.** -/
theorem mollified_first_moment {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y → b 1 = 1 →
      (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) → (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) →
      ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 3 * T →
        (c - a) / 2 - T / 8 ≤ ∫ u in a..c, |ZH u| * wM b y u := by
  obtain ⟨S, hS0, hL⟩ := norm_tauL_sub_one_le_all
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (32 * (S + 1) * (β + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hk₀' : (1 / 2 : ℝ) ^ k₀ * (32 * (S + 1) * (β + 1)) < 1 := by
    rwa [lt_div_iff₀ (by positivity)] at hk₀
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ k₀ := by positivity
  have hLS : (1 / 2 : ℝ) ^ (k₀ + 2) * S ≤ 1 / 32 := by
    have : (1 / 2 : ℝ) ^ (k₀ + 2) ≤ (1 / 2) ^ k₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h1 : (1 / 2 : ℝ) ^ k₀ * S * 32 ≤ 1 := by nlinarith
    nlinarith
  have hMS : β * (1 / 2 : ℝ) ^ k₀ ≤ 1 / 32 := by nlinarith
  set σ₁ : ℝ := 7 + ((k₀ + 2 : ℕ) : ℝ) with hσ₁
  have hσ₁6 : 6 ≤ σ₁ := by
    simp only [hσ₁]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k₀]
  obtain ⟨C, hC0, hC⟩ := tauL_right_half_bound (ε := 1 / 8) (by norm_num) (by norm_num)
  set W : ℝ := (σ₁ - 6) * (4 * C * β ^ 2) with hW
  have hW0 : 0 ≤ W := by rw [hW]; have := sub_nonneg.mpr hσ₁6; positivity
  refine ⟨(16 * W + 1) ^ 8, one_le_pow₀ (by linarith), fun T hT b y hy hb1 hb hyT a c ha hac hc => ?_⟩
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by linarith)) hT
  have hT0 : 0 < T := by linarith
  -- `16 W ≤ T^{1/8}`
  have hT8 : 16 * W + 1 ≤ T ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hT (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by linarith) (by norm_num)] at h
    convert h using 2; norm_num
  have hsplitT : T ^ (1 / 8 : ℝ) * T ^ (7 / 8 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have hWT : 2 * (W * T ^ (7 / 8 : ℝ)) ≤ T / 8 := by
    have h78 : 0 ≤ T ^ (7 / 8 : ℝ) := by positivity
    nlinarith
  -- the function
  set F : ℂ → ℂ := fun s => tauL s * Mc b y s ^ 2 with hFdef
  have hFd : Differentiable ℂ F := tauLSeries_entire.mul ((differentiable_Mc b y).pow 2)
  -- far line
  have hfar : ∀ v : ℝ, ‖F (σ₁ + v * I) - 1‖ ≤ 1 / 2 := by
    intro v
    refine norm_mul_sq_sub_one_le ?_ ?_
    · exact (hL (k₀ + 2) v).trans hLS
    · refine (norm_Mc_sub_one_le hβ hη1 hy hb1 hb k₀ ?_).trans hMS
      simp [hσ₁]
  -- horizontal sides
  have hside : ∀ v : ℝ, |v| ≤ 3 * T → ‖∫ x : ℝ in (6 : ℝ)..σ₁, F (x + v * I)‖ ≤
      W * T ^ (7 / 8 : ℝ) := by
    intro v hv
    have hpt : ∀ x ∈ Ι (6 : ℝ) σ₁, ‖F (x + v * I)‖ ≤ 4 * C * β ^ 2 * T ^ (7 / 8 : ℝ) := by
      intro x hx
      rw [Set.uIoc_of_le hσ₁6] at hx
      have hx6 : 6 ≤ x := hx.1.le
      have hre : 6 ≤ ((x : ℂ) + v * I).re := by simp [hx6]
      have hL1 := hC x v hx6
      have hM1 := norm_Mc_le hβ hη0 hy hb hre
      have hy0 : (0 : ℝ) ≤ y := by positivity
      have hM2 : ‖Mc b y ((x : ℂ) + v * I)‖ ^ 2 ≤ β ^ 2 * T ^ (1 / 4 : ℝ) := by
        have e : (β * (y : ℝ) ^ (1 + η)) ^ 2 = β ^ 2 * (y : ℝ) ^ (2 + 2 * η) := by
          rw [mul_pow, ← Real.rpow_natCast ((y : ℝ) ^ (1 + η)), ← Real.rpow_mul hy0]
          congr 2; push_cast; ring
        calc ‖Mc b y ((x : ℂ) + v * I)‖ ^ 2 ≤ (β * (y : ℝ) ^ (1 + η)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hM1 2
          _ = β ^ 2 * (y : ℝ) ^ (2 + 2 * η) := e
          _ ≤ β ^ 2 * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hyT (sq_nonneg β)
      have hv' : 1 + |v| ≤ 4 * T := by linarith
      have hpw : (1 + |v|) ^ (1 / 2 + 1 / 8 : ℝ) ≤ 4 * T ^ (5 / 8 : ℝ) := by
        calc (1 + |v|) ^ (1 / 2 + 1 / 8 : ℝ) ≤ (4 * T) ^ (1 / 2 + 1 / 8 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hv' (by norm_num)
          _ = 4 ^ (5 / 8 : ℝ) * T ^ (5 / 8 : ℝ) := by
              rw [Real.mul_rpow (by norm_num) hT0.le]; norm_num
          _ ≤ 4 * T ^ (5 / 8 : ℝ) := by
              gcongr
              calc (4 : ℝ) ^ (5 / 8 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 4 := Real.rpow_one 4
      have hLb : ‖tauL ((x : ℂ) + v * I)‖ ≤ C * (4 * T ^ (5 / 8 : ℝ)) :=
        hL1.trans (mul_le_mul_of_nonneg_left hpw hC0)
      have e78 : T ^ (5 / 8 : ℝ) * T ^ (1 / 4 : ℝ) = T ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add hT0]; norm_num
      calc ‖F (x + v * I)‖ = ‖tauL ((x : ℂ) + v * I)‖ * ‖Mc b y ((x : ℂ) + v * I)‖ ^ 2 := by
            simp only [hFdef, norm_mul, norm_pow]
        _ ≤ C * (4 * T ^ (5 / 8 : ℝ)) * (β ^ 2 * T ^ (1 / 4 : ℝ)) :=
            mul_le_mul hLb hM2 (by positivity) (by positivity)
        _ = 4 * C * β ^ 2 * (T ^ (5 / 8 : ℝ) * T ^ (1 / 4 : ℝ)) := by ring
        _ = 4 * C * β ^ 2 * T ^ (7 / 8 : ℝ) := by rw [e78]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (by linarith)] at this
    calc _ ≤ 4 * C * β ^ 2 * T ^ (7 / 8 : ℝ) * (σ₁ - 6) := this
      _ = W * T ^ (7 / 8 : ℝ) := by rw [hW]; ring
  -- rectangle
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((6 : ℂ) + a * I) ((σ₁ : ℂ) + c * I) hFd.differentiableOn
  have e1 : ((6 : ℂ) + a * I).re = 6 := by simp
  have e2 : ((6 : ℂ) + a * I).im = a := by simp
  have e3 : ((σ₁ : ℂ) + c * I).re = σ₁ := by simp
  have e4 : ((σ₁ : ℂ) + c * I).im = c := by simp
  rw [e1, e2, e3, e4] at hrect
  set Ha := ∫ x : ℝ in (6 : ℝ)..σ₁, F (x + a * I) with hHa
  set Hc := ∫ x : ℝ in (6 : ℝ)..σ₁, F (x + c * I) with hHc
  set X := ∫ v : ℝ in a..c, F (σ₁ + v * I) with hX
  set Y := ∫ v : ℝ in a..c, F (((6 : ℝ) : ℂ) + v * I) with hY
  have hEq : I • Y = Ha - Hc + I • X := by linear_combination -hrect
  have hHa' : ‖Ha‖ ≤ W * T ^ (7 / 8 : ℝ) := hside a (by rw [abs_of_nonneg ha]; linarith)
  have hHc' : ‖Hc‖ ≤ W * T ^ (7 / 8 : ℝ) :=
    hside c (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hcR : Continuous fun v : ℝ => F (σ₁ + v * I) := hFd.continuous.comp (by fun_prop)
  have hXsub : X - ((c - a : ℝ) : ℂ) = ∫ v : ℝ in a..c, (F (σ₁ + v * I) - 1) := by
    rw [intervalIntegral.integral_sub (hcR.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [hX]
  have hXb : ‖X - ((c - a : ℝ) : ℂ)‖ ≤ (c - a) / 2 := by
    rw [hXsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := c) (C := 1 / 2) (f := fun v : ℝ => F (σ₁ + v * I) - 1)
      (fun v _ => hfar v)
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hXl : (c - a) / 2 ≤ ‖X‖ := by
    have h1 := norm_sub_norm_le (((c - a : ℝ) : ℂ)) X
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
    linarith
  have hYl : (c - a) / 2 - T / 8 ≤ ‖Y‖ := by
    have hn : ‖Y‖ = ‖I • Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [hn, hEq]
    have h3 : ‖I • X‖ = ‖X‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 := norm_sub_norm_le (I • X) (-(Ha - Hc))
    rw [sub_neg_eq_add, norm_neg, h3, add_comm] at h1
    have h2 := norm_sub_le Ha Hc
    linarith
  refine hYl.trans ?_
  have e6 : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
  rw [hY, e6]
  refine (intervalIntegral.norm_integral_le_integral_norm hac).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [hFdef]
  exact norm_LM2_line b y u

end RamanujanTau.HafnerProportion
