/-
# Riesz means with a power-saving error from a continuation of `D(s)`

`rieszAsymp_of_continuation`: if `D(s) = ∑ aₙ n^{-s}` (`aₙ ≥ 0`, `∑ aₙ n^{-c} < ∞`, `c > 1`)
equals `F(s) + c₀/(s−1)` on the line `Re s = c`, where `F` is holomorphic on `Re s > σ₀` and
`‖F(s)‖ ≤ B (1 + |Im s|)^K` on `σ₁ ≤ Re s ≤ c` (`σ₀ < σ₁ ≤ 1`), then
`W a (K+1) x = c₀ x^{K+2}/(K+2) + O(x^{K+1+σ₁})`, i.e. `RieszAsymp a c₀ (K+1) (1 − σ₁)`.
-/
import RamanujanTau.RankinError.Perron

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

lemma Pk_div_sub_one (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Pk k s / (s - 1) = Pk (k + 1) (s - 1) / (k + 1) := by
  have hs0 : 0 < s.re := by linarith
  have h1 := prod_ne_zero_of_re_pos hs0 k
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  rw [Pk, Pk, Finset.prod_range_succ' _ (k + 1)]
  have e2 : ∏ j ∈ Finset.range (k + 1), (s - 1 + ((j + 1 : ℕ) : ℂ)) =
      ∏ j ∈ Finset.range (k + 1), (s + j) := by
    apply Finset.prod_congr rfl; intro j _; push_cast; ring
  rw [e2, Nat.factorial_succ]
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [Nat.cast_zero, add_zero]
  push_cast
  field_simp

lemma differentiableOn_Pk (k : ℕ) : DifferentiableOn ℂ (Pk k) {s : ℂ | 0 < s.re} := by
  intro s hs
  unfold Pk
  refine DifferentiableWithinAt.div (differentiableWithinAt_const _) ?_
    (prod_ne_zero_of_re_pos hs k)
  exact (DifferentiableAt.differentiableWithinAt (by fun_prop))

/-- The Riesz sum as a `tsum`. -/
lemma W_eq_tsum (a : ℕ → ℝ) (ha0 : a 0 = 0) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    W a k x = x ^ k * ∑' n : ℕ, a n * phi k (n / x) := by
  have hsupp : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊, a n * phi k (n / x) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [ha0]
    · have : ⌊x⌋₊ < n := by
        by_contra h; exact hn (Finset.mem_Icc.2 ⟨h0, by omega⟩)
      have hxn : x < n := (Nat.floor_lt hx.le).1 this
      rw [phi_of_gt hk ((one_lt_div hx).2 hxn), mul_zero]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) hsupp, W, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2).trans (Nat.floor_le hx.le)
  rw [phi_of_le ((div_le_one hx).2 hnx)]
  have : x - n = x * (1 - n / x) := by field_simp
  rw [this, mul_pow]; ring

theorem rieszAsymp_of_continuation (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) {K : ℕ}
    {c σ₀ σ₁ c₀ B : ℝ} (hc : 1 < c) (h01 : σ₀ < σ₁) (hσ₁ : 0 < σ₁) (hσ₁c : σ₁ ≤ c)
    (hσ₁1 : σ₁ ≤ 1) (hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-c))
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hD : ∀ s : ℂ, s.re = c → LSeries (fun n => (a n : ℂ)) s = F s + c₀ / (s - 1))
    (hFB : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖F s‖ ≤ B * (1 + |s.im|) ^ K) :
    RieszAsymp a c₀ (K + 1) (1 - σ₁) := by
  set k := K + 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hc0 : 0 < c := by linarith
  set m : ℝ := min σ₁ 1 with hm
  set M : ℝ := k.factorial * (2 / m) ^ (k + 1) * |B| with hM
  have hM0 : 0 ≤ M := by positivity
  -- bound for `Pk * F` on the strip
  have hPF : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖Pk k s * F s‖ ≤ M / (1 + |s.im|) ^ 2 := by
    intro s h1 h2
    have hP := norm_Pk_le k hσ₁ h1
    have hFs := hFB s h1 h2
    have ht : (0:ℝ) < 1 + |s.im| := by positivity
    rw [norm_mul]
    have hFs' : ‖F s‖ ≤ |B| * (1 + |s.im|) ^ K :=
      hFs.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
    calc ‖Pk k s‖ * ‖F s‖ ≤ (k.factorial * (2 / m) ^ (k + 1) / (1 + |s.im|) ^ (k + 1)) *
          (|B| * (1 + |s.im|) ^ K) := mul_le_mul hP hFs' (norm_nonneg _) (by positivity)
      _ = M / (1 + |s.im|) ^ 2 := by
          rw [hM, hkdef]; field_simp; ring
  -- the error integral
  have hI : Integrable fun y : ℝ => M / (1 + |y|) ^ 2 := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul M
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]; norm_cast
  set I₀ : ℝ := ∫ y : ℝ, M / (1 + |y|) ^ 2 with hI₀
  refine ⟨(I₀ / (2 * π) + |c₀|), fun x hx => ?_⟩
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- `x < 1`
    rw [W_eq_zero_of_lt_one a k hx1, zero_sub, abs_neg]
    have hI0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
    have hxe : x ^ (k + 1) ≤ x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge hx hx1.le
      push_cast; linarith
    have h1 : |c₀ * x ^ (k + 1) / (k + 1)| ≤ |c₀| * x ^ (k + 1) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < x ^ (k + 1)),
        abs_of_pos (by positivity : (0:ℝ) < k + 1)]
      apply div_le_self (by positivity)
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
    calc _ ≤ |c₀| * x ^ (k + 1) := h1
      _ ≤ |c₀| * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := mul_le_mul_of_nonneg_left hxe (abs_nonneg _)
      _ ≤ (I₀ / (2 * π) + |c₀|) * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ I₀ / (2 * π) := by positivity
          linarith
  · -- `x ≥ 1`
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hsumc : Summable fun n : ℕ => a n * (n : ℝ) ^ (-c) := hsum
    have hP := perron_riesz a ha ha0 hk hc hx hsumc
    -- integrability of the two pieces on the line `c`
    have hcont_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c →
        Continuous fun y : ℝ => (x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y)) := by
      intro σ h1 h2
      have hσ0 : 0 < σ := by linarith
      refine (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).mul
        ((continuous_Pk_line k hσ0).mul ?_)
      exact hF.continuousOn.comp_continuous (by fun_prop) (fun y => by simp [ln]; linarith)
    have hbound_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c → ∀ y : ℝ,
        ‖(x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y))‖ ≤ x ^ σ * (M / (1 + |y|) ^ 2) := by
      intro σ h1 h2 y
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
      have := hPF (ln σ y) (by simp [ln, h1]) (by simp [ln, h2])
      simp only [ln, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add] at this ⊢
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hint_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c →
        Integrable fun y : ℝ => (x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y)) := by
      intro σ h1 h2
      exact (hI.const_mul (x ^ σ)).mono' (hcont_line σ h1 h2).aestronglyMeasurable
        (Eventually.of_forall (hbound_line σ h1 h2))
    have hint_main : Integrable fun y : ℝ =>
        (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) := by
      have hP1 := integrable_Pk_line hk hc0
      have hmeas : AEStronglyMeasurable (fun y : ℝ =>
          (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1)))) := by
        refine Continuous.aestronglyMeasurable ?_
        refine (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).mul
          ((continuous_Pk_line k hc0).mul (continuous_const.div (by fun_prop) ?_))
        intro y h; have := congrArg re h; simp [ln] at this; linarith
      refine (hP1.norm.const_mul (x ^ c * (|c₀| / (c - 1)))).mono' hmeas
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_div, Complex.norm_real,
        Real.norm_eq_abs]
      have hre : (ln c y).re = c := by simp [ln]
      rw [hre]
      have hge : c - 1 ≤ ‖ln c y - 1‖ := by
        have := Complex.abs_re_le_norm (ln c y - 1)
        simp [ln] at this
        rw [abs_of_pos (by linarith)] at this; exact this
      have : |c₀| / ‖ln c y - 1‖ ≤ |c₀| / (c - 1) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hge
      have h0 : 0 ≤ ‖Pk k (ln c y)‖ := norm_nonneg _
      calc x ^ c * (‖Pk k (ln c y)‖ * (|c₀| / ‖ln c y - 1‖))
          ≤ x ^ c * (‖Pk k (ln c y)‖ * (|c₀| / (c - 1))) := by gcongr
        _ = x ^ c * (|c₀| / (c - 1)) * ‖Pk k (ln c y)‖ := by ring
    -- split the Perron integral
    have hsplit : ∫ y : ℝ, (x : ℂ) ^ ln c y * Pk k (ln c y) *
        LSeries (fun n => (a n : ℂ)) (ln c y) =
        (∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * F (ln c y))) +
        ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) := by
      rw [← integral_add (hint_line c hσ₁c le_rfl) hint_main]
      congr 1; funext y
      rw [hD (ln c y) (by simp [ln])]; ring
    -- the main term
    have hmain : ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) =
        (c₀ * x / (k + 1) : ℂ) * (2 * π * phi (k + 1) (1 / x)) := by
      have hinv := mellinInv_Pk (k := k + 1) (by omega) (σ := c - 1) (by linarith)
        (u := 1 / x) (by positivity)
      unfold mellinInv at hinv
      rw [Complex.real_smul] at hinv
      have h2π : (2 * π : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      have e : ∀ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) =
          (c₀ * x / (k + 1) : ℂ) * ((((1 / x : ℝ) : ℂ) ^ (-((c - 1 : ℝ) + y * I))) •
            Pk (k + 1) ((c - 1 : ℝ) + y * I)) := by
        intro y
        have hre : 1 < (ln c y).re := by simp [ln]; linarith
        have hdiv := Pk_div_sub_one k hre
        rw [cpow_div_neg zero_le_one hx, smul_eq_mul]
        have hl : ((c - 1 : ℝ) : ℂ) + y * I = ln c y - 1 := by simp [ln]; ring
        rw [hl, ofReal_one, one_cpow, one_mul]
        have hxs : (x : ℂ) ^ ln c y = x * (x : ℂ) ^ (ln c y - 1) := by
          rw [cpow_sub _ _ hx0, cpow_one]; field_simp
        have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have hs1 : ln c y - 1 ≠ 0 := by
          intro h; have := congrArg re h; simp [ln] at this; linarith
        have hdiv' : Pk (k + 1) (ln c y - 1) = ((k : ℂ) + 1) * (Pk k (ln c y) / (ln c y - 1)) := by
          rw [hdiv]; field_simp
        rw [hxs, hdiv']
        field_simp
      have hJ : ∫ y : ℝ, (((1 / x : ℝ) : ℂ) ^ (-((c - 1 : ℝ) + y * I))) •
          Pk (k + 1) ((c - 1 : ℝ) + y * I) = (2 * π : ℂ) * (phi (k + 1) (1 / x) : ℂ) := by
        rw [← hinv, ← mul_assoc]
        rw [show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]
      simp_rw [e]
      rw [integral_const_mul, hJ]
    -- the contour shift for the error term
    have hshift : ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * F (ln c y)) =
        ∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y)) := by
      have hdiff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s * (Pk k s * F s))
          {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ c} := by
        intro s hs
        have h0 : 0 < s.re := by linarith [hs.1]
        refine DifferentiableWithinAt.mul ?_ (DifferentiableWithinAt.mul ?_ ?_)
        · exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hx0)).differentiableWithinAt
        · exact ((differentiableOn_Pk k) s h0).mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
        · exact (hF s (by simp; linarith [hs.1])).mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
      have hB' : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c →
          ‖(x : ℂ) ^ s * (Pk k s * F s)‖ ≤ (x ^ c * M) / (1 + |s.im|) ^ 2 := by
        intro s h1 h2
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, mul_div_assoc]
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx1 h2) (hPF s h1 h2)
          (norm_nonneg _) (by positivity)
      exact integral_line_eq hσ₁c hdiff hB'
    have herr : ‖∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y))‖ ≤ x ^ σ₁ * I₀ := by
      calc _ ≤ ∫ y : ℝ, x ^ σ₁ * (M / (1 + |y|) ^ 2) :=
            norm_integral_le_of_norm_le (hI.const_mul _)
              (Eventually.of_forall (hbound_line σ₁ le_rfl hσ₁c))
        _ = x ^ σ₁ * I₀ := by rw [integral_const_mul]
    -- assemble
    rw [hsplit, hmain, hshift] at hP
    set E : ℂ := ∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y)) with hE
    set R : ℝ := ∑' n : ℕ, a n * phi k (n / x) with hR
    have hRc : (∑' n : ℕ, (a n : ℂ) * phi k (n / x)) = (R : ℂ) := by
      rw [hR, ofReal_tsum]; push_cast; rfl
    rw [hRc] at hP
    have hphi : phi (k + 1) (1 / x) = (1 - 1 / x) ^ (k + 1) :=
      phi_of_le ((div_le_one hx).2 hx1)
    -- `R - c₀ x (1-1/x)^{k+1}/(k+1) = E / (2π)`
    have hRe : |R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1)| ≤ x ^ σ₁ * I₀ / (2 * π) := by
      have h2π : (2 * π : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      have hEq : ((R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) : ℝ) : ℂ) = E / (2 * π) := by
        rw [hphi] at hP
        rw [eq_div_iff h2π]
        push_cast
        push_cast at hP
        linear_combination hP
      have : |R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1)| = ‖E‖ / (2 * π) := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, hEq, norm_div]
        congr 1
        rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [this]
      exact div_le_div_of_nonneg_right herr (by positivity)
    -- from `R` to `W`
    rw [W_eq_tsum a ha0 hk hx, ← hR]
    have h1x : 0 ≤ 1 - 1 / x := by rw [sub_nonneg]; exact (div_le_one hx).2 hx1
    have hbern : 1 - (1 - 1 / x) ^ (k + 1) ≤ (k + 1) * (1 / x) := by
      have := (pow_succ_sub_bounds k h1x (h := 1 / x) (by positivity)).2
      rw [sub_add_cancel, one_pow, one_pow, mul_one] at this
      linarith
    have hpow_le : (1 - 1 / x) ^ (k + 1) ≤ 1 := pow_le_one₀ h1x (by
      have : 0 < 1 / x := by positivity
      linarith)
    have hxk : x ^ k * x ^ σ₁ = x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx]; congr 1; ring
    have hxk2 : x ^ k ≤ x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hk1 : (0:ℝ) < k + 1 := by positivity
    -- the main-term discrepancy
    have hdisc : |c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1)| ≤ |c₀| := by
      have : c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1) =
          -(c₀ * x * (1 - (1 - 1 / x) ^ (k + 1)) / (k + 1)) := by ring
      rw [this, abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos hx, abs_of_pos hk1,
        abs_of_nonneg (show (0:ℝ) ≤ 1 - (1 - 1 / x) ^ (k + 1) by linarith)]
      rw [div_le_iff₀ hk1]
      have : x * (1 - (1 - 1 / x) ^ (k + 1)) ≤ k + 1 := by
        have := mul_le_mul_of_nonneg_left hbern hx.le
        rw [show x * ((k + 1) * (1 / x)) = k + 1 by field_simp] at this
        exact this
      calc |c₀| * x * (1 - (1 - 1 / x) ^ (k + 1)) = |c₀| * (x * (1 - (1 - 1 / x) ^ (k + 1))) := by
            ring
        _ ≤ |c₀| * (k + 1) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have hfin : |R - c₀ * x / (k + 1)| ≤ x ^ σ₁ * I₀ / (2 * π) + |c₀| := by
      have := abs_add_le (R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1))
        (c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1))
      rw [show R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) +
        (c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1)) =
        R - c₀ * x / (k + 1) by ring] at this
      linarith
    have heq : x ^ k * R - c₀ * x ^ (k + 1) / (k + 1) = x ^ k * (R - c₀ * x / (k + 1)) := by
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    have hxσ : 1 ≤ x ^ σ₁ := Real.one_le_rpow hx1 hσ₁.le
    calc x ^ k * |R - c₀ * x / (k + 1)| ≤ x ^ k * (x ^ σ₁ * I₀ / (2 * π) + |c₀|) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = (I₀ / (2 * π)) * (x ^ k * x ^ σ₁) + |c₀| * x ^ k := by ring
      _ ≤ (I₀ / (2 * π)) * (x ^ k * x ^ σ₁) + |c₀| * (x ^ k * x ^ σ₁) := by
          have : x ^ k ≤ x ^ k * x ^ σ₁ := le_mul_of_one_le_right (by positivity) hxσ
          have hI0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
          nlinarith [abs_nonneg c₀]
      _ = (I₀ / (2 * π) + |c₀|) * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by rw [← hxk]; ring

end RamanujanTau.RankinError
