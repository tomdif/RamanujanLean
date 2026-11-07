/-
# The first Riesz mean of a Dirichlet series with an entire continuation

`riesz_one_bound`: let `a : ℕ → ℂ`, `a 0 = 0`, with `∑ ‖aₙ‖ n^{-c} < ∞`, and let `F` be entire
with `F = L(a, ·)` on `Re s = c`. If `‖F(s)‖ ≤ K (1+|Im s|)^{2-p}` (`p > 1`) on the strip
`σ₁ ≤ Re s ≤ c` (`0 < σ₁`), then

    ‖∑ₙ aₙ (1 − n/x)₊‖ ≤ K' x^{σ₁}        (x ≥ 1).

Proof: Perron for Riesz means with complex coefficients (`MeanSquare.perron_c`, order 1),
then a contour shift of the *holomorphic* integrand `x^s P₁(s) F(s)` from `Re s = c` to
`Re s = σ₁` (`Stirling.integral_line_eq_rpow`; no poles since `σ₁ > 0`), then the trivial
bound on the new line.

`sum_F1_eq`: the tsum is the finite sum `x⁻¹ ∑_{n ≤ x} aₙ (x − n)`.
-/
import RamanujanTau.MeanSquare.Shift

set_option autoImplicit false

namespace RamanujanTau.TauPartialSums

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError

/-- **Riesz mean of order one, via a contour shift.** -/
theorem riesz_one_bound (a : ℕ → ℂ) (ha0 : a 0 = 0) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c σ₁ p K : ℝ} (hσ₁ : 0 < σ₁) (hσc : σ₁ ≤ c) (hp : 1 < p)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c))
    (hD : ∀ s : ℂ, s.re = c → LSeries a s = F s)
    (hFB : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖F s‖ ≤ K * (1 + |s.im|) ^ (2 - p)) :
    ∃ K' : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑' n : ℕ, a n * (phi 1 (n / x) : ℂ)‖ ≤ K' * x ^ σ₁ := by
  have hc : 0 < c := lt_of_lt_of_le hσ₁ hσc
  set m : ℝ := min σ₁ 1 with hm
  set M : ℝ := (2 / m) ^ 2 * |K| with hM
  have hM0 : 0 ≤ M := by positivity
  have hI : Integrable fun y : ℝ => M * (1 + |y|) ^ (-p) := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p)
      (by simpa using hp)).const_mul M
    simpa [Real.norm_eq_abs] using this
  set I₀ : ℝ := ∫ y : ℝ, M * (1 + |y|) ^ (-p) with hI₀
  refine ⟨I₀ / (2 * π), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  set g : ℂ → ℂ := fun s => (x : ℂ) ^ s * Pk 1 s * F s with hg
  -- pointwise bound on the strip
  have hgB : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c →
      ‖g s‖ ≤ x ^ s.re * (M * (1 + |s.im|) ^ (-p)) := by
    intro s h1 h2
    have hP := norm_Pk_le 1 hσ₁ h1
    have hFs : ‖F s‖ ≤ |K| * (1 + |s.im|) ^ (2 - p) :=
      (hFB s h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    have ht : (0:ℝ) < 1 + |s.im| := by positivity
    have hsplit : (1 + |s.im|) ^ (2 - p) / (1 + |s.im|) ^ (1 + 1) = (1 + |s.im|) ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub ht]; push_cast; ring_nf
    simp only [hg, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hf1] at hP
    calc x ^ s.re * ‖Pk 1 s‖ * ‖F s‖
        ≤ x ^ s.re * (1 * (2 / m) ^ (1 + 1) / (1 + |s.im|) ^ (1 + 1)) *
          (|K| * (1 + |s.im|) ^ (2 - p)) := by gcongr
      _ = x ^ s.re * (M * ((1 + |s.im|) ^ (2 - p) / (1 + |s.im|) ^ (1 + 1))) := by
          rw [hM]; ring
      _ = x ^ s.re * (M * (1 + |s.im|) ^ (-p)) := by rw [hsplit]
  have hgB' : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c →
      ‖g s‖ ≤ (x ^ c * M) * (1 + |s.im|) ^ (-p) := by
    intro s h1 h2
    refine (hgB s h1 h2).trans ?_
    have : x ^ s.re ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx h2
    calc x ^ s.re * (M * (1 + |s.im|) ^ (-p)) ≤ x ^ c * (M * (1 + |s.im|) ^ (-p)) := by
          gcongr
      _ = _ := by ring
  have hgD : DifferentiableOn ℂ g {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ c} := by
    intro s hs
    have hs0 : 0 < s.re := lt_of_lt_of_le hσ₁ hs.1
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      (differentiableAt_id.const_cpow (Or.inl hxC))
    have h2 : DifferentiableAt ℂ (Pk 1) s :=
      (differentiableOn_Pk 1).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs0)
    exact ((h1.mul h2).mul (hF s)).differentiableWithinAt
  have hshift := Stirling.integral_line_eq_rpow hp hσc hgD hgB'
  -- Perron
  have hsum' : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c) := hsum
  have hper := MeanSquare.perron_c a ha0 (k := 1) le_rfl hc hx0 hsum'
  have hper' : (2 * π : ℂ) * ∑' n : ℕ, a n * (phi 1 (n / x) : ℂ) =
      ∫ y : ℝ, g (c + y * I) := by
    rw [hper]
    congr 1; funext y
    simp only [hg]
    rw [hD (ln c y) (by simp [ln])]
  rw [hshift] at hper'
  -- bound the left integral
  have hint : ‖∫ y : ℝ, g (σ₁ + y * I)‖ ≤ ∫ y : ℝ, x ^ σ₁ * (M * (1 + |y|) ^ (-p)) := by
    refine norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall fun y => ?_)
    have := hgB (σ₁ + y * I) (by simp) (by simp [hσc])
    simpa using this
  rw [integral_const_mul] at hint
  have h2π : 0 < 2 * π := by positivity
  have hn : ‖(2 * π : ℂ) * ∑' n : ℕ, a n * (phi 1 (n / x) : ℂ)‖ =
      2 * π * ‖∑' n : ℕ, a n * (phi 1 (n / x) : ℂ)‖ := by
    rw [norm_mul]; congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h2π]
  rw [← hper', hn] at hint
  rw [div_mul_eq_mul_div, le_div_iff₀ h2π]
  linarith

/-- The first Riesz sum `F₁(x) = ∑_{1 ≤ n ≤ x} aₙ (x − n)`. -/
noncomputable def F1 (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n)

/-- `x · ∑' aₙ (1 − n/x)₊ = F₁(x)`. -/
lemma tsum_phi_eq (a : ℕ → ℂ) (ha0 : a 0 = 0) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * ∑' n : ℕ, a n * (phi 1 (n / x) : ℂ) = F1 a x := by
  have hz : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊, a n * (phi 1 (n / x) : ℂ) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ha0]
    · have hlt : ⌊x⌋₊ < n := by
        simp only [Finset.mem_Icc, not_and, not_le] at hn; exact hn hpos
      have hxn : x < n := (Nat.floor_lt hx.le).1 hlt
      have : 1 < (n : ℝ) / x := by rw [one_lt_div hx]; exact hxn
      rw [phi_of_gt le_rfl this]; simp
  rw [tsum_eq_sum hz, Finset.mul_sum, F1]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) ≤ x := by
    have := (Finset.mem_Icc.1 hn).2
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hx.le)
  have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx]; exact hnx
  rw [phi_of_le hle, pow_one]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

/-- **Riesz sum bound**: `‖F₁(x)‖ ≤ K' x^{1+σ₁}` for `x ≥ 1`. -/
theorem F1_bound (a : ℕ → ℂ) (ha0 : a 0 = 0) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c σ₁ p K : ℝ} (hσ₁ : 0 < σ₁) (hσc : σ₁ ≤ c) (hp : 1 < p)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c))
    (hD : ∀ s : ℂ, s.re = c → LSeries a s = F s)
    (hFB : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖F s‖ ≤ K * (1 + |s.im|) ^ (2 - p)) :
    ∃ K' : ℝ, ∀ x : ℝ, 1 ≤ x → ‖F1 a x‖ ≤ K' * x ^ (1 + σ₁) := by
  obtain ⟨K', hK'⟩ := riesz_one_bound a ha0 hF hσ₁ hσc hp hsum hD hFB
  refine ⟨K', fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [← tsum_phi_eq a ha0 hx0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0, Real.rpow_add hx0, Real.rpow_one]
  have := hK' x hx
  calc x * ‖∑' n : ℕ, a n * (phi 1 (n / x) : ℂ)‖ ≤ x * (K' * x ^ σ₁) := by gcongr
    _ = K' * (x * x ^ σ₁) := by ring

end RamanujanTau.TauPartialSums
