/-
# The exact dual expansion of the Riesz mean of a level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `k ≥ 12`, `a = coef f`, order `r ≥ 2` and `x > 0`:

    W_r(x) := ∑_{n≤x} aₙ (x−n)^r = i^{−k}(2π)^{−k} ∑ₙ aₙ n^{−k−r} J_r^{(σ_m)}(n x),

with `σ_m = (2k−3)/4 = (k−1)/2 − 1/4` (`dual_rep`). Proof:

1. Perron (`MeanSquare.perron_c`) on `Re s = k/2 + 1`;
2. contour shift of the *holomorphic* integrand `x^s P_r(s) L(f,s)` to `Re s = σ_m`
   (`Stirling.integral_line_eq_rpow`; the convexity bound of `HeckeConvexGeneral` gives
   `‖L(f,s)‖ ≪ (1+|t|)^{3/2}` on the strip, and `‖P_r(s)‖ ≪ (1+|t|)^{−r−1}`);
3. on `Re s = σ_m`, the functional equation gives `P_r(s)L(f,s) = i^{−k}(2π)^{−k}Q_r(s)L(f,k−s)`,
   and `L(f,k−s)` is an absolutely convergent Dirichlet series (`Re(k−s) = (k+1)/2 + 1/4`);
4. Fubini.

No residues occur: the cusp form's `L(f,s)` is entire and the integrand never leaves
`Re s > 0`.
-/
import RamanujanTau.TauPartialSumsSharp.Kernel
import RamanujanTau.MeanSquare.Shift
import RamanujanTau.HeckeConvexGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real MeasureTheory Set Filter Topology Finset LSeries ModularForm
open RamanujanTau.RankinError RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

/-- The Riesz sum `W_r(x) = ∑_{1≤n≤x} aₙ (x−n)^r`. -/
noncomputable def WC (a : ℕ → ℂ) (r : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) ^ r

/-- `x^r ∑' aₙ φ_r(n/x) = W_r(x)`. -/
lemma tsum_phi_eq (a : ℕ → ℂ) (ha0 : a 0 = 0) {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ r * ∑' n : ℕ, a n * (phi r (n / x) : ℂ) = WC a r x := by
  have hz : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊, a n * (phi r (n / x) : ℂ) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ha0]
    · have hlt : ⌊x⌋₊ < n := by
        simp only [Finset.mem_Icc, not_and, not_le] at hn; exact hn hpos
      have hxn : x < n := (Nat.floor_lt hx.le).1 hlt
      have : 1 < (n : ℝ) / x := by rw [one_lt_div hx]; exact hxn
      rw [phi_of_gt hr this]; simp
  rw [tsum_eq_sum hz, Finset.mul_sum, WC]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) ≤ x := by
    have := (Finset.mem_Icc.1 hn).2
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hx.le)
  have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx]; exact hnx
  rw [phi_of_le hle]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : ((x : ℂ) - n) = (x : ℂ) * (1 - (n : ℂ) / x) := by field_simp
  rw [e, mul_pow]
  push_cast
  ring

variable {k : ℕ}

/-- The strip bound `‖L(f,s)‖ ≤ K (1+|t|)^{3/2}` on `(2k−3)/4 ≤ Re s ≤ k/2+1`. -/
lemma fL_strip_bound' (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) :
    ∃ K : ℝ, ∀ s : ℂ, (2 * (k : ℝ) - 3) / 4 ≤ s.re → s.re ≤ (k : ℝ) / 2 + 1 →
      ‖fL f s‖ ≤ K * (1 + |s.im|) ^ ((3 : ℝ) / 2) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk (ε := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk1 (σ := ((k : ℝ) + 1) / 2 + 1 / 4) (by linarith)
  set c : ℝ := (k : ℝ) / 2 + 1 with hc
  refine ⟨2 * Real.exp 10 * C * c ^ ((3 : ℝ) / 2) + D, fun s h1 h2 => ?_⟩
  have ht1 : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hpow1 : 1 ≤ (1 + |s.im|) ^ ((3 : ℝ) / 2) := Real.one_le_rpow ht1 (by norm_num)
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  rcases le_or_gt s.re (((k : ℝ) + 1) / 2 + 1 / 4) with h3 | h3
  · have hL := fL_line f hk (ε := 1 / 4) (by norm_num) (by norm_num) hC (s := s)
      (by linarith) h3
    set θ : ℝ := ((k : ℝ) + 1) / 2 + 1 / 4 - s.re with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ1 : θ ≤ 3 / 2 := by rw [hθ]; linarith
    have hs1 : 1 ≤ ‖s / 2‖ := by
      rw [norm_div, Complex.norm_two, le_div_iff₀ (by norm_num)]
      have := Complex.abs_re_le_norm s
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    have hs2 : ‖s / 2‖ ≤ c * (1 + |s.im|) := by
      rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg s.im]
    have hp1 : ‖s / 2‖ ^ θ ≤ ‖s / 2‖ ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hs1 hθ1
    have hp2 : ‖s / 2‖ ^ ((3 : ℝ) / 2) ≤ (c * (1 + |s.im|)) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (norm_nonneg _) hs2 (by norm_num)
    have hp3 : (c * (1 + |s.im|)) ^ ((3 : ℝ) / 2) =
        c ^ ((3 : ℝ) / 2) * (1 + |s.im|) ^ ((3 : ℝ) / 2) :=
      Real.mul_rpow (by linarith) (by linarith)
    have hK0 : 0 ≤ 2 * Real.exp 10 * C := by positivity
    have hD' : 0 ≤ D * (1 + |s.im|) ^ ((3 : ℝ) / 2) := by positivity
    calc ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
      _ ≤ 2 * Real.exp 10 * C * (c ^ ((3 : ℝ) / 2) * (1 + |s.im|) ^ ((3 : ℝ) / 2)) := by
          gcongr; rw [← hp3]; exact hp1.trans hp2
      _ ≤ (2 * Real.exp 10 * C * c ^ ((3 : ℝ) / 2) + D) * (1 + |s.im|) ^ ((3 : ℝ) / 2) := by
          nlinarith
  · have h4 := hD s h3.le
    have h5 : D ≤ D * (1 + |s.im|) ^ ((3 : ℝ) / 2) := le_mul_of_one_le_right hD0 hpow1
    have h6 : 0 ≤ 2 * Real.exp 10 * C * c ^ ((3 : ℝ) / 2) * (1 + |s.im|) ^ ((3 : ℝ) / 2) := by
      positivity
    nlinarith

/-- `P_r(s) L(f,s) = i^{−k}(2π)^{−k} Q_r(s) L(f,k−s)` for `0 < Re s < k`. -/
lemma Pk_fL_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk1 : 1 ≤ k) (r : ℕ) {s : ℂ} (h0 : 0 < s.re)
    (hk : s.re < k) :
    Pk r s * fL f s = (I ^ k)⁻¹ * ((2 * π : ℂ) ^ k)⁻¹ * (Q k r s * fL f ((k : ℂ) - s)) := by
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n h; have := congrArg Complex.re h; simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hs' : ∀ n : ℕ, (k : ℂ) - s ≠ -n := by
    intro n h; have := congrArg Complex.re h; simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hFE := fL_functional_equation f hk1 hs hs'
  have hb : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h0
  have hGr : Complex.Gamma (s + r + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)])
  have hIk : (I : ℂ) ^ k ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hP : ∏ j ∈ range (r + 1), (s + j) = Complex.Gamma (s + r + 1) / Complex.Gamma s := by
    have e := RamanujanTau.RankinLandau.inv_Gamma_eq_prod s (r + 1)
    rw [show s + ((r + 1 : ℕ) : ℂ) = s + r + 1 by push_cast; ring] at e
    rw [eq_div_iff hG]
    have : (Complex.Gamma s)⁻¹ * Complex.Gamma s = 1 := inv_mul_cancel₀ hG
    calc (∏ j ∈ range (r + 1), (s + j)) * Complex.Gamma s =
        (∏ j ∈ range (r + 1), (s + j)) * (Complex.Gamma (s + r + 1))⁻¹ *
          Complex.Gamma (s + r + 1) * Complex.Gamma s := by field_simp
      _ = (Complex.Gamma s)⁻¹ * Complex.Gamma s * Complex.Gamma (s + r + 1) := by rw [← e]; ring
      _ = Complex.Gamma (s + r + 1) := by rw [this, one_mul]
  have hc1 : (2 * π : ℂ) ^ (-((k : ℂ) - s)) = (2 * π : ℂ) ^ s / (2 * π : ℂ) ^ k := by
    rw [show -((k : ℂ) - s) = s - k by ring, Complex.cpow_sub _ _ hb, Complex.cpow_natCast]
  have hc2 : (2 * π : ℂ) ^ (-s) = ((2 * π : ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
  have hc3 : ((2 * π : ℝ) : ℂ) ^ (2 * s) = (2 * π : ℂ) ^ s * (2 * π : ℂ) ^ s := by
    rw [show ((2 * π : ℝ) : ℂ) = (2 * π : ℂ) by push_cast; ring, show (2 : ℂ) * s = s + s by ring,
      Complex.cpow_add _ _ hb]
  have hbs : (2 * π : ℂ) ^ s ≠ 0 := two_pi_cpow_ne_zero s
  rw [hc1, hc2] at hFE
  have hL : Complex.Gamma s * fL f s = (I ^ k)⁻¹ * ((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ s /
      (2 * π : ℂ) ^ k) * Complex.Gamma ((k : ℂ) - s) * fL f ((k : ℂ) - s) := by
    calc Complex.Gamma s * fL f s = (I ^ k)⁻¹ * (2 * π : ℂ) ^ s *
          (I ^ k * (((2 * π : ℂ) ^ s)⁻¹ * Complex.Gamma s * fL f s)) := by field_simp
      _ = (I ^ k)⁻¹ * (2 * π : ℂ) ^ s * ((2 * π : ℂ) ^ s / (2 * π : ℂ) ^ k *
          Complex.Gamma ((k : ℂ) - s) * fL f ((k : ℂ) - s)) := by rw [hFE]
      _ = _ := by ring
  unfold Pk Q
  rw [hP, hc3]
  have hbk : (2 * π : ℂ) ^ k ≠ 0 := pow_ne_zero _ hb
  rw [show (r.factorial : ℂ) / (Complex.Gamma (s + r + 1) / Complex.Gamma s) * fL f s =
    (r.factorial : ℂ) * (Complex.Gamma s * fL f s) / Complex.Gamma (s + r + 1) by
      field_simp, hL]
  field_simp

/-- `∫ y^{σ+it} Q_r(σ+it) dt = 2π y^{−r} J_r^{(σ)}(y)`. -/
lemma integral_cpow_Q (r : ℕ) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Q k r (σ + t * I) =
      (2 * π : ℂ) * ((y : ℂ) ^ r)⁻¹ * Jc k r σ y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hyk : (y : ℂ) ^ r ≠ 0 := pow_ne_zero _ hy0
  have e : ∀ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I + r) * Q k r (σ + t * I) =
      (y : ℂ) ^ r * ((y : ℂ) ^ ((σ : ℂ) + t * I) * Q k r (σ + t * I)) := by
    intro t; rw [Complex.cpow_add _ _ hy0, Complex.cpow_natCast]; ring
  unfold Jc
  simp_rw [e]
  rw [integral_const_mul]
  have hπ : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  set Iv := ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Q k r (σ + t * I) with hIv
  push_cast
  field_simp

/-- **The exact dual expansion** of the Riesz mean of order `r ≥ 2`. -/
theorem dual_rep (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : 0 < x) :
    WC (coef f) r x = (I ^ k)⁻¹ * ((2 * π : ℂ) ^ k)⁻¹ *
      ∑' n : ℕ, coef f n / (n : ℂ) ^ (k + r) * Jc k r ((2 * (k : ℝ) - 3) / 4) (n * x) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set a := coef f with ha
  have ha0 : a 0 = 0 := coef_zero f
  set c : ℝ := (k : ℝ) / 2 + 1 with hc
  set σ : ℝ := (2 * (k : ℝ) - 3) / 4 with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσc : σ ≤ c := by rw [hσ, hc]; linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- Perron
  have hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c) := by
    refine (summable_norm_coef_div_rpow f hk1 (σ := c) (by rw [hc]; linarith)).congr
      fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hper := MeanSquare.perron_c a ha0 (k := r) hr1 (by rw [hc]; linarith) hx hsum
  -- the contour shift
  obtain ⟨K, hK⟩ := fL_strip_bound' f hk
  set g : ℂ → ℂ := fun s => (x : ℂ) ^ s * Pk r s * fL f s with hg
  set M : ℝ := (r.factorial : ℝ) * 2 ^ (r + 1) * |K| with hM
  set p : ℝ := (r : ℝ) - 1 / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hgB : ∀ s : ℂ, σ ≤ s.re → s.re ≤ c →
      ‖g s‖ ≤ ((x ^ σ + x ^ c) * M) * (1 + |s.im|) ^ (-p) := by
    intro s h1 h2
    have hP := norm_Pk_le r hσ0 h1
    have hmin : min σ 1 = 1 := min_eq_right (by rw [hσ]; linarith)
    rw [hmin, div_one] at hP
    have hFs : ‖fL f s‖ ≤ |K| * (1 + |s.im|) ^ ((3 : ℝ) / 2) :=
      (hK s h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    have ht : (0 : ℝ) < 1 + |s.im| := by positivity
    have hsplit : (1 + |s.im|) ^ ((3 : ℝ) / 2) / (1 + |s.im|) ^ (r + 1) = (1 + |s.im|) ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub ht, hp]; push_cast; ring_nf
    have hxp : x ^ s.re ≤ x ^ σ + x ^ c := by
      rcases le_or_gt 1 x with hx1 | hx1
      · have := Real.rpow_le_rpow_of_exponent_le hx1 h2
        linarith [Real.rpow_nonneg hx.le σ]
      · have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le h1
        linarith [Real.rpow_nonneg hx.le c]
    simp only [hg, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    calc x ^ s.re * ‖Pk r s‖ * ‖fL f s‖
        ≤ (x ^ σ + x ^ c) * ((r.factorial : ℝ) * 2 ^ (r + 1) / (1 + |s.im|) ^ (r + 1)) *
          (|K| * (1 + |s.im|) ^ ((3 : ℝ) / 2)) := by gcongr
      _ = (x ^ σ + x ^ c) * (M * ((1 + |s.im|) ^ ((3 : ℝ) / 2) / (1 + |s.im|) ^ (r + 1))) := by
          rw [hM]; ring
      _ = ((x ^ σ + x ^ c) * M) * (1 + |s.im|) ^ (-p) := by rw [hsplit]; ring
  have hgD : DifferentiableOn ℂ g {s : ℂ | σ ≤ s.re ∧ s.re ≤ c} := by
    intro s hs
    have hs0 : 0 < s.re := lt_of_lt_of_le hσ0 hs.1
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      (differentiableAt_id.const_cpow (Or.inl hxC))
    have h2 : DifferentiableAt ℂ (Pk r) s :=
      (differentiableOn_Pk r).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs0)
    exact ((h1.mul h2).mul (fL_entire f hk1 s)).differentiableWithinAt
  have hshift := Stirling.integral_line_eq_rpow hp1 hσc hgD hgB
  have hper' : (2 * π : ℂ) * ∑' n : ℕ, a n * (phi r (n / x) : ℂ) =
      ∫ y : ℝ, g (c + y * I) := by
    rw [hper]
    congr 1; funext y
    simp only [hg]
    rw [fL_eq_LSeries f hk1 (s := ln c y) (by simp [ln]; rw [hc]; linarith)]
  rw [hshift] at hper'
  -- the left line: functional equation and Fubini
  set s : ℝ → ℂ := fun t => (σ : ℂ) + t * I with hs
  have hsre : ∀ t, (s t).re = σ := fun t => by simp [hs]
  have hsim : ∀ t, (s t).im = t := fun t => by simp [hs]
  set τ₀ : ℝ := ((k : ℝ) + 1) / 2 + 1 / 4 with hτ₀
  have h1re : ∀ t, ((k : ℂ) - s t).re = τ₀ := fun t => by
    simp [hs]; rw [hσ, hτ₀]; ring
  set cst : ℂ := (I ^ k)⁻¹ * ((2 * π : ℂ) ^ k)⁻¹ with hcst
  have hLS : LSeriesSummable a (τ₀ : ℂ) := LSeriesSummable_coef f hk1 (by rw [ofReal_re, hτ₀]; linarith)
  have hQint : Integrable fun t : ℝ => Q k r (s t) := by
    have := integrable_jint k r (σ := σ) (by rw [hσ]; linarith) (by rw [hσ]; linarith)
      (by rw [hσ]; linarith) (y := 1) one_pos
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [jint, hs]
  set F : ℕ → ℝ → ℂ := fun n t =>
    (x : ℂ) ^ (s t) * (cst * Q k r (s t)) * LSeries.term a ((k : ℂ) - s t) n with hF
  have hterm_norm : ∀ n t, ‖LSeries.term a ((k : ℂ) - s t) n‖ = ‖LSeries.term a (τ₀ : ℂ) n‖ := by
    intro n t; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, h1re]; simp
  have hFnorm : ∀ n t, ‖F n t‖ = x ^ σ * ‖cst‖ * ‖LSeries.term a (τ₀ : ℂ) n‖ * ‖Q k r (s t)‖ := by
    intro n t
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul, hterm_norm, Complex.norm_cpow_eq_rpow_re_of_pos hx, hsre]
    ring
  have hcont_term : ∀ n, Continuous fun t => LSeries.term a ((k : ℂ) - s t) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]; exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      refine continuous_const.div (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
        (fun t => Complex.cpow_ne_zero_iff.2 (Or.inl hn0))
  have hcontQ : Continuous fun t : ℝ => Q k r (s t) :=
    continuous_Q_line k r (σ := σ) (by rw [hσ]; linarith)
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have hc' : Continuous (F n) := by
      simp only [hF]
      exact ((Continuous.const_cpow (by fun_prop) (Or.inl hxC)).mul
        (continuous_const.mul hcontQ)).mul (hcont_term n)
    refine (hQint.norm.const_mul (x ^ σ * ‖cst‖ * ‖LSeries.term a (τ₀ : ℂ) n‖)).mono'
      hc'.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [hFnorm]
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hFnorm, integral_const_mul]
    exact ((hLS.norm.mul_left (x ^ σ * ‖cst‖)).mul_right _)
  have key := integral_tsum_of_summable_integral_norm hFint hFsum
  have hgF : ∀ t, g (s t) = ∑' n, F n t := by
    intro t
    have h0 : 0 < (s t).re := by rw [hsre]; exact hσ0
    have hkk : (s t).re < k := by rw [hsre, hσ]; linarith
    simp only [hg]
    rw [mul_assoc, Pk_fL_eq f hk1 r h0 hkk,
      fL_eq_LSeries f hk1 (s := (k : ℂ) - s t) (by rw [h1re, hτ₀]; linarith)]
    simp only [hF, LSeries]
    rw [tsum_mul_left, hcst]; ring
  have hleft : ∫ y : ℝ, g (σ + y * I) = ∑' n, ∫ t, F n t := by
    simp_rw [show ∀ t : ℝ, (σ : ℂ) + t * I = s t from fun t => rfl, hgF]
    exact key.symm
  rw [hleft] at hper'
  -- each term
  have hterm : ∀ n, ∫ t, F n t = cst * ((2 * π : ℂ) * (a n / (n : ℂ) ^ k) *
      (((n * x : ℝ) : ℂ) ^ r)⁻¹ * Jc k r σ (n * x)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF, LSeries.term_zero, ha0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hnx : (0 : ℝ) < n * x := by positivity
      have e : ∀ t, F n t = cst * (a n / (n : ℂ) ^ k) *
          ((((n : ℝ) * x : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) * Q k r ((σ : ℂ) + t * I)) := by
        intro t
        simp only [hF, hs, LSeries.term_of_ne_zero hn]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn0.le hx.le,
          Complex.cpow_sub _ _ hnc, Complex.cpow_natCast]
        have h1 : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
        rw [h1]
        have h2 : (n : ℂ) ^ ((σ : ℂ) + t * I) ≠ 0 :=
          Complex.cpow_ne_zero_iff.2 (Or.inl hnc)
        have h3 : (n : ℂ) ^ k ≠ 0 := pow_ne_zero _ hnc
        field_simp
      simp_rw [e]
      rw [integral_const_mul, integral_cpow_Q r σ hnx]
      ring
  simp_rw [hterm] at hper'
  -- assemble
  have hW := tsum_phi_eq a ha0 hr1 hx
  rw [← hW]
  have h2π : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have hxr : (x : ℂ) ^ r ≠ 0 := pow_ne_zero _ hxC
  have hsum_eq : (x : ℂ) ^ r * ∑' n : ℕ, a n * (phi r (n / x) : ℂ) =
      (x : ℂ) ^ r * (((2 * π : ℂ))⁻¹ * ∑' n, cst * ((2 * π : ℂ) * (a n / (n : ℂ) ^ k) *
        (((n * x : ℝ) : ℂ) ^ r)⁻¹ * Jc k r σ (n * x))) := by
    rw [← hper']; field_simp
  rw [hsum_eq, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ha0]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have e : (((n * x : ℝ) : ℂ) ^ r) = (n : ℂ) ^ r * (x : ℂ) ^ r := by push_cast; ring
    rw [e, pow_add]
    have h3 : (n : ℂ) ^ k ≠ 0 := pow_ne_zero _ hnc
    have h4 : (n : ℂ) ^ r ≠ 0 := pow_ne_zero _ hnc
    field_simp

end RamanujanTau.TauPartialSumsSharp
