/-
# A Landau-type theorem for logarithmic derivatives

**Landau's theorem** (1905): a Dirichlet series with nonnegative coefficients has a singularity
at the real point of its abscissa of convergence.  We prove the form needed here.

`landau_abscissa`: let `a ≥ 0`, let `b` have abscissa of absolute convergence `≤ θ`, let `L` be
entire with `L(σ) ≠ 0` for real `σ ∈ (θ, 1]`, `ε² = 1`, and suppose that on `Re s > 1`

  `ε · (−L'(s)/L(s)) = ∑ a(n) n^{−s} + ∑ b(n) n^{−s}`,  `L(s) ≠ 0`,

and that `∑ a(n)n^{−s}` converges absolutely for `Re s > 1`.  Then the abscissa of `a` is `≤ θ`.

Proof.  Suppose `x₀ := abscissa(a) > θ`.
1. `W = LSeries a + LSeries b` is holomorphic on `Ω = {Re s > x₀}` and `L' + εWL` vanishes on
   `Re s > 1`, hence on `Ω` (identity theorem).
2. `L(x₀) ≠ 0`, so on a small ball `B(x₀, r)` the function `Φ = −εL'/L − LSeries b` is
   holomorphic, and `Φ = LSeries a` on `B ∩ Ω`.
3. Taylor-expand `Φ` at `c = x₀ + r/4` and evaluate at `z = x₀ − r/4` (Mathlib's
   `Complex.hasSum_taylorSeries_on_ball`).  The `k`-th derivative of `LSeries a` at the real point
   `c` is `(−1)^k ∑ a(n)(log n)^k n^{−c}`, so every term of the double series
   `∑_k ∑_n (r/2)^k (log n)^k a(n) n^{−c} / k!` is `≥ 0`; Tonelli lets us sum over `k` first,
   giving `∑_n a(n) n^{−c} n^{r/2} = ∑_n a(n) n^{−z} < ∞`.  So the abscissa is `≤ z < x₀`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries Metric

lemma iterate_logMul_apply (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [logMul, ih]
    ring

/-- The real terms `(log n)^k a(n) n^{−c}`. -/
noncomputable def wR (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.log n ^ k * a n / (n : ℝ) ^ c

lemma term_iterate_eq (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    term (logMul^[k] fun n => (a n : ℂ)) (c : ℂ) n = (wR a c k n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [wR]
  rw [term_of_ne_zero hn, iterate_logMul_apply, wR, if_neg hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [show ((n : ℂ) ^ (c : ℂ)) = (((n : ℝ) ^ c : ℝ) : ℂ) by
      rw [Complex.ofReal_cpow hn0.le]; push_cast; rfl,
    show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
      rw [Complex.ofReal_log hn0.le]; push_cast; rfl]
  push_cast
  ring

lemma wR_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (c : ℝ) (k n : ℕ) : 0 ≤ wR a c k n := by
  unfold wR
  split_ifs with hn
  · exact le_rfl
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have := Real.log_nonneg hn1
    have := ha n
    positivity

set_option maxHeartbeats 1000000 in
theorem landau_abscissa {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {b : ℕ → ℂ} {θ : ℝ}
    (hb : abscissaOfAbsConv b ≤ θ) (ha1 : abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ 1)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L) (hLσ : ∀ σ : ℝ, θ < σ → σ ≤ 1 → L σ ≠ 0)
    {ε : ℂ} (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 1 < s.re → L s ≠ 0 ∧
      ε * (-deriv L s / L s) = LSeries (fun n => (a n : ℂ)) s + LSeries b s) :
    abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ θ := by
  set a' : ℕ → ℂ := fun n => (a n : ℂ)
  by_contra hcon
  push Not at hcon
  have hfin : abscissaOfAbsConv a' ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top 1) ha1
  have hbot : abscissaOfAbsConv a' ≠ ⊥ := ne_bot_of_gt hcon
  set x0 : ℝ := (abscissaOfAbsConv a').toReal
  have hx0 : abscissaOfAbsConv a' = x0 := (EReal.coe_toReal hfin hbot).symm
  have hθx : θ < x0 := by rw [hx0] at hcon; exact_mod_cast hcon
  have hx1 : x0 ≤ 1 := by rw [hx0] at ha1; exact_mod_cast ha1
  -- Step 1: the identity `L' + ε W L = 0` on `Ω`.
  set Ω : Set ℂ := {s | x0 < s.re}
  have hΩo : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_re
  have hdL : Differentiable ℂ (deriv L) := fun s =>
    (((hL.differentiableOn (s := Set.univ)).deriv isOpen_univ) s
      (Set.mem_univ s)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
  have haD : DifferentiableOn ℂ (LSeries a') Ω := (LSeries_differentiableOn a').mono
    fun s (hs : x0 < s.re) => by rw [Set.mem_setOf_eq, hx0]; exact_mod_cast hs
  have hbD : DifferentiableOn ℂ (LSeries b) {s : ℂ | θ < s.re} := (LSeries_differentiableOn b).mono
    fun s (hs : θ < s.re) => by
      rw [Set.mem_setOf_eq]; exact hb.trans_lt (by exact_mod_cast hs)
  set E : ℂ → ℂ := fun s => deriv L s + ε * (LSeries a' s + LSeries b s) * L s
  have hE : DifferentiableOn ℂ E Ω := by
    refine hdL.differentiableOn.add (((differentiableOn_const _).mul (haD.add (hbD.mono ?_))).mul
      hL.differentiableOn)
    intro s (hs : x0 < s.re); show θ < s.re; linarith
  have h2 : (2 : ℂ) ∈ Ω := by show x0 < (2 : ℂ).re; simp; linarith
  have hE2 : E =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with z (hz : 1 < z.re)
    obtain ⟨hL0, he⟩ := heq z hz
    simp only [E, Pi.zero_apply]
    rw [← he]
    field_simp
    linear_combination (-deriv L z) * hε
  have hEΩ : Set.EqOn E 0 Ω :=
    (hE.analyticOnNhd hΩo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt x0).isPreconnected h2 hE2
  -- Step 2: a ball around `x₀` free of zeros of `L`.
  have hLx0 : L x0 ≠ 0 := hLσ x0 hθx hx1
  obtain ⟨r1, hr1, hr1L⟩ := Metric.eventually_nhds_iff.mp
    (hL.continuous.continuousAt.eventually_ne hLx0)
  set r : ℝ := min r1 (x0 - θ)
  have hr : 0 < r := lt_min hr1 (by linarith)
  have hball_L : ∀ s ∈ ball (x0 : ℂ) r, L s ≠ 0 := fun s hs =>
    hr1L (lt_of_lt_of_le (mem_ball.mp hs) (min_le_left _ _))
  have hball_θ : ∀ s ∈ ball (x0 : ℂ) r, θ < s.re := by
    intro s hs
    have h1 : dist s x0 < x0 - θ := lt_of_lt_of_le (mem_ball.mp hs) (min_le_right _ _)
    have h2 : |s.re - x0| ≤ dist s x0 := by
      rw [Complex.dist_eq]
      have := Complex.abs_re_le_norm (s - x0)
      simpa using this
    have := neg_abs_le (s.re - x0)
    linarith
  set Φ : ℂ → ℂ := fun s => -ε * deriv L s / L s - LSeries b s
  have hΦD : DifferentiableOn ℂ Φ (ball (x0 : ℂ) r) := by
    refine ((((differentiableOn_const _).mul hdL.differentiableOn).div hL.differentiableOn
      hball_L)).sub (hbD.mono fun s hs => hball_θ s hs)
  have hΦa : ∀ s ∈ ball (x0 : ℂ) r ∩ Ω, Φ s = LSeries a' s := by
    rintro s ⟨hs1, hs2⟩
    have h0 := hEΩ hs2
    have hLs := hball_L s hs1
    simp only [E, Pi.zero_apply] at h0
    simp only [Φ]
    rw [sub_eq_iff_eq_add, div_eq_iff hLs]
    linear_combination (-ε) * h0 + (LSeries a' s + LSeries b s) * L s * hε
  -- Step 3: Taylor expansion at `c = x₀ + r/4`, evaluated at `z = x₀ − r/4`.
  set c : ℝ := x0 + r / 4
  have hcΩ : (c : ℂ) ∈ ball (x0 : ℂ) r ∩ Ω := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp only [c]; rw [show x0 + r / 4 - x0 = r / 4 by ring, abs_of_pos (by positivity)]
      linarith
    · show x0 < (c : ℂ).re; simp only [Complex.ofReal_re, c]; linarith
  have hev : Φ =ᶠ[𝓝 (c : ℂ)] LSeries a' := by
    filter_upwards [(isOpen_ball.inter hΩo).mem_nhds hcΩ] with s hs
    exact hΦa s hs
  have hsubball : ball (c : ℂ) (3 * r / 4) ⊆ ball (x0 : ℂ) r := by
    intro s hs
    rw [mem_ball] at hs ⊢
    have : dist (c : ℂ) (x0 : ℂ) = r / 4 := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp only [c]; rw [show x0 + r / 4 - x0 = r / 4 by ring, abs_of_pos (by positivity)]
    calc dist s x0 ≤ dist s c + dist (c : ℂ) x0 := dist_triangle _ _ _
      _ < 3 * r / 4 + r / 4 := by rw [this]; linarith
      _ = r := by ring
  set z : ℝ := x0 - r / 4
  have hz : (z : ℂ) ∈ ball (c : ℂ) (3 * r / 4) := by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [z, c]; rw [show x0 - r / 4 - (x0 + r / 4) = -(r / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball (hΦD.mono hsubball) hz
  have hcabs : abscissaOfAbsConv a' < (c : ℂ).re := by
    rw [hx0]; simp only [Complex.ofReal_re, c]; exact_mod_cast (by linarith : x0 < x0 + r / 4)
  -- the Taylor coefficients
  have hsumk : ∀ k : ℕ, Summable (fun n => wR a c k n) := by
    intro k
    have hs : LSeriesSummable (logMul^[k] a') (c : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by rwa [LSeries.absicssaOfAbsConv_logPowMul])
    have : Summable (fun n => (wR a c k n : ℂ)) := by
      refine hs.congr fun n => ?_
      exact term_iterate_eq a c k n
    exact Complex.summable_ofReal.mp this
  have hcoef : ∀ k : ℕ, (k.factorial : ℂ)⁻¹ • ((z : ℂ) - c) ^ k • iteratedDeriv k Φ c =
      ((((k.factorial : ℝ))⁻¹ * (r / 2) ^ k * ∑' n, wR a c k n : ℝ) : ℂ) := by
    intro k
    rw [hev.iteratedDeriv_eq k, LSeries_iteratedDeriv k hcabs]
    have hL : LSeries (logMul^[k] a') (c : ℂ) = ((∑' n, wR a c k n : ℝ) : ℂ) := by
      rw [LSeries, Complex.ofReal_tsum]
      exact tsum_congr fun n => term_iterate_eq a c k n
    rw [hL]
    have hzc : (z : ℂ) - c = ((-(r / 2) : ℝ) : ℂ) := by simp only [z, c]; push_cast; ring
    rw [hzc, smul_eq_mul, smul_eq_mul]
    have hp : ((-(r / 2) : ℝ) : ℂ) ^ k * (-1) ^ k = ((r / 2 : ℝ) : ℂ) ^ k := by
      rw [← mul_pow]; congr 1; push_cast; ring
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_pow]
    linear_combination ((k.factorial : ℂ))⁻¹ * ((∑' n, wR a c k n : ℝ) : ℂ) * hp
  simp_rw [hcoef] at hT
  have hTre := Complex.hasSum_re hT
  simp only [Complex.ofReal_re] at hTre
  -- Tonelli
  set U : ℕ × ℕ → ℝ := fun q => ((q.1.factorial : ℝ))⁻¹ * (r / 2) ^ q.1 * wR a c q.1 q.2
  have hU0 : 0 ≤ U := fun q => by
    have := wR_nonneg ha c q.1 q.2
    simp only [U, Pi.zero_apply]; positivity
  have hUs : Summable U := by
    refine (summable_prod_of_nonneg hU0).mpr ⟨fun k => ?_, ?_⟩
    · show Summable fun y => ((k.factorial : ℝ))⁻¹ * (r / 2) ^ k * wR a c k y
      exact (hsumk k).mul_left _
    · refine hTre.summable.congr fun k => ?_
      show _ = ∑' y, ((k.factorial : ℝ))⁻¹ * (r / 2) ^ k * wR a c k y
      rw [tsum_mul_left]
  have hUs' : Summable (U ∘ Prod.swap) := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hUs
  have hcol := hUs'.prod
  -- the inner sums over `k`
  have hinner : ∀ n : ℕ, ∑' k, (U ∘ Prod.swap) (n, k) =
      if n = 0 then 0 else a n / (n : ℝ) ^ c * Real.exp (r / 2 * Real.log n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [U, wR]
    rw [if_neg hn]
    have hE := NormedSpace.expSeries_div_hasSum_exp (r / 2 * Real.log n)
    rw [← Real.exp_eq_exp_ℝ] at hE
    have := (hE.mul_left (a n / (n : ℝ) ^ c)).tsum_eq
    rw [← this]
    refine tsum_congr fun k => ?_
    simp only [Function.comp_apply, Prod.swap, U, wR, if_neg hn]
    rw [mul_pow]
    field_simp
  have hfinal : LSeriesSummable a' (z : ℂ) := by
    refine Summable.of_norm ?_
    refine (hcol.congr fun n => hinner n).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg hn, norm_term_eq, if_neg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ha n), Complex.ofReal_re]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he : Real.exp (r / 2 * Real.log n) = (n : ℝ) ^ (r / 2) := by
      rw [Real.rpow_def_of_pos hn0, mul_comm]
    rw [he]
    simp only [z, c] at *
    rw [show x0 - r / 4 = (x0 + r / 4) - r / 2 by ring, Real.rpow_sub hn0]
    field_simp
  have := hfinal.abscissaOfAbsConv_le
  rw [hx0] at this
  simp only [Complex.ofReal_re, z] at this
  have : x0 ≤ x0 - r / 4 := by exact_mod_cast this
  linarith

end RamanujanTau.TauPNTUncond
