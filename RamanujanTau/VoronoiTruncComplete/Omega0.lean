/-
# Exact `Ω±` at the first nonzero frequency

`VoronoiTruncGeneral/Omega.lean` runs Ingham's positive-kernel argument with the kernel
`1 ± cos θ₁(x)` and therefore needs `a(1) = 1`.  Here the kernel is `ρ(x) = 1 ± cos θ_{n₀}(x)`,
where `n₀` is the first index with `a(n₀) ≠ 0`.

The only new estimate is `term_int0`: for `n ≥ n₀`,

    ∫_X^{2X} cos θₙ · (1 + s cos θ_{n₀}) = s [n = n₀] X/2 + O((2 + √(n₀+1) + √n₀) √(2X)/π).

Because `a(n) = 0` for `n < n₀`, only frequencies `n > n₀` occur off the diagonal, and for them
`√n − √n₀ ≥ √(n₀+1) − √n₀ = 1/(√(n₀+1) + √n₀)`.  This is a constant that does not depend on `X`
or on the truncation `N`, so the off-diagonal terms are again `O(√X)` each.  The `τ` proof
(frequency `1`) had the same structure with `√2 − 1 ≥ 2/5`.

`omega_core0`: if `bco m a n₀ = 1` (i.e. `a(n₀) n₀^{−(m+1/4)} = 1`) then for `c < 1/(2π√2)`,
`s = ±1` and all large `X` some `x ∈ [X, 2X]` has `s S(x) > c x^{m−1/4}`.
`omega_pm_first`: the rescaled statement with constant `c < |a(n₀)| n₀^{−(m+1/4)}/(2π√2)`.
-/
import RamanujanTau.VoronoiTruncGeneral.Omega

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncComplete

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.VoronoiTruncGeneral

variable {m : ℕ} {a : ℕ → ℝ}

/-- The positive kernel `ρ(x) = 1 + s cos θ_{n₀}(x)`. -/
noncomputable def rho0 (n₀ : ℕ) (s x : ℝ) : ℝ := 1 + s * Real.cos (th n₀ x)

lemma rho0_nonneg (n₀ : ℕ) {s : ℝ} (hs : s = 1 ∨ s = -1) (x : ℝ) : 0 ≤ rho0 n₀ s x := by
  unfold rho0
  rcases hs with rfl | rfl
  · linarith [Real.neg_one_le_cos (th n₀ x)]
  · linarith [Real.cos_le_one (th n₀ x)]

lemma rho0_le_two (n₀ : ℕ) {s : ℝ} (hs : s = 1 ∨ s = -1) (x : ℝ) : rho0 n₀ s x ≤ 2 := by
  unfold rho0
  rcases hs with rfl | rfl
  · linarith [Real.cos_le_one (th n₀ x)]
  · linarith [Real.neg_one_le_cos (th n₀ x)]

lemma continuous_rho0 (n₀ : ℕ) (s : ℝ) : Continuous (rho0 n₀ s) := by
  unfold rho0
  exact continuous_const.add (continuous_const.mul (Real.continuous_cos.comp (continuous_th n₀)))

/-- `1/(√n − √n₀) ≤ √(n₀+1) + √n₀` for `n > n₀`. -/
lemma inv_gap_le {n₀ n : ℕ} (h : n₀ < n) :
    0 < √(n : ℝ) - √(n₀ : ℝ) ∧ 1 / (√(n : ℝ) - √(n₀ : ℝ)) ≤ √((n₀ : ℝ) + 1) + √(n₀ : ℝ) := by
  have hn : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast h
  have h1 : √((n₀ : ℝ) + 1) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn
  have h2 : √(n₀ : ℝ) < √((n₀ : ℝ) + 1) := Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (by linarith)
  have hq1 : √((n₀ : ℝ) + 1) ^ 2 = (n₀ : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hq0 : √(n₀ : ℝ) ^ 2 = (n₀ : ℝ) := Real.sq_sqrt (by positivity)
  have hpos : 0 < √(n : ℝ) - √(n₀ : ℝ) := by linarith
  refine ⟨hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  have h0 : 0 ≤ √(n₀ : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- `∫_X^{2X} cos θₙ · ρ = s [n=n₀] X/2 + O(√X)` for `n ≥ n₀`. -/
lemma term_int0 {n₀ n : ℕ} (h0 : 1 ≤ n₀) (hn : n₀ ≤ n) {X : ℝ} (hX : 0 < X) {s : ℝ}
    (hs : s = 1 ∨ s = -1) :
    |(∫ x in X..2 * X, Real.cos (th n x) * rho0 n₀ s x) - (if n = n₀ then s * X / 2 else 0)| ≤
      (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π := by
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hsn0 : 1 ≤ √(n₀ : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]; simpa using (Nat.one_le_cast.2 h0)
  have hsn : 1 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    simpa using (Nat.one_le_cast.2 (le_trans h0 hn))
  have hXX : X ≤ 2 * X := by linarith
  have e : ∀ x, Real.cos (th n x) * rho0 n₀ s x = Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) +
      s / 2 * Real.cos (4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0) +
      s / 2 * Real.cos (4 * π * (√(n : ℝ) + √(n₀ : ℝ)) * √x + (-(π / 2))) := by
    intro x
    unfold rho0
    rw [mul_add, mul_one, mul_left_comm, cos_mul_cos']
    have e1 : th n x - th n₀ x = 4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0 := by unfold th; ring
    have e2 : th n x + th n₀ x = 4 * π * (√(n : ℝ) + √(n₀ : ℝ)) * √x + (-(π / 2)) := by
      unfold th; ring
    have e3 : th n x = 4 * π * √(n : ℝ) * √x + (-(π / 4)) := by unfold th; ring
    rw [e1, e2, e3]; ring
  have c1 : Continuous fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) := by fun_prop
  have c2 : Continuous fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0) := by
    fun_prop
  have c3 : Continuous fun x =>
      s / 2 * Real.cos (4 * π * (√(n : ℝ) + √(n₀ : ℝ)) * √x + (-(π / 2))) := by fun_prop
  simp_rw [e]
  rw [intervalIntegral.integral_add
      (f := fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))) +
        s / 2 * Real.cos (4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0))
      (g := fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) + √(n₀ : ℝ)) * √x + (-(π / 2))))
      ((c1.add c2).intervalIntegrable _ _) (c3.intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun x => Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4))))
      (g := fun x => s / 2 * Real.cos (4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0))
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  set A := ∫ x in X..2 * X, Real.cos (4 * π * √(n : ℝ) * √x + (-(π / 4)))
  set Bm := ∫ x in X..2 * X, Real.cos (4 * π * (√(n : ℝ) - √(n₀ : ℝ)) * √x + 0)
  set Bp := ∫ x in X..2 * X, Real.cos (4 * π * (√(n : ℝ) + √(n₀ : ℝ)) * √x + (-(π / 2)))
  set Q := √(2 * X) / π
  have hQ : 0 ≤ Q := by positivity
  have hR : (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π =
      (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * Q := by simp only [Q]; ring
  rw [hR]
  have hS0 : 0 ≤ √((n₀ : ℝ) + 1) := Real.sqrt_nonneg _
  have iA : |A| ≤ Q := by
    have i1 := abs_integral_cos_le (δ := √(n : ℝ)) (φ := -(π / 4)) (by positivity) hX hXX
    rw [abs_of_pos (by positivity : (0 : ℝ) < √(n : ℝ))] at i1
    refine i1.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith [Real.pi_pos]
  have iBp : |Bp| ≤ Q / 2 := by
    have i3 := abs_integral_cos_le (δ := √(n : ℝ) + √(n₀ : ℝ)) (φ := -(π / 2)) (by positivity) hX hXX
    rw [abs_of_pos (by positivity : (0 : ℝ) < √(n : ℝ) + √(n₀ : ℝ))] at i3
    refine i3.trans ?_
    rw [show Q / 2 = √(2 * X) / (2 * π) by simp only [Q]; ring]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith [Real.pi_pos]
  have hsA : |s / 2 * Bp| ≤ Q / 4 := by
    rw [abs_mul, abs_div, hs1, abs_two]; linarith
  by_cases h1 : n = n₀
  · subst h1
    rw [if_pos rfl]
    have hBm : Bm = X := by
      simp only [Bm, sub_self, mul_zero, zero_mul, add_zero, Real.cos_zero,
        intervalIntegral.integral_const, smul_eq_mul, mul_one]
      ring
    rw [hBm]
    have e2 : A + s / 2 * X + s / 2 * Bp - s * X / 2 = A + s / 2 * Bp := by ring
    rw [e2]
    calc |A + s / 2 * Bp| ≤ |A| + |s / 2 * Bp| := abs_add_le _ _
      _ ≤ Q + Q / 4 := add_le_add iA hsA
      _ ≤ (2 + √((n : ℝ) + 1) + √(n : ℝ)) * Q := by nlinarith
  · rw [if_neg h1, sub_zero]
    have hlt : n₀ < n := lt_of_le_of_ne hn (Ne.symm h1)
    obtain ⟨hδ, hinv⟩ := inv_gap_le hlt
    set G := √((n₀ : ℝ) + 1) + √(n₀ : ℝ)
    have iBm : |Bm| ≤ G * Q := by
      have i2 := abs_integral_cos_le (δ := √(n : ℝ) - √(n₀ : ℝ)) (φ := 0) hδ.ne' hX hXX
      rw [abs_of_pos hδ] at i2
      refine i2.trans ?_
      have : √(2 * X) / (π * (√(n : ℝ) - √(n₀ : ℝ))) = Q * (1 / (√(n : ℝ) - √(n₀ : ℝ))) := by
        simp only [Q]; field_simp
      rw [this, mul_comm G]
      exact mul_le_mul_of_nonneg_left hinv hQ
    have hsB : |s / 2 * Bm| ≤ G / 2 * Q := by
      rw [abs_mul, abs_div, hs1, abs_two]; linarith
    have hG0 : 0 ≤ G := by positivity
    calc |A + s / 2 * Bm + s / 2 * Bp| ≤ |A| + |s / 2 * Bm| + |s / 2 * Bp| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Q + G / 2 * Q + Q / 4 := add_le_add (add_le_add iA hsB) hsA
      _ ≤ (2 + G) * Q := by nlinarith
      _ = (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * Q := by simp only [G]; ring

/-- The main-term integral against the kernel at frequency `n₀`. -/
lemma main_int0 {n₀ : ℕ} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0) (h1 : bco m a n₀ = 1) {X : ℝ}
    (hX : 1 ≤ X) (N : ℕ) (hN : n₀ ≤ N) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    |(∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho0 n₀ s x) -
        s * X / 2| ≤
      (∑ n ∈ Finset.Icc 1 N, |bco m a n|) * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π) := by
  have hX0 : 0 < X := by linarith
  have hc : ∀ n : ℕ, Continuous fun x => bco m a n * Real.cos (th n x) * rho0 n₀ s x := fun n =>
    (continuous_const.mul (Real.continuous_cos.comp (continuous_th n))).mul (continuous_rho0 n₀ s)
  have e1 : ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho0 n₀ s x =
      ∑ n ∈ Finset.Icc 1 N, bco m a n * ∫ x in X..2 * X, Real.cos (th n x) * rho0 n₀ s x := by
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum
      (f := fun n x => bco m a n * Real.cos (th n x) * rho0 n₀ s x)
      (fun n _ => (hc n).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show bco m a n * Real.cos (th n x) * rho0 n₀ s x = bco m a n * (Real.cos (th n x) * rho0 n₀ s x)
    ring
  have e2 : s * X / 2 = ∑ n ∈ Finset.Icc 1 N, bco m a n * (if n = n₀ then s * X / 2 else 0) := by
    rw [Finset.sum_eq_single n₀ (fun n _ hn => by rw [if_neg hn, mul_zero])
      (fun h => absurd (Finset.mem_Icc.2 ⟨h0, hN⟩) h), if_pos rfl, h1, one_mul]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [abs_mul]
  rcases lt_or_ge n n₀ with hlt | hge
  · have : bco m a n = 0 := by simp [bco, hz n hlt]
    rw [this, abs_zero, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (term_int0 h0 hge hX0 hs) (abs_nonneg _)

set_option maxHeartbeats 1000000 in
/-- **Core of the `Ω±` argument.** -/
theorem omega_core0 (hd : VData m a) {n₀ : ℕ} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0)
    (hb1 : bco m a n₀ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / (2 * π * √2)) :
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
  have hr1 : Tendsto (fun X : ℝ => (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 8)).const_mul ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * St7 / π ^ 2)
  have ev2 := (tendsto_order.1 hr1).2 (g / 4) (by positivity)
  have hr2 : Tendsto (fun X : ℝ => c * √2 / π * X ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (c * √2 / π)
  have ev3 := (tendsto_order.1 hr2).2 (g / 4) (by positivity)
  have ev4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop (n₀ : ℝ)
  filter_upwards [ev1, ev2, ev3, ev4, eventually_ge_atTop 1] with X h1 h2 h3 h4 hX
  by_contra hcon
  push Not at hcon
  have hX0 : 0 < X := by linarith
  set N := ⌊X ^ (1 / 4 : ℝ)⌋₊
  have hN : n₀ ≤ N := Nat.le_floor h4
  set w : ℝ → ℝ := fun x => x ^ (-((m : ℝ) - 1 / 4)) with hw
  have hwm : Measurable w := measurable_id.pow_const _
  have hwle : ∀ x, X ≤ x → w x ≤ 1 := fun x hx =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hw0 : ∀ x, X ≤ x → 0 ≤ w x := fun x hx => Real.rpow_nonneg (by linarith) _
  have hwx : ∀ x, X ≤ x → x ^ ((m : ℝ) - 1 / 4) * w x = 1 := fun x hx => by
    show x ^ ((m : ℝ) - 1 / 4) * x ^ (-((m : ℝ) - 1 / 4)) = 1
    rw [← Real.rpow_add (by linarith)]; simp
  have hρm : Measurable (rho0 n₀ s) := (continuous_rho0 n₀ s).measurable
  have hρ0 := rho0_nonneg n₀ hs
  have hρ2 := rho0_le_two n₀ hs
  -- integrability
  set K := ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊, |a n|
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set fS : ℝ → ℝ := fun x => s * Sre a x * w x * rho0 n₀ s x
  set fV : ℝ → ℝ := fun x => s * Vth m a N x * w x * rho0 n₀ s x
  have hfS : IntegrableOn fS (Ioc X (2 * X)) := by
    refine integrableOn_bounded_meas (((measurable_const.mul measurable_Sre).mul hwm).mul hρm)
      (K := K * 2) fun x hx => ?_
    show |s * Sre a x * w x * rho0 n₀ s x| ≤ K * 2
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
    ((continuousOn_const.mul (continuous_Vth hd.one_le N).continuousOn).mul hwc).mul (continuous_rho0 n₀ s).continuousOn
  have hfV : IntegrableOn fV (Ioc X (2 * X)) :=
    (hfVc.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  -- upper bound from the one-sided hypothesis
  have hcos1 : |∫ x in X..2 * X, Real.cos (th n₀ x)| ≤ √(2 * X) / π := by
    have hs0 : (1 : ℝ) ≤ √(n₀ : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast h0)
    have := abs_integral_cos_le (δ := √(n₀ : ℝ)) (φ := -(π / 4)) (by positivity) hX0
      (by linarith : X ≤ 2 * X)
    rw [abs_of_pos (by positivity : (0 : ℝ) < √(n₀ : ℝ))] at this
    have e : ∀ x, th n₀ x = 4 * π * √(n₀ : ℝ) * √x + -(π / 4) := by intro x; unfold th; ring
    simp_rw [e]
    refine this.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith [Real.pi_pos]
  have hρint : ∫ x in Ioc X (2 * X), rho0 n₀ s x ≤ X + √(2 * X) / π := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    unfold rho0
    rw [intervalIntegral.integral_add (f := fun _ => (1 : ℝ)) (g := fun x => s * Real.cos (th n₀ x))
      intervalIntegrable_const
      ((continuous_const.mul (Real.continuous_cos.comp (continuous_th n₀))).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, mul_one]
    have : s * ∫ x in X..2 * X, Real.cos (th n₀ x) ≤ √(2 * X) / π := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, hs1, one_mul]; exact hcos1
    linarith
  have hupper : ∫ x in Ioc X (2 * X), fS x ≤ c * (X + √(2 * X) / π) := by
    have hcρ : IntegrableOn (fun x => c * rho0 n₀ s x) (Ioc X (2 * X)) :=
      (((continuous_rho0 n₀ s).const_mul c).continuousOn.integrableOn_Icc (μ := volume)).mono_set
        Ioc_subset_Icc_self
    calc ∫ x in Ioc X (2 * X), fS x ≤ ∫ x in Ioc X (2 * X), c * rho0 n₀ s x := by
          refine setIntegral_mono_on hfS hcρ measurableSet_Ioc fun x hx => ?_
          have h := hcon x ⟨hx.1.le, hx.2⟩
          simp only [fS]
          have hwr : 0 ≤ w x * rho0 n₀ s x := mul_nonneg (hw0 x hx.1.le) (hρ0 x)
          calc s * Sre a x * w x * rho0 n₀ s x = (s * Sre a x) * (w x * rho0 n₀ s x) := by ring
            _ ≤ (c * x ^ ((m : ℝ) - 1 / 4)) * (w x * rho0 n₀ s x) := mul_le_mul_of_nonneg_right h hwr
            _ = c * rho0 n₀ s x * (x ^ ((m : ℝ) - 1 / 4) * w x) := by ring
            _ = c * rho0 n₀ s x := by rw [hwx x hx.1.le, mul_one]
      _ = c * ∫ x in Ioc X (2 * X), rho0 n₀ s x := integral_const_mul _ _
      _ ≤ c * (X + √(2 * X) / π) := mul_le_mul_of_nonneg_left hρint hc0
  -- the main-term part
  set E := (∑ n ∈ Finset.Icc 1 N, |bco m a n|) * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π)
  have hE := main_int0 (m := m) h0 hz hb1 hX N hN hs
  have hVint : ∫ x in Ioc X (2 * X), fV x = s * (1 / (π * √2)) *
      ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho0 n₀ s x := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [fV]
    have := Vth_mul_rpow (m := m) (a := a) N (show 0 < x by linarith [hx.1])
    calc s * Vth m a N x * w x * rho0 n₀ s x = s * (Vth m a N x * x ^ (-((m : ℝ) - 1 / 4))) * rho0 n₀ s x := by
          simp only [hw]; ring
      _ = _ := by rw [this]; ring
  have hVlow : (1 / (π * √2)) * (X / 2 - E) ≤ ∫ x in Ioc X (2 * X), fV x := by
    rw [hVint]
    set J := ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)) * rho0 n₀ s x
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
      have e : fS x - fV x = s * (Sre a x - Vth m a N x) * w x * rho0 n₀ s x := by simp only [fS, fV]; ring
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
      calc |Sre a x - Vth m a N x| * w x * rho0 n₀ s x ≤ aa * 2 := by
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
    have hEb : E ≤ X ^ (1 / 8 : ℝ) * St7 * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π) :=
      mul_le_mul_of_nonneg_right hsb (by positivity)
    have h2' : (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ) * X ≤ g / 4 * X := by
      exact mul_le_mul_of_nonneg_right h2.le hX0.le
    have e : X ^ (1 / 8 : ℝ) * St7 * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π) / (π * √2) =
        (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * St7 / π ^ 2 * X ^ (-(3 / 8) : ℝ) * X := by
      have hA : X ^ (1 / 8 : ℝ) * √X = X ^ (5 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]; norm_num
      have hB : X ^ (-(3 / 8) : ℝ) * X = X ^ (5 / 8 : ℝ) := by
        rw [← Real.rpow_add_one hX0.ne']; norm_num
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) X]
      have h2s : (0 : ℝ) < √2 := by positivity
      have e1 : X ^ (1 / 8 : ℝ) * St7 * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * (√2 * √X) / π) / (π * √2) =
          (2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * St7 / π ^ 2 * (X ^ (1 / 8 : ℝ) * √X) := by
        field_simp
      rw [e1, hA, mul_assoc, hB]
    calc E / (π * √2) ≤ X ^ (1 / 8 : ℝ) * St7 * ((2 + √((n₀ : ℝ) + 1) + √(n₀ : ℝ)) * √(2 * X) / π) / (π * √2) :=
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



/-- `Ω₊` at the first nonzero frequency, normalized (`bco m a n₀ = 1`). -/
theorem omega_plus0 (hd : VData m a) {n₀ : ℕ} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0)
    (hb1 : bco m a n₀ = 1) {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop, ∃ x ∈ Icc X (2 * X), c * x ^ ((m : ℝ) - 1 / 4) < Sre a x := by
  rcases le_or_gt 0 c with hc0 | hc0
  · filter_upwards [omega_core0 hd h0 hz hb1 (Or.inl rfl) hc0 hc] with X ⟨x, hx, h⟩
    exact ⟨x, hx, by linarith⟩
  · have hp : (0 : ℝ) < 1 / (2 * π * √2) := by positivity
    filter_upwards [omega_core0 hd h0 hz hb1 (Or.inl rfl) le_rfl hp, eventually_gt_atTop 0]
      with X ⟨x, hx, h⟩ hX
    refine ⟨x, hx, ?_⟩
    have : 0 ≤ x ^ ((m : ℝ) - 1 / 4) := Real.rpow_nonneg (by linarith [hx.1]) _
    nlinarith

/-- `Ω₋` at the first nonzero frequency, normalized (`bco m a n₀ = 1`). -/
theorem omega_minus0 (hd : VData m a) {n₀ : ℕ} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0)
    (hb1 : bco m a n₀ = 1) {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop, ∃ x ∈ Icc X (2 * X), Sre a x < -c * x ^ ((m : ℝ) - 1 / 4) := by
  rcases le_or_gt 0 c with hc0 | hc0
  · filter_upwards [omega_core0 hd h0 hz hb1 (Or.inr rfl) hc0 hc] with X ⟨x, hx, h⟩
    exact ⟨x, hx, by linarith⟩
  · have hp : (0 : ℝ) < 1 / (2 * π * √2) := by positivity
    filter_upwards [omega_core0 hd h0 hz hb1 (Or.inr rfl) le_rfl hp, eventually_gt_atTop 0]
      with X ⟨x, hx, h⟩ hX
    refine ⟨x, hx, ?_⟩
    have : 0 ≤ x ^ ((m : ℝ) - 1 / 4) := Real.rpow_nonneg (by linarith [hx.1]) _
    nlinarith

/-- **Exact `Ω±(x^{m−1/4})` at the first nonzero frequency `n₀`**, with constant
`c < |a(n₀)| n₀^{−(m+1/4)}/(2π√2)`, for any `VData` sequence. -/
theorem omega_pm_first (hd : VData m a) {n₀ : ℕ} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0)
    (hn₀ : a n₀ ≠ 0) {c : ℝ}
    (hc : c < |a n₀| * (n₀ : ℝ) ^ (-((m : ℝ) + 1 / 4)) / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ ((m : ℝ) - 1 / 4) < Sre a x) ∧
      (∃ x ∈ Icc X (2 * X), Sre a x < -c * x ^ ((m : ℝ) - 1 / 4)) := by
  set α := bco m a n₀ with hα
  have hp : 0 < (n₀ : ℝ) ^ (-((m : ℝ) + 1 / 4)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast h0) _
  have hα0 : α ≠ 0 := mul_ne_zero hn₀ hp.ne'
  have hαabs : |α| = |a n₀| * (n₀ : ℝ) ^ (-((m : ℝ) + 1 / 4)) := by
    rw [hα, bco, abs_mul, abs_of_pos hp]
  rw [← hαabs] at hc
  have hαa : 0 < |α| := abs_pos.2 hα0
  set b : ℕ → ℝ := fun n => α⁻¹ * a n with hbdef
  have hb : VData m b := hd.smul α⁻¹
  have hbz : ∀ n < n₀, b n = 0 := fun n hn => by simp [hbdef, hz n hn]
  have hb1 : bco m b n₀ = 1 := by
    have : bco m b n₀ = α⁻¹ * α := by simp only [bco, hbdef, hα]; ring
    rw [this, inv_mul_cancel₀ hα0]
  have hSb : ∀ x, Sre b x = α⁻¹ * Sre a x := fun x => by unfold Sre; rw [Finset.mul_sum]
  set c' := c / |α| with hc'
  have hc'lt : c' < 1 / (2 * π * √2) := by
    rw [hc', div_lt_iff₀ hαa]
    have : |α| / (2 * π * √2) = 1 / (2 * π * √2) * |α| := by ring
    linarith
  have hcα : c' * |α| = c := by rw [hc']; field_simp
  filter_upwards [omega_plus0 hb h0 hbz hb1 hc'lt, omega_minus0 hb h0 hbz hb1 hc'lt] with X hP hM
  obtain ⟨x1, hx1, hP1⟩ := hP
  obtain ⟨x2, hx2, hM2⟩ := hM
  rw [hSb] at hP1 hM2
  set S1 := Sre a x1
  set S2 := Sre a x2
  rcases lt_or_gt_of_ne hα0 with hneg | hpos
  · have habs : |α| = -α := abs_of_neg hneg
    refine ⟨⟨x2, hx2, ?_⟩, ⟨x1, hx1, ?_⟩⟩
    · have : α⁻¹ * S2 * α > -c' * x2 ^ ((m : ℝ) - 1 / 4) * α :=
        mul_lt_mul_of_neg_right hM2 hneg
      rw [show α⁻¹ * S2 * α = S2 by field_simp] at this
      have e : -c' * x2 ^ ((m : ℝ) - 1 / 4) * α = c * x2 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
    · have : c' * x1 ^ ((m : ℝ) - 1 / 4) * α > α⁻¹ * S1 * α :=
        mul_lt_mul_of_neg_right hP1 hneg
      rw [show α⁻¹ * S1 * α = S1 by field_simp] at this
      have e : c' * x1 ^ ((m : ℝ) - 1 / 4) * α = -c * x1 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
  · have habs : |α| = α := abs_of_pos hpos
    refine ⟨⟨x1, hx1, ?_⟩, ⟨x2, hx2, ?_⟩⟩
    · have : c' * x1 ^ ((m : ℝ) - 1 / 4) * α < α⁻¹ * S1 * α :=
        mul_lt_mul_of_pos_right hP1 hpos
      rw [show α⁻¹ * S1 * α = S1 by field_simp] at this
      have e : c' * x1 ^ ((m : ℝ) - 1 / 4) * α = c * x1 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
    · have : α⁻¹ * S2 * α < -c' * x2 ^ ((m : ℝ) - 1 / 4) * α :=
        mul_lt_mul_of_pos_right hM2 hpos
      rw [show α⁻¹ * S2 * α = S2 by field_simp] at this
      have e : -c' * x2 ^ ((m : ℝ) - 1 / 4) * α = -c * x2 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith

/-- The first nonzero index of a sequence that is not identically zero (with `a 0 = 0`). -/
lemma exists_first {b : ℕ → ℝ} (h0 : b 0 = 0) (hne : ∃ n, b n ≠ 0) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ b n₀ ≠ 0 ∧ ∀ n < n₀, b n = 0 := by
  classical
  refine ⟨Nat.find hne, ?_, Nat.find_spec hne, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hne) with h | h
    · exact absurd (h ▸ Nat.find_spec hne) (by simp [h0])
    · exact h
  · by_contra h; exact Nat.find_min hne hn h

end RamanujanTau.VoronoiTruncComplete
