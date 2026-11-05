/-
# The mean-square theorem inside the strip: `37/6 < σ ≤ 13/2`

`mean_square_strip`: for `37/6 < σ ≤ 13/2`,

    (1/T) ∫₀ᵀ |L(Δ, σ+it)|² dt → ∑ τ(n)² n^{-2σ}.

Instance of `mean_sq_of_approx` with the smoothed polynomials of `approx_tauL` of length
`X = T^{3/2}`.  Write `x = σ − 6 ∈ (1/6, 1/2]`, `g = x − 1/6`, and choose
`δ = 7/12 + x/2`, `ε = g/2`, so `σ − δ ≥ 11/2`, `δ < 1` and `θ = 13/2 − σ + δ + ε = 1`:

* approximation error `≪ X^{-δ} T = T^{1 − 3δ/2}`, and `1 − 3δ/2 = 1/8 − 3x/4 < 0`;
* off-diagonal error `≪ (1 + log T) X^{13 + g/2 − 2σ} = (1 + log T) T^p`,
  `p = 11/8 − 9x/4 < 1`.

Both exponent conditions are exactly `x > 1/6`, i.e. `σ > 37/6`: this is where the convexity
bound (rather than Lindelöf-type information) limits the range.
-/
import RamanujanTau.MeanSquare.Approx

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Real MeasureTheory Filter Topology Finset
open RamanujanTau.RankinError RamanujanTau.HeckeL

lemma phi_le_one {u : ℝ} (hu : 0 ≤ u) : phi 3 u ≤ 1 := by
  unfold phi
  exact pow_le_one₀ (le_max_right _ _) (max_le (by linarith) zero_le_one)

lemma phi_zero : phi 3 0 = 1 := by rw [phi_of_le zero_le_one]; norm_num

lemma norm_bsm_sq (σ X : ℝ) (n : ℕ) :
    ‖bsm σ X n‖ ^ 2 = ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (phi 3 (n / X)) ^ 2 := by
  have e := norm_babs_sq σ n
  rw [babs] at e
  rw [bsm, norm_mul, mul_pow, e, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The diagonal sum as a `tsum`. -/
lemma sum_bsm_eq_tsum {σ X : ℝ} (hX : 0 < X) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, ‖bsm σ X n‖ ^ 2 =
      ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (phi 3 (n / X)) ^ 2 := by
  rw [tsum_eq_sum (s := range (⌊X⌋₊ + 1))]
  · rw [sum_Icc_eq_sum_range (g := fun n => ‖bsm σ X n‖ ^ 2) (by simp [bsm, tau_zero])]
    exact sum_congr rfl fun n _ => norm_bsm_sq σ X n
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h1 : X < n := by
      have := Nat.lt_floor_add_one X
      have : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this; linarith
    have : 1 < (n : ℝ) / X := by rw [one_lt_div hX]; exact h1
    rw [phi_of_gt (by norm_num) this]; simp

/-- **Mean square of `L(Δ,s)` on `Re s = σ`, `37/6 < σ ≤ 13/2`.** -/
theorem mean_square_strip {σ : ℝ} (hσ1 : 37 / 6 < σ) (hσ2 : σ ≤ 13 / 2) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (RS (2 * σ))) := by
  set x := σ - 6 with hx
  set g := x - 1 / 6 with hg
  have hg0 : 0 < g := by rw [hg, hx]; linarith
  set δ := 7 / 12 + x / 2 with hδ
  set ε := g / 2 with hε
  have hθ1 : 13 / 2 - σ + δ + ε = 1 := by rw [hε, hδ, hg, hx]; ring
  obtain ⟨C, hC0, hC⟩ := approx_tauL (σ := σ) (δ := δ) (ε := ε) (by linarith) hσ2
    (by rw [hδ, hx]; linarith) (by rw [hδ, hx]; linarith) (by rw [hδ, hx]; linarith)
    (by rw [hε]; linarith) (by rw [hθ1]; norm_num)
  rw [hθ1] at hC
  have hcont : Continuous fun t : ℝ => tauL ((σ : ℂ) + t * I) :=
    tauLSeries_entire.continuous.comp (by fun_prop)
  set X : ℝ → ℝ := fun T => T ^ (3 / 2 : ℝ) with hX
  have hXt : Tendsto X atTop atTop := tendsto_rpow_atTop (by norm_num)
  set N : ℝ → ℕ := fun T => ⌊X T⌋₊ with hN
  set ρ : ℝ → ℝ := fun T => C * X T ^ (-δ) * (1 + T) with hρ
  refine mean_sq_of_approx hcont (fun T => bsm σ (X T)) N ρ ?_ ?_ ?_ ?_
  · -- approximation
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT t ht
    have hX1 : 1 ≤ X T := Real.one_le_rpow hT (by norm_num)
    have := hC (X T) hX1 t
    rw [Real.rpow_one] at this
    refine this.trans ?_
    have : 1 + |t| ≤ 1 + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have : 0 ≤ C * X T ^ (-δ) := by positivity
    simp only [hρ]
    gcongr
  · -- `ρ → 0`
    have hexp : 0 < 3 / 2 * δ - 1 := by rw [hδ, hx]; linarith
    have hlim := (tendsto_rpow_neg_atTop hexp).const_mul (2 * C)
    rw [mul_zero] at hlim
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      simp only [hρ, hX]; positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := by linarith
      simp only [hρ, hX]
      rw [← Real.rpow_mul hT0.le]
      have e : T ^ (-(3 / 2 * δ - 1)) = T ^ ((3 / 2 : ℝ) * -δ) * T := by
        rw [show -(3 / 2 * δ - 1) = (3 / 2 : ℝ) * -δ + 1 by ring, Real.rpow_add hT0,
          Real.rpow_one]
      rw [e]
      have : 0 ≤ C * T ^ ((3 / 2 : ℝ) * -δ) := by positivity
      nlinarith
  · -- diagonal
    have hs := summable_tau_sq (β := 2 * σ) (by linarith)
    have hlim : Tendsto (fun T => ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) *
        (phi 3 (n / X T)) ^ 2) atTop
        (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (phi 3 0) ^ 2)) := by
      refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
      · refine tendsto_const_nhds.mul ((((continuous_phi 3).tendsto 0).comp ?_).pow 2)
        exact tendsto_const_nhds.div_atTop hXt
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT n
        have hXT : 0 < X T := by simp only [hX]; positivity
        have hu : 0 ≤ (n : ℝ) / X T := by positivity
        have h1 := phi_le_one hu
        have h0 := phi_nonneg 3 ((n : ℝ) / X T)
        have hA : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by positivity
        rw [Real.norm_of_nonneg (by positivity)]
        have : (phi 3 ((n : ℝ) / X T)) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
        nlinarith
    simp only [phi_zero, one_pow, mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hXT : 0 < X T := by simp only [hX]; positivity
    exact (sum_bsm_eq_tsum hXT).symm
  · -- off-diagonal error
    set β : ℝ := 12 + g / 2 with hβ
    set e : ℝ := β - (2 * σ - 1) with he
    have he0 : 0 ≤ e := by rw [he, hβ]; linarith
    set p : ℝ := 3 / 2 * e with hp
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hp1 : p < 1 := by rw [hp, he, hβ, hg, hx]; linarith
    have hlim := (tendsto_log_rpow_div hp0 hp1).const_mul (3 / 2 * RS β)
    rw [mul_zero] at hlim
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have := H_nonneg (N T)
      have : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 :=
        sum_nonneg fun _ _ => by positivity
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := by linarith
      have hX1 : 1 ≤ X T := Real.one_le_rpow hT (by norm_num)
      have hXT : 0 < X T := by linarith
      have hNX : (N T : ℝ) ≤ X T := Nat.floor_le hXT.le
      -- the weighted sum
      have hW : ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 ≤ T ^ p * RS β := by
        have h1 : ∀ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 ≤
            ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ - 1)) := by
          intro n hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
          rw [norm_bsm_sq]
          have hu : 0 ≤ (n : ℝ) / X T := by positivity
          have hph : (phi 3 ((n : ℝ) / X T)) ^ 2 ≤ 1 :=
            pow_le_one₀ (phi_nonneg 3 _) (phi_le_one hu)
          have e1 : (n : ℝ) ^ (-(2 * σ - 1)) = (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) := by
            rw [show -(2 * σ - 1) = 1 + -(2 * σ) by ring, Real.rpow_add hn0, Real.rpow_one]
          rw [e1]
          have hA : 0 ≤ (n : ℝ) * (((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))) := by positivity
          nlinarith
        refine (sum_le_sum h1).trans ?_
        refine (sum_tau_sq_rpow_le (β := β) (γ := 2 * σ - 1) (by rw [hβ]; linarith)
          (by rw [hβ]; linarith) (N T)).trans ?_
        have hRS := RS_nonneg β
        gcongr
        calc (N T : ℝ) ^ (β - (2 * σ - 1)) ≤ X T ^ e :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hNX he0
          _ = T ^ p := by simp only [hX]; rw [← Real.rpow_mul hT0.le]
      -- the harmonic factor
      have hH : H (N T) ≤ 3 / 2 * (1 + Real.log T) := by
        refine (H_le_one_add_log (N T)).trans ?_
        have hlogX : Real.log (N T) ≤ Real.log (X T) := by
          rcases Nat.eq_zero_or_pos (N T) with h0 | hpos
          · rw [h0]; simp; exact Real.log_nonneg hX1
          · exact Real.log_le_log (by exact_mod_cast hpos) hNX
        have : Real.log (X T) = 3 / 2 * Real.log T := by
          simp only [hX]; rw [Real.log_rpow hT0]
        have hl := Real.log_nonneg hT
        linarith
      have hW0 : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 :=
        sum_nonneg fun _ _ => by positivity
      have hlog0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
      calc H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2) / T
          ≤ (3 / 2 * (1 + Real.log T)) * (T ^ p * RS β) / T := by
            gcongr
        _ = 3 / 2 * RS β * ((1 + Real.log T) * T ^ p / T) := by ring

end RamanujanTau.MeanSquare
