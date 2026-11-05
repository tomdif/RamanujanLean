/-
# Mean-square bounds on lines left of the critical line, via the functional equation

* `norm_tauL_neg`: `|L(Δ, σ − iu)| = |L(Δ, σ + iu)|` (from `tauL_conj`).
* `norm_tauL_left_le` (uniform Stirling for `Γ(12−s)/Γ(s)`): for `0 ≤ y ≤ 1/2`,
  `|L(Δ, 6−y+iu)| ≤ 6e¹⁰ (1+|u|)^{2y} |L(Δ, 6+y+iu)|`.
* `bound_of_tendsto`: a mean-square limit gives `∫₀ᵁ ≤ C(1+U)` for all `U ≥ 0`.
* `left_line_mean_bound`: if `∫₀ᵁ |L(Δ,6+y+iu)|² ≤ C(1+U)` for all `U ≥ 0`, then
  `∫_{−U}^{U} |L(Δ,6−y+iu)|² ≤ 2(6e¹⁰)² C (1+U)^{1+4y}`.
-/
import RamanujanTau.MeanSquareFull.L2Assembly
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Complex Real MeasureTheory intervalIntegral Filter Topology
open RamanujanTau.HeckeL
open scoped ComplexConjugate

lemma norm_tauL_neg (σ u : ℝ) :
    ‖tauL ((σ : ℂ) + ((-u : ℝ) : ℂ) * I)‖ = ‖tauL ((σ : ℂ) + (u : ℂ) * I)‖ := by
  have e : ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) = conj ((σ : ℂ) + (u : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [e, RamanujanTau.HeckeZeros.tauL_conj, Complex.norm_conj]

/-- **Functional equation + uniform Stirling**: `|L(6−y+iu)| ≪ (1+|u|)^{2y} |L(6+y+iu)|`. -/
theorem norm_tauL_left_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) (u : ℝ) :
    ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      6 * Real.exp 10 * (1 + |u|) ^ (2 * y) * ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  set s : ℂ := ((6 - y : ℝ) : ℂ) + (u : ℂ) * I with hsdef
  have hs : s.re = 6 - y := by simp [hsdef]
  have hsim : s.im = u := by simp [hsdef]
  have hs0 : ∀ n : ℕ, 12 - s ≠ -n := by
    intro n h; have := congrArg re h; simp [hs] at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hT : tauL s = ((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))) *
      (Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹) * tauL (12 - s) := by
    conv_lhs => rw [tauL, ← heckeLambda_functional_equation s, heckeLambda_eq_tauL hs0]
    ring
  have e1 : 12 - s = starRingEnd ℂ s + ((2 * y : ℝ) : ℂ) := by
    rw [RamanujanTau.HeckeConvex.twelve_sub_eq_conj_add, hs]; congr 1; push_cast; ring
  have hcs1 : 1 ≤ (starRingEnd ℂ s).re := by simp [hs]; linarith
  have I1 := RamanujanTau.Stirling.norm_Gamma_add_le_one hcs1 (θ := 2 * y) (by positivity)
    (by linarith)
  rw [← e1, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I1
  have hA : 0 < ‖Complex.Gamma s‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; linarith))
  have hP : ‖(2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))‖ ≤ 1 := by
    rw [norm_mul, RamanujanTau.HeckeConvex.norm_two_pi_cpow',
      RamanujanTau.HeckeConvex.norm_two_pi_cpow', ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; linarith
  have hQ : ‖Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹‖ ≤ Real.exp 10 * ‖s‖ ^ (2 * y) := by
    rw [norm_mul, norm_inv, mul_inv_le_iff₀ hA]; linarith
  have hL : ‖tauL (12 - s)‖ = ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
    have e : 12 - s = conj (((6 + y : ℝ) : ℂ) + (u : ℂ) * I) := by
      apply Complex.ext <;> simp [hsdef]; ring
    rw [e, RamanujanTau.HeckeZeros.tauL_conj, Complex.norm_conj]
  have hn : ‖s‖ ≤ 6 * (1 + |u|) := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hs, hsim, abs_of_nonneg (by linarith : (0:ℝ) ≤ 6 - y)]; linarith [abs_nonneg u]
  have hn2 : ‖s‖ ^ (2 * y) ≤ 6 * (1 + |u|) ^ (2 * y) := by
    calc ‖s‖ ^ (2 * y) ≤ (6 * (1 + |u|)) ^ (2 * y) :=
          Real.rpow_le_rpow (norm_nonneg _) hn (by positivity)
      _ = 6 ^ (2 * y) * (1 + |u|) ^ (2 * y) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 6 * (1 + |u|) ^ (2 * y) := by
          gcongr
          calc (6 : ℝ) ^ (2 * y) ≤ 6 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 6 := Real.rpow_one 6
  rw [hT, norm_mul, norm_mul, hL]
  have hLn := norm_nonneg (tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I))
  calc _ ≤ 1 * (Real.exp 10 * ‖s‖ ^ (2 * y)) * ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
        gcongr
    _ ≤ 1 * (Real.exp 10 * (6 * (1 + |u|) ^ (2 * y))) *
          ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ := by gcongr
    _ = _ := by ring

/-- A mean-square limit gives a linear upper bound valid for every `U ≥ 0`. -/
lemma bound_of_tendsto {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ u, 0 ≤ h u) {S : ℝ}
    (hT : Tendsto (fun T => (∫ t in (0 : ℝ)..T, h t) / T) atTop (𝓝 S)) :
    ∃ C : ℝ, ∀ U : ℝ, 0 ≤ U → ∫ u in (0 : ℝ)..U, h u ≤ C * (1 + U) := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.1
    ((hT.eventually (gt_mem_nhds (lt_add_one S))).and (eventually_gt_atTop (0 : ℝ)))
  set T1 := max T0 1
  set M0 := ∫ u in (0 : ℝ)..T1, h u
  have hM0 : 0 ≤ M0 := intervalIntegral.integral_nonneg (by positivity) fun u _ => h0 u
  refine ⟨max (S + 1) 0 + M0, fun U hU => ?_⟩
  rcases le_or_gt T1 U with h1 | h1
  · obtain ⟨hlt, hpos⟩ := hT0 U ((le_max_left _ _).trans h1)
    have := (div_lt_iff₀ hpos).1 hlt
    have : (S + 1) * U ≤ max (S + 1) 0 * (1 + U) := by
      calc (S + 1) * U ≤ max (S + 1) 0 * U := by gcongr; exact le_max_left _ _
        _ ≤ max (S + 1) 0 * (1 + U) := by gcongr; linarith
    nlinarith [le_max_right (S + 1) 0]
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 U) (hc.intervalIntegrable U T1)
    have hnn : 0 ≤ ∫ u in U..T1, h u :=
      intervalIntegral.integral_nonneg h1.le fun u _ => h0 u
    have : ∫ u in (0 : ℝ)..U, h u ≤ M0 := by linarith
    have hm : 0 ≤ max (S + 1) 0 * (1 + U) := by
      have := le_max_right (S + 1) 0; positivity
    nlinarith

/-- **Mean square on the left line `Re s = 6 − y`.** -/
theorem left_line_mean_bound {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) {C : ℝ}
    (hC : ∀ U : ℝ, 0 ≤ U →
      ∫ u in (0 : ℝ)..U, ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ C * (1 + U)) :
    ∀ U : ℝ, 0 ≤ U → ∫ u in (-U)..U, ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      2 * (6 * Real.exp 10) ^ 2 * C * (1 + U) ^ (1 + 4 * y) := by
  intro U hU
  set h : ℝ → ℝ := fun u => ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 with hh
  have hcont : ∀ σ : ℝ, Continuous fun u : ℝ => ‖tauL ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
    fun σ => (tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2
  have hhc : Continuous h := hcont (6 + y)
  have heven : ∀ u, h (-u) = h u := fun u => by simp only [hh]; rw [norm_tauL_neg]
  -- `∫_{−U}^{U} h = 2 ∫₀ᵁ h`
  have hsym : ∫ u in (-U)..U, h u = 2 * ∫ u in (0 : ℝ)..U, h u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hhc.intervalIntegrable (μ := volume) _ _) (hhc.intervalIntegrable (μ := volume) _ _)]
    have e := intervalIntegral.integral_comp_neg (a := 0) (b := U) h
    simp only [neg_zero] at e
    simp_rw [heven] at e
    rw [← e]; ring
  set K : ℝ := 6 * Real.exp 10
  have hK : 0 ≤ K := by positivity
  have hpt : ∀ u ∈ Set.Icc (-U) U, ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      K ^ 2 * (1 + U) ^ (4 * y) * h u := by
    intro u hu
    have hb := norm_tauL_left_le hy0 hy1 u
    have hu' : |u| ≤ U := abs_le.2 hu
    have h1 : (1 + |u|) ^ (2 * y) ≤ (1 + U) ^ (2 * y) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have h2 : ((1 + U) ^ (2 * y)) ^ 2 = (1 + U) ^ (4 * y) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
    have hb2 : ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        K * (1 + U) ^ (2 * y) * ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
      refine hb.trans ?_
      gcongr
    calc ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2
        ≤ (K * (1 + U) ^ (2 * y) * ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb2 2
      _ = K ^ 2 * ((1 + U) ^ (2 * y)) ^ 2 * h u := by simp only [hh]; ring
      _ = _ := by rw [h2]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -U ≤ U)
    ((hcont (6 - y)).intervalIntegrable (μ := volume) _ _)
    ((hhc.const_mul (K ^ 2 * (1 + U) ^ (4 * y))).intervalIntegrable (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_const_mul, hsym] at hmono
  refine hmono.trans ?_
  have hcU := hC U hU
  have hp : (1 + U) ^ (1 + 4 * y) = (1 + U) * (1 + U) ^ (4 * y) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  rw [hp]
  have : 0 ≤ K ^ 2 * (1 + U) ^ (4 * y) := by positivity
  calc K ^ 2 * (1 + U) ^ (4 * y) * (2 * ∫ u in (0 : ℝ)..U, h u)
      ≤ K ^ 2 * (1 + U) ^ (4 * y) * (2 * (C * (1 + U))) := by gcongr
    _ = _ := by ring

end RamanujanTau.MeanSquareFull
