/-
# One bootstrap step: from `Re s = 6 + y` to `Re s = 6 + x`, `x > y/(1+4y)`

`step_core`: let `0 < x ≤ 1/6`, `0 < y ≤ 1/4`, and suppose
`∫₀ᵁ |L(Δ, 6+y+iu)|² ≤ C(1+U)` for all `U ≥ 0`.  Given `α, η > 0` with

* `α(1 + η − 2x) < 1`   (off-diagonal Montgomery–Vaughan error `≪ log T · T^{α(1+η−2x)} = o(T)`),
* `4y < 2α(x + y)`      (contour remainder `≪ X^{−2(x+y)} T^{1+4y} = o(T)` for `X = T^α`),

the mean square on `Re s = 6 + x` is `∑ τ(n)² n^{−2(6+x)}`.

The proof applies `mean_sq_of_L2approx` to `f(t) = L(Δ, 6+x+it)`, `λ_T = lam δ (T^α)`,
`P_T = ∑_{n ≤ T^α} τ(n)(1 − n/T^α)³ n^{−6−x−it}`, `δ = x + y`: by `tauL_identity` the error
`λ_T f − P_T` is `−Ig/(2π)`, a `P₃`-weighted average of `L` on the line `Re = 6 − y`; there
`left_line_mean_bound` (functional equation) gives `∫_{−U}^{U} |L|² ≪ (1+U)^{1+4y}`, and
`L2_remainder` (Cauchy–Schwarz + Fubini) turns that into `∫₀ᵀ |λ_T f − P_T|² ≪ T^{α·(−2δ)} T^{1+4y}`.

`exists_params`: such `α, η` exist as soon as `y < x(1 + 4y)`.
-/
import RamanujanTau.MeanSquareFull.Identity

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Complex Real MeasureTheory Filter Topology Finset
open RamanujanTau.RankinError RamanujanTau.HeckeL RamanujanTau.MeanSquare

set_option maxHeartbeats 1000000 in
/-- **The bootstrap step.** -/
theorem step_core {x y α η : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 6) (hy0 : 0 < y) (hy1 : y ≤ 1 / 4)
    (hα : 0 < α) (hη : 0 < η) (hdg : α * (1 + η - 2 * x) < 1) (hrem : 4 * y < 2 * α * (x + y))
    {C : ℝ} (hR : ∀ U : ℝ, 0 ≤ U →
      ∫ u in (0 : ℝ)..U, ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ C * (1 + U)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (RS (2 * (6 + x)))) := by
  have hC0 : 0 ≤ C := by have := hR 0 le_rfl; simpa using this
  set σ : ℝ := 6 + x with hσ
  set δ : ℝ := x + y with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have hσδ : σ - δ = 6 - y := by rw [hσ, hδ]; ring
  -- the left line
  set g : ℝ → ℝ := fun u => ‖tauL (((σ - δ : ℝ) : ℂ) + (u : ℂ) * I)‖ with hgdef
  have hgc : Continuous g := (tauLSeries_entire.continuous.comp (by fun_prop)).norm
  have hg0 : ∀ u, 0 ≤ g u := fun u => norm_nonneg _
  obtain ⟨Kc, hKc0, hKc⟩ :=
    RamanujanTau.HeckeConvex.tauL_convexity_strip (ε := 1 / 4) (by norm_num)
  have hgK : ∀ u, g u ≤ Kc * (1 + |u|) := by
    intro u
    have h := hKc (σ - δ) u (by rw [hσδ]; linarith) (by rw [hσδ]; linarith)
    refine h.trans ?_
    have h1 : (1 : ℝ) ≤ 1 + |u| := by linarith [abs_nonneg u]
    have h2 : (1 + |u|) ^ (13 / 2 - (σ - δ) + 1 / 4) ≤ (1 + |u|) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by rw [hσδ]; linarith)
    rw [Real.rpow_one] at h2
    exact mul_le_mul_of_nonneg_left h2 hKc0
  set a : ℝ := 1 + 4 * y with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha2 : a ≤ 2 := by rw [ha]; linarith
  set C' : ℝ := 2 * (6 * Real.exp 10) ^ 2 * C with hC'
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  have hG : ∀ U : ℝ, 0 ≤ U → ∫ u in (-U)..U, g u ^ 2 ≤ C' * (1 + U) ^ a := by
    intro U hU
    have := left_line_mean_bound hy0.le (by linarith) hR U hU
    simp only [hgdef, hσδ]
    exact this
  -- parameters
  set W : ℝ := ∫ y, wt y with hW
  have hW0 : 0 < W := integral_wt_pos
  set J : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  have hA0 := Acst_nonneg hδ0 hδ1
  set K0 : ℝ := (Acst δ / (2 * π)) ^ 2 * W * (C' * J) with hK0
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  set X : ℝ → ℝ := fun T => T ^ α with hX
  have hXt : Tendsto X atTop atTop := tendsto_rpow_atTop hα
  set N : ℝ → ℕ := fun T => ⌊X T⌋₊ with hN
  set Bf : ℝ → ℝ := fun T => K0 * T ^ (-(2 * α * δ)) * (1 + T) ^ a / T with hBf
  have hcont : Continuous fun t : ℝ => tauL ((σ : ℂ) + t * I) :=
    tauLSeries_entire.continuous.comp (by fun_prop)
  have hXpow : ∀ T : ℝ, 0 < T → (X T ^ (-δ)) ^ 2 = T ^ (-(2 * α * δ)) := by
    intro T hT
    simp only [hX]
    rw [← Real.rpow_mul hT.le, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    congr 1; push_cast; ring
  refine mean_sq_of_L2approx hcont (fun T => lam δ (X T)) ((tendsto_lam hδ0 hδ1).comp hXt)
    (fun T => bsm σ (X T)) N Bf ?_ ?_ ?_ ?_
  · -- the `L²` approximation
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hX1 : 1 ≤ X T := Real.one_le_rpow hT hα.le
    have hX0 : 0 < X T := by linarith
    set E : ℝ → ℂ := fun t => lam δ (X T) * tauL ((σ : ℂ) + t * I) -
      dpoly (bsm σ (X T)) (N T) t with hE
    have hEc : Continuous E := (continuous_const.mul hcont).sub (continuous_dpoly _ _)
    set Bc : ℝ := X T ^ (-δ) * Acst δ / (2 * π) with hBc
    have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
    have hEB : ∀ t, ‖E t‖ ≤ Bc * ∫ y, wt y * g (t + y) := by
      intro t
      have hid := tauL_identity (σ := σ) (δ := δ) (by rw [hσ]; linarith) (by rw [hσ]; linarith)
        hδ0 hδ1 hX1 t
      simp only [hE, hN]
      rw [hid, norm_neg, norm_div]
      have hnorm2π : ‖(2 * π : ℂ)‖ = 2 * π := by
        rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hnorm2π, div_le_iff₀ (by positivity)]
      have := norm_Ig_le (σ := σ) hδ0 hδ1 hX0 t (integrable_wt_mul hgc hg0 hgK t)
      refine this.trans (le_of_eq ?_)
      have h2π : (2 * π : ℝ) ≠ 0 := by positivity
      simp only [hBc]
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ h2π]
    have hL2 := L2_remainder hgc hg0 hgK ha0 ha2 hG hEc hBc0 hEB hT0.le
    refine hL2.trans (le_of_eq ?_)
    simp only [hBf, hBc]
    rw [div_pow, mul_pow, hXpow T hT0]
    field_simp
    rw [hK0]; field_simp; ring
  · -- `B → 0`
    set κ : ℝ := 2 * α * δ - 4 * y with hκ
    have hκ0 : 0 < κ := by rw [hκ, hδ]; linarith
    have hlim := (tendsto_rpow_neg_atTop hκ0).const_mul (K0 * 2 ^ a)
    rw [mul_zero] at hlim
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simp only [hBf]; positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := by linarith
      simp only [hBf]
      have h1 : (1 + T) ^ a ≤ 2 ^ a * T ^ a := by
        rw [← Real.mul_rpow (by norm_num) hT0.le]
        exact Real.rpow_le_rpow (by positivity) (by linarith) ha0
      have e : T ^ (-(2 * α * δ)) * T ^ a / T = T ^ (-κ) := by
        rw [← Real.rpow_add hT0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0]
        congr 1; rw [hκ, ha]; ring
      calc K0 * T ^ (-(2 * α * δ)) * (1 + T) ^ a / T
          ≤ K0 * T ^ (-(2 * α * δ)) * (2 ^ a * T ^ a) / T := by gcongr
        _ = K0 * 2 ^ a * (T ^ (-(2 * α * δ)) * T ^ a / T) := by ring
        _ = K0 * 2 ^ a * T ^ (-κ) := by rw [e]
  · -- diagonal
    have hs := summable_tau_sq (β := 2 * σ) (by rw [hσ]; linarith)
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
    set β : ℝ := 12 + η with hβ
    set e : ℝ := β - (2 * σ - 1) with he
    have he0 : 0 ≤ e := by rw [he, hβ, hσ]; linarith
    set p : ℝ := α * e with hp
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hp1 : p < 1 := by
      have : α * e = α * (1 + η - 2 * x) := by rw [he, hβ, hσ]; ring
      rw [hp, this]; exact hdg
    have hlim := (tendsto_log_rpow_div hp0 hp1).const_mul ((1 + α) * RS β)
    rw [mul_zero] at hlim
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have := H_nonneg (N T)
      have : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 :=
        sum_nonneg fun _ _ => by positivity
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := by linarith
      have hX1 : 1 ≤ X T := Real.one_le_rpow hT hα.le
      have hXT : 0 < X T := by linarith
      have hNX : (N T : ℝ) ≤ X T := Nat.floor_le hXT.le
      have hW' : ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 ≤ T ^ p * RS β := by
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
          (by rw [hβ, hσ]; linarith) (N T)).trans ?_
        have hRS := RS_nonneg β
        gcongr
        calc (N T : ℝ) ^ (β - (2 * σ - 1)) ≤ X T ^ e :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hNX he0
          _ = T ^ p := by simp only [hX]; rw [← Real.rpow_mul hT0.le]
      have hH : H (N T) ≤ (1 + α) * (1 + Real.log T) := by
        refine (H_le_one_add_log (N T)).trans ?_
        have hlogX : Real.log (N T) ≤ Real.log (X T) := by
          rcases Nat.eq_zero_or_pos (N T) with h0 | hpos
          · rw [h0]; simp; exact Real.log_nonneg hX1
          · exact Real.log_le_log (by exact_mod_cast hpos) hNX
        have : Real.log (X T) = α * Real.log T := by
          simp only [hX]; rw [Real.log_rpow hT0]
        have hl := Real.log_nonneg hT
        have e : (1 + α) * (1 + Real.log T) = 1 + Real.log T + α + α * Real.log T := by ring
        rw [e]
        linarith [mul_nonneg hα.le hl]
      have hW0' : 0 ≤ ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2 :=
        sum_nonneg fun _ _ => by positivity
      have hlog0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
      calc H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖bsm σ (X T) n‖ ^ 2) / T
          ≤ ((1 + α) * (1 + Real.log T)) * (T ^ p * RS β) / T := by
            gcongr
        _ = (1 + α) * RS β * ((1 + Real.log T) * T ^ p / T) := by ring

/-- Admissible parameters exist when `y < x(1 + 4y)`. -/
lemma exists_params {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 6) (hy0 : 0 < y)
    (hxy : y < x * (1 + 4 * y)) :
    ∃ α η : ℝ, 0 < α ∧ 0 < η ∧ α * (1 + η - 2 * x) < 1 ∧ 4 * y < 2 * α * (x + y) := by
  have hd : 0 < 1 - 2 * x := by linarith
  have hxy0 : 0 < x + y := by linarith
  set p : ℝ := 2 * y / (x + y) with hp
  set q : ℝ := 1 / (1 - 2 * x) with hq
  have hpe : p * (x + y) = 2 * y := by rw [hp]; field_simp
  have hqe : q * (1 - 2 * x) = 1 := by rw [hq]; field_simp
  have hpq : p < q := by
    rw [hp, hq, div_lt_div_iff₀ hxy0 hd]; nlinarith
  have hp0 : 0 < p := by rw [hp]; positivity
  set α : ℝ := (p + q) / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hαq : α * (1 - 2 * x) < 1 := by
    have : α < q := by rw [hα]; linarith
    nlinarith
  have hαp : 4 * y < 2 * α * (x + y) := by
    have : p < α := by rw [hα]; linarith
    nlinarith
  refine ⟨α, (1 - α * (1 - 2 * x)) / (2 * α), hα0, div_pos (by linarith) (by positivity),
    ?_, hαp⟩
  have e : α * (1 + (1 - α * (1 - 2 * x)) / (2 * α) - 2 * x) = (1 + α * (1 - 2 * x)) / 2 := by
    field_simp; ring
  rw [e]; linarith

end RamanujanTau.MeanSquareFull
