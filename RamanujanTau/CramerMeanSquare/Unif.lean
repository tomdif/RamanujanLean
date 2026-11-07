/-
# The Carlson–Potter mean value of `L(Δ,s)`, uniformly in `σ ∈ [31/5, 25/4]`

`mean_square_unif`: there is `E(T) → 0` such that for all `σ ∈ [31/5, 25/4]` and `T ≥ 1`,

    | (1/T) ∫₀ᵀ |L(Δ,σ+it)|² dt − RS(2σ) | ≤ E(T),        RS(β) = Σ τ(n)² n^{−β}.

`MeanSquare.mean_square_strip` gives the limit for each fixed `σ > 37/6`; here every
parameter of that proof is fixed once for the whole interval (`25/4 − 31/5 = 1/20`):

* Perron shift `δ = 17/25`, convexity loss `ε = 1/100`, length `X = T^{3/2}`
  (`approx_tauL_unif`): `|L − P_T| ≤ C X^{−17/25} (1+T)^{99/100} ≤ 2C T^{−3/100}`;
* off-diagonal (`mv_poly` with `β = 1201/100`): `≤ 9 RS(β) (1 + log T) T^{183/200}`;
* diagonal: `0 ≤ RS(2σ) − Σ |b_n|² ≤ Σ τ(n)² n^{−62/5} (1 − φ(n/X)²) → 0`, a bound
  that does not depend on `σ`.
-/
import RamanujanTau.CramerMeanSquare.Approx

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Complex Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinError RamanujanTau.HeckeL RamanujanTau.MeanSquare

/-- The uniform diagonal tail `Σ τ(n)² n^{−62/5} (1 − φ(n/X)²)`. -/
noncomputable def dX (X : ℝ) : ℝ :=
  ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) * (1 - (phi 3 (n / X)) ^ 2)

lemma phi_sq_mem {u : ℝ} (hu : 0 ≤ u) : 0 ≤ 1 - (phi 3 u) ^ 2 ∧ 1 - (phi 3 u) ^ 2 ≤ 1 := by
  have h0 := phi_nonneg 3 u
  have h1 := phi_le_one hu
  constructor
  · nlinarith
  · nlinarith

lemma summable_62 : Summable fun n : ℕ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) :=
  summable_tau_sq (by norm_num)

lemma tendsto_dX : Tendsto (fun T : ℝ => dX (T ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  have hXt : Tendsto (fun T : ℝ => T ^ (3 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) summable_62
    (f := fun T n => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) *
      (1 - (phi 3 (n / T ^ (3 / 2 : ℝ))) ^ 2))
    (g := fun n => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) * (1 - (phi 3 0) ^ 2))
    (fun n => by
      refine tendsto_const_nhds.mul (tendsto_const_nhds.sub
        ((((continuous_phi 3).tendsto 0).comp ?_).pow 2))
      exact tendsto_const_nhds.div_atTop hXt) ?_
  · simp only [phi_zero, one_pow, sub_self, mul_zero, tsum_zero] at h
    exact h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT n
    have hu : 0 ≤ (n : ℝ) / T ^ (3 / 2 : ℝ) := by positivity
    obtain ⟨h0, h1⟩ := phi_sq_mem hu
    have hA : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith

lemma rpow_le_62 {σ : ℝ} (hσ : 31 / 5 ≤ σ) (n : ℕ) :
    ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tau_zero]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ^ (-(2 * σ)) ≤ (n : ℝ) ^ (-(62 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

/-- The diagonal is uniformly close to `RS(2σ)`. -/
lemma diag_unif {σ : ℝ} (hσ : 31 / 5 ≤ σ) {X : ℝ} (hX : 0 < X) :
    |(∑ n ∈ Icc 1 ⌊X⌋₊, ‖bsm σ X n‖ ^ 2) - RS (2 * σ)| ≤ dX X ∧
      ∑ n ∈ Icc 1 ⌊X⌋₊, ‖bsm σ X n‖ ^ 2 ≤ RS (2 * σ) := by
  rw [sum_bsm_eq_tsum hX]
  have hs := summable_tau_sq (β := 2 * σ) (by linarith)
  have hs1 : Summable fun n : ℕ =>
      ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (phi 3 (n / X)) ^ 2 := by
    refine hs.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    have hu : 0 ≤ (n : ℝ) / X := by positivity
    have := phi_sq_mem hu
    have hA : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by positivity
    nlinarith
  have hs2 : Summable fun n : ℕ =>
      ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (1 - (phi 3 (n / X)) ^ 2) := by
    refine hs.of_nonneg_of_le (fun n => ?_) fun n => ?_
    · have hu : 0 ≤ (n : ℝ) / X := by positivity
      have := (phi_sq_mem hu).1
      positivity
    · have hu : 0 ≤ (n : ℝ) / X := by positivity
      have := phi_sq_mem hu
      have hA : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by positivity
      nlinarith
  have hdiff : RS (2 * σ) - ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (phi 3 (n / X)) ^ 2
      = ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (1 - (phi 3 (n / X)) ^ 2) := by
    rw [RS, ← hs.tsum_sub hs1]
    congr 1; funext n; ring
  have hnn : 0 ≤ ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (1 - (phi 3 (n / X)) ^ 2) :=
    tsum_nonneg fun n => by
      have hu : 0 ≤ (n : ℝ) / X := by positivity
      have := (phi_sq_mem hu).1
      positivity
  have hle : ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (1 - (phi 3 (n / X)) ^ 2) ≤
      dX X := by
    unfold dX
    refine hs2.tsum_le_tsum (fun n => ?_) ?_
    · have hu : 0 ≤ (n : ℝ) / X := by positivity
      have := (phi_sq_mem hu).1
      exact mul_le_mul_of_nonneg_right (rpow_le_62 hσ n) this
    · refine summable_62.of_nonneg_of_le (fun n => ?_) fun n => ?_
      · have hu : 0 ≤ (n : ℝ) / X := by positivity
        have := (phi_sq_mem hu).1
        positivity
      · have hu : 0 ≤ (n : ℝ) / X := by positivity
        have := phi_sq_mem hu
        have hA : 0 ≤ ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(62 / 5 : ℝ)) := by positivity
        nlinarith
  constructor
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · linarith

/-- The off-diagonal weight `Σ n |b_n|² ≤ X^{61/100} RS(1201/100)`. -/
lemma offdiag_unif {σ : ℝ} (hσ1 : 31 / 5 ≤ σ) (hσ2 : σ ≤ 25 / 4) {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, (n : ℝ) * ‖bsm σ X n‖ ^ 2 ≤ X ^ (61 / 100 : ℝ) * RS (1201 / 100) := by
  have hX0 : 0 < X := by linarith
  have hNX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have h1 : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, (n : ℝ) * ‖bsm σ X n‖ ^ 2 ≤
      ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ - 1)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [norm_bsm_sq]
    have hu : 0 ≤ (n : ℝ) / X := by positivity
    have hph : (phi 3 ((n : ℝ) / X)) ^ 2 ≤ 1 := pow_le_one₀ (phi_nonneg 3 _) (phi_le_one hu)
    have e1 : (n : ℝ) ^ (-(2 * σ - 1)) = (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) := by
      rw [show -(2 * σ - 1) = 1 + -(2 * σ) by ring, Real.rpow_add hn0, Real.rpow_one]
    rw [e1]
    have hA : 0 ≤ (n : ℝ) * (((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))) := by positivity
    nlinarith
  refine (sum_le_sum h1).trans ?_
  refine (sum_tau_sq_rpow_le (β := 1201 / 100) (γ := 2 * σ - 1) (by norm_num)
    (by linarith) _).trans ?_
  have hRS := RS_nonneg (1201 / 100)
  gcongr
  calc (⌊X⌋₊ : ℝ) ^ (1201 / 100 - (2 * σ - 1)) ≤ X ^ (1201 / 100 - (2 * σ - 1)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hNX (by linarith)
    _ ≤ X ^ (61 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- The Perron constant for `δ = 17/25`, `ε = 1/100`. -/
lemma approx_unif : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 31 / 5 ≤ σ → σ ≤ 25 / 4 → ∀ T : ℝ, 1 ≤ T →
    ∀ t ∈ Icc 0 T,
      ‖tauL ((σ : ℂ) + t * I) - dpoly (bsm σ (T ^ (3 / 2 : ℝ))) ⌊T ^ (3 / 2 : ℝ)⌋₊ t‖ ≤
        2 * C * T ^ (-(3 / 100 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := approx_tauL_unif (δ := 17 / 25) (ε := 1 / 100) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨C, hC0, fun σ hσ1 hσ2 T hT t ht => ?_⟩
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ T ^ (3 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have h := hC σ (by linarith) (by linarith) (by linarith) (by linarith) _ hX1 t
  refine h.trans ?_
  have hXp : (T ^ (3 / 2 : ℝ)) ^ (-(17 / 25 : ℝ)) = T ^ (-(51 / 50 : ℝ)) := by
    rw [← Real.rpow_mul hT0.le]; norm_num
  rw [hXp]
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have htT : 1 + |t| ≤ 2 * T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hθ : (1 + |t|) ^ (13 / 2 - σ + 17 / 25 + 1 / 100) ≤ 2 * T ^ (99 / 100 : ℝ) := by
    calc (1 + |t|) ^ (13 / 2 - σ + 17 / 25 + 1 / 100) ≤ (1 + |t|) ^ (99 / 100 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ ≤ (2 * T) ^ (99 / 100 : ℝ) := Real.rpow_le_rpow (by linarith) htT (by norm_num)
      _ = 2 ^ (99 / 100 : ℝ) * T ^ (99 / 100 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 * T ^ (99 / 100 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (99 / 100 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have e : T ^ (-(51 / 50 : ℝ)) * T ^ (99 / 100 : ℝ) = T ^ (-(3 / 100 : ℝ)) := by
    rw [← Real.rpow_add hT0]; norm_num
  calc C * T ^ (-(51 / 50 : ℝ)) * (1 + |t|) ^ (13 / 2 - σ + 17 / 25 + 1 / 100)
      ≤ C * T ^ (-(51 / 50 : ℝ)) * (2 * T ^ (99 / 100 : ℝ)) := by gcongr
    _ = 2 * C * (T ^ (-(51 / 50 : ℝ)) * T ^ (99 / 100 : ℝ)) := by ring
    _ = 2 * C * T ^ (-(3 / 100 : ℝ)) := by rw [e]

/-- The integrated approximation error. -/
lemma integral_sq_diff_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {T ρ : ℝ}
    (hT : 0 ≤ T) (h : ∀ t ∈ Icc 0 T, ‖f t - g t‖ ≤ ρ) :
    |(∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) - ∫ t in (0 : ℝ)..T, ‖g t‖ ^ 2| ≤
      T * (ρ ^ 2 + ρ) + ρ * ∫ t in (0 : ℝ)..T, ‖g t‖ ^ 2 := by
  have hcf : Continuous fun t => ‖f t‖ ^ 2 := by fun_prop
  have hcg : Continuous fun t => ‖g t‖ ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_sub (hcf.intervalIntegrable _ _) (hcg.intervalIntegrable _ _)]
  have hpt : ∀ t ∈ Icc 0 T, ‖‖f t‖ ^ 2 - ‖g t‖ ^ 2‖ ≤ ρ ^ 2 + ρ * (1 + ‖g t‖ ^ 2) := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact sq_sub_sq_le (norm_nonneg _) ((abs_norm_sub_norm_le _ _).trans (h t ht))
  have hI := intervalIntegral.norm_integral_le_of_norm_le hT
    (Eventually.of_forall fun t ht => hpt t (Set.Ioc_subset_Icc_self ht))
    ((show Continuous fun t => ρ ^ 2 + ρ * (1 + ‖g t‖ ^ 2) by fun_prop).intervalIntegrable
      (μ := volume) 0 T)
  rw [← Real.norm_eq_abs]
  refine hI.trans (le_of_eq ?_)
  have e2 : (fun t => ρ ^ 2 + ρ * (1 + ‖g t‖ ^ 2)) = fun t => (ρ ^ 2 + ρ) + ρ * ‖g t‖ ^ 2 := by
    funext t; ring
  rw [e2, intervalIntegral.integral_add (intervalIntegrable_const (μ := volume))
    ((hcg.const_mul ρ).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

/-- **Uniform Carlson–Potter mean value on `σ ∈ [31/5, 25/4]`.** -/
theorem mean_square_unif : ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
    ∀ σ : ℝ, 31 / 5 ≤ σ → σ ≤ 25 / 4 → ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T - RS (2 * σ)| ≤ E T := by
  obtain ⟨C, hC0, hC⟩ := approx_unif
  set ρ : ℝ → ℝ := fun T => 2 * C * T ^ (-(3 / 100 : ℝ)) with hρ
  set Rb : ℝ := RS (1201 / 100) with hRb
  set Ra : ℝ := RS (62 / 5) with hRa
  set e : ℝ → ℝ := fun T => 9 * Rb * ((1 + Real.log T) * T ^ (183 / 200 : ℝ) / T) with he
  set d : ℝ → ℝ := fun T => dX (T ^ (3 / 2 : ℝ)) with hd
  refine ⟨fun T => ρ T ^ 2 + ρ T + ρ T * (Ra + e T) + e T + d T, ?_, ?_⟩
  · have hρl : Tendsto ρ atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 3 / 100) (by norm_num)).const_mul (2 * C)
      simpa [hρ] using this
    have hel : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_log_rpow_div (p := 183 / 200) (by norm_num) (by norm_num)).const_mul
        (9 * Rb)
      simpa [he] using this
    have h := ((((hρl.pow 2).add hρl).add (hρl.mul ((tendsto_const_nhds (x := Ra)).add hel))).add hel).add
      tendsto_dX
    simpa using h
  · intro σ hσ1 hσ2 T hT
    have hT0 : 0 < T := by linarith
    set X : ℝ := T ^ (3 / 2 : ℝ) with hX
    have hX1 : 1 ≤ X := Real.one_le_rpow hT (by norm_num)
    have hX0 : 0 < X := by linarith
    set N : ℕ := ⌊X⌋₊ with hN
    set b := bsm σ X with hb
    set I0 : ℝ := ∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2 with hI0
    set MD : ℝ := ∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2 with hMD
    set A : ℝ := ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 with hA
    have hρ0 : 0 ≤ ρ T := by simp only [hρ]; positivity
    have hcont : Continuous fun t : ℝ => tauL ((σ : ℂ) + t * I) :=
      tauLSeries_entire.continuous.comp (by fun_prop)
    -- (i) approximation
    have h1 : |I0 - MD| ≤ T * (ρ T ^ 2 + ρ T) + ρ T * MD :=
      integral_sq_diff_le hcont (continuous_dpoly b N) hT0.le (hC σ hσ1 hσ2 T hT)
    -- (ii) polynomial mean value
    have hH : H N ≤ 3 / 2 * (1 + Real.log T) := by
      refine (H_le_one_add_log N).trans ?_
      have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
      have hlogX : Real.log N ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · rw [h0]; simp; exact Real.log_nonneg hX1
        · exact Real.log_le_log (by exact_mod_cast hpos) hNX
      have : Real.log X = 3 / 2 * Real.log T := by rw [hX, Real.log_rpow hT0]
      have hl := Real.log_nonneg hT
      linarith
    have hW := offdiag_unif hσ1 hσ2 hX1
    have hXp : X ^ (61 / 100 : ℝ) = T ^ (183 / 200 : ℝ) := by
      rw [hX, ← Real.rpow_mul hT0.le]; norm_num
    rw [hXp] at hW
    have h2 : |MD - T * A| ≤ T * e T := by
      refine (mv_poly b N T).trans ?_
      have hW0 : 0 ≤ ∑ n ∈ Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 := sum_nonneg fun _ _ => by positivity
      have hlog0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
      have hRb0 : 0 ≤ Rb := RS_nonneg _
      calc 6 * H N * ∑ n ∈ Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2
          ≤ 6 * (3 / 2 * (1 + Real.log T)) * (T ^ (183 / 200 : ℝ) * Rb) := by
            gcongr
        _ = T * e T := by simp only [he]; field_simp; ring
    -- (iii) diagonal
    obtain ⟨h3, hAR⟩ := diag_unif hσ1 hX0
    have hRR : RS (2 * σ) ≤ Ra := by
      unfold RS
      exact (summable_tau_sq (by linarith)).tsum_le_tsum (fun n => rpow_le_62 hσ1 n) summable_62
    have hd0 : 0 ≤ d T := by
      simp only [hd]; unfold dX
      exact tsum_nonneg fun n => by
        have hu : 0 ≤ (n : ℝ) / X := by positivity
        have := (phi_sq_mem hu).1
        positivity
    -- assembly
    have hMDle : MD ≤ T * (Ra + e T) := by
      have := (abs_le.1 h2).2
      nlinarith
    have hMD0 : 0 ≤ MD := intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
    have key : |I0 - T * RS (2 * σ)| ≤ T * (ρ T ^ 2 + ρ T + ρ T * (Ra + e T) + e T + d T) := by
      have hsplit : I0 - T * RS (2 * σ) = (I0 - MD) + (MD - T * A) + T * (A - RS (2 * σ)) := by
        ring
      rw [hsplit]
      have h3' : |T * (A - RS (2 * σ))| ≤ T * d T := by
        rw [abs_mul, abs_of_pos hT0]; exact mul_le_mul_of_nonneg_left h3 hT0.le
      have hρMD : ρ T * MD ≤ T * (ρ T * (Ra + e T)) := by
        have := mul_le_mul_of_nonneg_left hMDle hρ0; nlinarith
      calc |(I0 - MD) + (MD - T * A) + T * (A - RS (2 * σ))|
          ≤ |I0 - MD| + |MD - T * A| + |T * (A - RS (2 * σ))| := abs_add_three _ _ _
        _ ≤ (T * (ρ T ^ 2 + ρ T) + ρ T * MD) + T * e T + T * d T := by gcongr
        _ ≤ T * (ρ T ^ 2 + ρ T) + T * (ρ T * (Ra + e T)) + T * e T + T * d T := by linarith
        _ = _ := by ring
    rw [show I0 / T - RS (2 * σ) = (I0 - T * RS (2 * σ)) / T by field_simp, abs_div,
      abs_of_pos hT0, div_le_iff₀ hT0]
    linarith

end RamanujanTau.CramerMeanSquare
