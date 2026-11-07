/-
# Uniform tails of `∫ |L(Δ,σ+iu)/(σ+iu)|² du` for `23/4 < σ < 6`

`Ψ_σ(u) = |L(Δ,σ+iu)/(σ+iu)|²`.  For `σ = 6 − y`, `0 < y < 1/4`:

* `block_bound`: `∫_T^{2T} Ψ_{6−y} ≤ K T^{4y−1} / y` for `T ≥ 1`, with `K` independent of `y`
  (`HardyCountHafner.mean_square_uniform` on the line `6 + y`, moved to `6 − y` by
  `MeanSquareFull.norm_tauL_left_le`);
* `tail_of_blocks`: dyadic summation of block bounds `B T^{−p}` gives integrability on `(R,∞)` and
  `∫_R^∞ ≤ B R^{−p}/(1 − 2^{−p})`;
* `tail_bound`: hence `∫_R^∞ Ψ_{6−y} ≤ K R^{−(1−4y)} / (y (1 − 2^{−(1−4y)}))`, uniformly in `y`.
-/
import RamanujanTau.HardyCountHafner.MeanSquare
import RamanujanTau.MeanSquareFull.LeftLine

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL
open scoped ComplexConjugate Real

/-- `Ψ_σ(u) = |L(Δ, σ+iu)/(σ+iu)|²`. -/
noncomputable def Psi (σ u : ℝ) : ℝ :=
  ‖tauL ((σ : ℂ) + (u : ℂ) * I) / ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2

lemma Psi_nonneg (σ u : ℝ) : 0 ≤ Psi σ u := by unfold Psi; positivity

lemma ne_zero_of_re_pos {σ : ℝ} (hσ : 0 < σ) (u : ℝ) : (σ : ℂ) + (u : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

lemma continuous_Psi {σ : ℝ} (hσ : 0 < σ) : Continuous (Psi σ) := by
  unfold Psi
  refine (Continuous.norm ?_).pow 2
  refine Continuous.div (tauLSeries_entire.continuous.comp (by fun_prop)) (by fun_prop) ?_
  exact ne_zero_of_re_pos hσ

lemma Psi_neg (σ u : ℝ) : Psi σ (-u) = Psi σ u := by
  unfold Psi
  rw [norm_div, norm_div]
  have h1 := RamanujanTau.MeanSquareFull.norm_tauL_neg σ u
  have h2 : ‖(σ : ℂ) + ((-u : ℝ) : ℂ) * I‖ = ‖(σ : ℂ) + (u : ℂ) * I‖ := by
    have e : ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) = conj ((σ : ℂ) + (u : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, Complex.norm_conj]
  rw [h1, h2]

lemma Psi_le {σ u : ℝ} (hu : 0 < u) :
    Psi σ u ≤ ‖tauL ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 / u ^ 2 := by
  unfold Psi
  rw [norm_div, div_pow]
  have h1 : u ≤ ‖(σ : ℂ) + (u : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I)
    simp at this
    rw [abs_of_pos hu] at this; exact this
  have h2 : u ^ 2 ≤ ‖(σ : ℂ) + (u : ℂ) * I‖ ^ 2 := pow_le_pow_left₀ hu.le h1 2
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2

/-- **Block bound** on `σ = 6 − y`: `∫_T^{2T} Ψ_{6−y} ≤ K T^{4y−1}/y`, uniformly in `0 < y ≤ 1/4`. -/
theorem block_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 4 → ∀ T : ℝ, 1 ≤ T →
    ∫ u in Icc T (2 * T), Psi (6 - y) u ≤ K * T ^ (4 * y - 1) / y := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.HardyCountHafner.mean_square_uniform
  set E : ℝ := 6 * Real.exp 10 with hE
  refine ⟨3 * E ^ 2 * C, by positivity, fun y hy0 hy1 T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hm := hC y hy0 (by linarith) T hT
  set g : ℝ → ℝ := fun u => ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 with hg
  have hgc : Continuous g :=
    (tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2
  have h6 : (0 : ℝ) < 6 - y := by linarith
  -- pointwise
  have hpt : ∀ u ∈ Icc T (2 * T), Psi (6 - y) u ≤ 3 * E ^ 2 * T ^ (4 * y - 2) * g u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have h1 := Psi_le (σ := 6 - y) hu0
    have h2 := RamanujanTau.MeanSquareFull.norm_tauL_left_le hy0.le (by linarith) u
    have e6 : ((6 - y : ℝ) : ℂ) = ((6 - y : ℝ) : ℂ) := rfl
    rw [abs_of_pos hu0] at h2
    have h3 : ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
        (E * (1 + u) ^ (2 * y)) ^ 2 * g u := by
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [hg]; simp only
      calc _ ≤ (6 * Real.exp 10 * (1 + u) ^ (2 * y) *
            ‖tauL (((6 + y : ℝ) : ℂ) + (u : ℂ) * I)‖) ^ 2 := this
        _ = _ := by rw [hE]; ring
    have h4 : ((1 + u) ^ (2 * y)) ^ 2 ≤ 3 * T ^ (4 * y) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      have e : 2 * y * ((2 : ℕ) : ℝ) = 4 * y := by push_cast; ring
      rw [e]
      have hb : 1 + u ≤ 3 * T := by linarith [hu.2]
      calc (1 + u) ^ (4 * y) ≤ (3 * T) ^ (4 * y) :=
            Real.rpow_le_rpow (by linarith) hb (by linarith)
        _ = 3 ^ (4 * y) * T ^ (4 * y) := Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 3 * T ^ (4 * y) := by
            gcongr
            calc (3 : ℝ) ^ (4 * y) ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 3 := Real.rpow_one 3
    have hu2 : T ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hT0.le hu.1 2
    have hg0 : 0 ≤ g u := by rw [hg]; positivity
    have hTp : T ^ (4 * y - 2) = T ^ (4 * y) / T ^ 2 := by
      rw [Real.rpow_sub hT0, Real.rpow_two]
    calc Psi (6 - y) u ≤ ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 / u ^ 2 := h1
      _ ≤ ‖tauL (((6 - y : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 / T ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hu2
      _ ≤ (E * (1 + u) ^ (2 * y)) ^ 2 * g u / T ^ 2 := by gcongr
      _ = E ^ 2 * ((1 + u) ^ (2 * y)) ^ 2 * g u / T ^ 2 := by ring
      _ ≤ E ^ 2 * (3 * T ^ (4 * y)) * g u / T ^ 2 := by gcongr
      _ = 3 * E ^ 2 * T ^ (4 * y - 2) * g u := by rw [hTp]; ring
  have hPc := continuous_Psi h6
  have hint : ∫ u in Icc T (2 * T), Psi (6 - y) u ≤
      ∫ u in Icc T (2 * T), 3 * E ^ 2 * T ^ (4 * y - 2) * g u :=
    setIntegral_mono_on hPc.integrableOn_Icc (hgc.const_mul _).integrableOn_Icc
      measurableSet_Icc hpt
  rw [integral_const_mul] at hint
  refine hint.trans ?_
  have hm' : ∫ u in Icc T (2 * T), g u ≤ C * T / y := by
    rw [hg]; exact hm
  have hTq : T ^ (4 * y - 2) * T = T ^ (4 * y - 1) := by
    rw [show 4 * y - 1 = (4 * y - 2) + 1 by ring, Real.rpow_add hT0, Real.rpow_one]
  calc 3 * E ^ 2 * T ^ (4 * y - 2) * ∫ u in Icc T (2 * T), g u
      ≤ 3 * E ^ 2 * T ^ (4 * y - 2) * (C * T / y) := by gcongr
    _ = 3 * E ^ 2 * C * (T ^ (4 * y - 2) * T) / y := by ring
    _ = _ := by rw [hTq]

/-- **Dyadic tail summation.** -/
theorem tail_of_blocks {φ : ℝ → ℝ} (hc : Continuous φ) (h0 : ∀ u, 0 ≤ φ u) {R B p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hb : ∀ T, R ≤ T → ∫ u in Icc T (2 * T), φ u ≤ B * T ^ (-p)) :
    IntegrableOn φ (Ioi R) ∧ ∫ u in Ioi R, φ u ≤ B * R ^ (-p) / (1 - 2 ^ (-p)) := by
  set b : ℕ → ℝ := fun n => 2 ^ n * R with hbdef
  set r : ℝ := (2 : ℝ) ^ (-p) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbR : ∀ n, R ≤ b n := fun n => by
    simp only [hbdef]; exact le_mul_of_one_le_left hR.le (one_le_pow₀ (by norm_num))
  have hbs : ∀ n, b (n + 1) = 2 * b n := fun n => by simp only [hbdef]; rw [pow_succ]; ring
  have hblock : ∀ j, ∫ u in b j..b (j + 1), φ u ≤ B * R ^ (-p) * r ^ j := by
    intro j
    rw [hbs, intervalIntegral.integral_of_le (by linarith [hbR j]),
      ← integral_Icc_eq_integral_Ioc]
    refine (hb (b j) (hbR j)).trans (le_of_eq ?_)
    simp only [hbdef]
    rw [Real.mul_rpow (by positivity) hR.le, hr, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hBn : 0 ≤ B * R ^ (-p) := by
    have := hb R le_rfl
    have hI : 0 ≤ ∫ u in Icc R (2 * R), φ u := setIntegral_nonneg measurableSet_Icc fun u _ => h0 u
    linarith
  have hpart : ∀ n : ℕ, ∫ u in R..b n, φ u ≤ B * R ^ (-p) / (1 - r) := by
    intro n
    have hsum : ∑ j ∈ Finset.range n, ∫ u in b j..b (j + 1), φ u = ∫ u in b 0..b n, φ u :=
      intervalIntegral.sum_integral_adjacent_intervals fun j _ => (hc.intervalIntegrable _ _)
    have hb0 : b 0 = R := by simp [hbdef]
    have e0 : ∫ u in R..b n, φ u = ∫ u in b 0..b n, φ u := by rw [hb0]
    rw [e0, ← hsum]
    calc ∑ j ∈ Finset.range n, ∫ u in b j..b (j + 1), φ u
        ≤ ∑ j ∈ Finset.range n, B * R ^ (-p) * r ^ j := Finset.sum_le_sum fun j _ => hblock j
      _ = B * R ^ (-p) * ∑ j ∈ Finset.range n, r ^ j := by rw [Finset.mul_sum]
      _ ≤ B * R ^ (-p) * (1 / (1 - r)) := by
          gcongr
          rw [geom_sum_eq hr1.ne]
          have e : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
            rw [← neg_div_neg_eq]; ring_nf
          rw [e]
          exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 n]) (by linarith)
      _ = B * R ^ (-p) / (1 - r) := by ring
  have hbt : Tendsto b atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hR
  have hint : IntegrableOn φ (Ioi R) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (B * R ^ (-p) / (1 - r)) R
      (fun i => hc.integrableOn_Ioc) hbt (Eventually.of_forall fun n => ?_)
    simp_rw [Real.norm_of_nonneg (h0 _)]
    exact hpart n
  refine ⟨hint, ?_⟩
  exact le_of_tendsto' (intervalIntegral_tendsto_integral_Ioi R hint hbt) hpart

/-- **Uniform tail bound** for `Ψ_{6−y}`, `0 < y < 1/4`. -/
theorem tail_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → y < 1 / 4 → ∀ R : ℝ, 1 ≤ R →
    IntegrableOn (Psi (6 - y)) (Ioi R) ∧
    ∫ u in Ioi R, Psi (6 - y) u ≤ K / y * R ^ (-(1 - 4 * y)) / (1 - 2 ^ (-(1 - 4 * y))) := by
  obtain ⟨K, hK0, hK⟩ := block_bound
  refine ⟨K, hK0, fun y hy0 hy1 R hR => ?_⟩
  refine tail_of_blocks (continuous_Psi (by linarith)) (Psi_nonneg _) (by linarith : (0:ℝ) < R)
    (by linarith : 0 < 1 - 4 * y) (B := K / y) (fun T hT => ?_)
  have := hK y hy0 hy1.le T (by linarith)
  calc _ ≤ K * T ^ (4 * y - 1) / y := this
    _ = K / y * T ^ (-(1 - 4 * y)) := by rw [neg_sub]; ring

/-- Splitting an even continuous function integrable on `(R,∞)`. -/
theorem even_split {φ : ℝ → ℝ} (hc : Continuous φ) (he : ∀ u, φ (-u) = φ u) {R : ℝ}
    (hR : 0 ≤ R) (hi : IntegrableOn φ (Ioi R)) :
    Integrable φ ∧ ∫ u, {u : ℝ | R < |u|}.indicator φ u = 2 * ∫ u in Ioi R, φ u ∧
      ∫ u, φ u = (∫ u in Icc (-R) R, φ u) + 2 * ∫ u in Ioi R, φ u := by
  set ψ : ℝ → ℝ := (Ioi R).indicator φ with hψ
  set χ : ℝ → ℝ := (Icc (-R) R).indicator φ with hχ
  have hψi : Integrable ψ := (integrable_indicator_iff measurableSet_Ioi).2 hi
  have hψn : Integrable (fun u => ψ (-u)) := hψi.comp_neg
  have hχi : Integrable χ :=
    (integrable_indicator_iff measurableSet_Icc).2 hc.integrableOn_Icc
  have hind : ∀ u, {u : ℝ | R < |u|}.indicator φ u = ψ u + ψ (-u) := by
    intro u
    simp only [hψ, Set.indicator, mem_Ioi, mem_setOf_eq]
    rcases le_or_gt 0 u with h | h
    · simp only [abs_of_nonneg h]
      by_cases hu : R < u
      · have : ¬ R < -u := by linarith
        simp [hu, this]
      · simp [hu]
        intro h'; linarith
    · simp only [abs_of_neg h]
      by_cases hu : R < -u
      · have : ¬ R < u := by linarith
        simp [hu, this, he]
      · simp [hu]
        intro h'; linarith
  have hsplit : ∀ u, φ u = χ u + (ψ u + ψ (-u)) := by
    intro u
    rw [← hind]
    simp only [hχ, Set.indicator, mem_Icc, mem_setOf_eq]
    by_cases h : R < |u|
    · have : ¬ (-R ≤ u ∧ u ≤ R) := by
        rintro ⟨h1, h2⟩; have := abs_le.2 ⟨h1, h2⟩; linarith
      simp [h, this]
    · push Not at h
      have := abs_le.1 h
      simp [this.1, this.2, not_lt.2 h]
  have hφi : Integrable φ := by
    have : φ = fun u => χ u + (ψ u + ψ (-u)) := funext hsplit
    rw [this]; exact hχi.add (hψi.add hψn)
  have hI2 : ∫ u, {u : ℝ | R < |u|}.indicator φ u = 2 * ∫ u in Ioi R, φ u := by
    simp_rw [hind]
    rw [integral_add hψi hψn, integral_neg_eq_self, hψ, integral_indicator measurableSet_Ioi]
    ring
  refine ⟨hφi, hI2, ?_⟩
  have hχint : ∫ u, χ u = ∫ u in Icc (-R) R, φ u := integral_indicator measurableSet_Icc
  calc ∫ u, φ u = ∫ u, (χ u + (ψ u + ψ (-u))) := integral_congr_ae (Eventually.of_forall hsplit)
    _ = (∫ u, χ u) + ∫ u, (ψ u + ψ (-u)) := integral_add hχi (hψi.add hψn)
    _ = (∫ u in Icc (-R) R, φ u) + 2 * ∫ u in Ioi R, φ u := by
        rw [hχint, ← hI2]; congr 1; exact integral_congr_ae (Eventually.of_forall fun u => (hind u).symm)

/-- `Ψ_{6−y}` is integrable on `ℝ` for `0 < y < 1/4`. -/
theorem integrable_Psi {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 4) : Integrable (Psi (6 - y)) := by
  obtain ⟨K, _, hK⟩ := tail_bound
  exact (even_split (continuous_Psi (by linarith)) (Psi_neg _) zero_le_one (hK y hy0 hy1 1 le_rfl).1).1

end RamanujanTau.Voronoi
