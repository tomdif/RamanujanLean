/-
# The exact Mellin constant: `δ · ∫₁^∞ S(x)² x^{−25/2−2δ} dx → B/(8π²)`

`delta_Phi_tendsto`, with `B = RS(25/2) = Σ τ(n)² n^{−25/2}`.

Write `σ = 23/4 + δ = 6 − y`, `y = 1/4 − δ`.  By `Voronoi` (Plancherel + Landau),
`Φ(δ) = (2π)⁻¹ ∫_ℝ Ψ_σ(u) du`, and `Ψ_σ` is even, so for any `t₀ ≥ 1`

    Φ(δ) = (2π)⁻¹ [ ∫_{−t₀}^{t₀} Ψ_σ + 2 ∫_{t₀}^∞ Ψ_σ ].

* the compact part is `O(1)` uniformly in `δ`, so it disappears after multiplying by `δ`;
* on `t ≥ t₀`, `Ψ_σ(t) = (2π)^{−4y} R(y,t) t^{−1−4δ} |L(25/4−δ+it)|²` (`Psi_eq`) with
  `|R − 1| ≤ ε` (`R_unif`);
* `4δ ∫_{t₀}^∞ t^{−1−4δ} |L(25/4−δ+it)|² dt → B` (`abel_param` fed by the uniform mean
  value `mean_square_unif` on `σ' = 25/4 − δ ∈ [31/5, 25/4]`).

So `δΦ(δ) → (2π)⁻¹ · 2 · (2π)⁻¹ · B/4 = B/(8π²)`.
-/
import RamanujanTau.CramerMeanSquare.Abel
import RamanujanTau.CramerMeanSquare.Unif
import RamanujanTau.CramerMeanSquare.Gamma
import RamanujanTau.Voronoi.Final

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.MeanSquare

/-- The line `σ' = 25/4 − η/4`. -/
noncomputable def fL (η t : ℝ) : ℝ := ‖tauL (((25 / 4 - η / 4 : ℝ) : ℂ) + t * I)‖ ^ 2

/-- Its mean-value constant `RS(2σ')`. -/
noncomputable def cL (η : ℝ) : ℝ := RS (2 * (25 / 4 - η / 4))

lemma continuous_fL (η : ℝ) : Continuous (fL η) :=
  RamanujanTau.MeanSquareLeft.continuous_normsq_line _

lemma fL_nonneg (η t : ℝ) : 0 ≤ fL η t := by unfold fL; positivity

lemma RS_le_62 {σ : ℝ} (hσ : 31 / 5 ≤ σ) : RS (2 * σ) ≤ RS (62 / 5) :=
  (summable_tau_sq (by linarith)).tsum_le_tsum (fun n => rpow_le_62 hσ n) summable_62

lemma B_pos : 0 < RS (25 / 2) := by
  have hs := summable_tau_sq (β := 25 / 2) (by norm_num)
  have h := hs.le_tsum 1 (fun n _ => by positivity)
  simp [RamanujanTau.tau_one] at h
  unfold RS; linarith

lemma eventually_le_fifth : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 / 5 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 5 by norm_num)] with η h
  exact ⟨h.1, h.2.le⟩

lemma tendsto_cL : Tendsto cL (𝓝[>] 0) (𝓝 (RS (25 / 2))) := by
  unfold cL RS
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ)) summable_62
    (f := fun η n => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * (25 / 4 - η / 4))))
    (g := fun n => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ)))
    (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [tau_zero]
      · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hc : Continuous fun η : ℝ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * (25 / 4 - η / 4))) :=
          continuous_const.mul ((Real.continuous_const_rpow hn0).comp (by fun_prop))
        have := hc.tendsto 0
        refine tendsto_nhdsWithin_of_tendsto_nhds ?_
        convert this using 3; norm_num)
    (by
      filter_upwards [eventually_le_fifth] with η hη n
      rw [Real.norm_of_nonneg (by positivity)]
      exact rpow_le_62 (σ := 25 / 4 - η / 4) (by linarith [hη.2]) n)
  exact h

/-- The Abelian hypothesis from the uniform mean value. -/
lemma hG_unif {t0 : ℝ} (ht0 : 1 ≤ t0) : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ T, t0 ≤ T → |(∫ t in t0..T, fL η t) - cL η * T| ≤ ε * T + D := by
  intro ε hε
  obtain ⟨E, hE, hEb⟩ := mean_square_unif
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 (hE.eventually (Iic_mem_nhds hε))
  set T2 : ℝ := max T1 t0 with hT2
  have hT21 : 1 ≤ T2 := ht0.trans (le_max_right _ _)
  set Ra : ℝ := RS (62 / 5) with hRa
  have hRa0 : 0 ≤ Ra := RS_nonneg _
  have hET2 : E T2 ≤ ε := hT1 T2 (le_max_left _ _)
  set D : ℝ := (Ra + ε) * T2 + Ra * T2 with hD
  refine ⟨D, by positivity, ?_⟩
  filter_upwards [eventually_le_fifth] with η hη T hT
  set σ : ℝ := 25 / 4 - η / 4 with hσ
  have hσ1 : 31 / 5 ≤ σ := by rw [hσ]; linarith [hη.2]
  have hσ2 : σ ≤ 25 / 4 := by rw [hσ]; linarith [hη.1]
  have hc0 : 0 ≤ cL η := RS_nonneg _
  have hcR : cL η ≤ Ra := RS_le_62 hσ1
  set F : ℝ → ℝ := fun T => ∫ t in (0 : ℝ)..T, fL η t with hF
  have hFm : ∀ a b : ℝ, 0 ≤ a → a ≤ b → F a ≤ F b := by
    intro a b ha hab
    simp only [hF]
    rw [← intervalIntegral.integral_add_adjacent_intervals ((continuous_fL η).intervalIntegrable 0 a)
      ((continuous_fL η).intervalIntegrable a b)]
    have := intervalIntegral.integral_nonneg (μ := volume) hab fun t _ => fL_nonneg η t
    linarith
  have hF0 : ∀ a : ℝ, 0 ≤ a → 0 ≤ F a := fun a ha =>
    intervalIntegral.integral_nonneg ha fun t _ => fL_nonneg η t
  have hbnd : ∀ T, 1 ≤ T → |F T - cL η * T| ≤ E T * T := by
    intro T hT
    have h := hEb σ hσ1 hσ2 T hT
    have hT0 : 0 < T := by linarith
    have e : F T - cL η * T = ((∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T - RS (2 * σ)) * T := by
      rw [sub_mul, div_mul_cancel₀ _ hT0.ne']; simp only [hF, fL, cL, hσ]
    rw [e, abs_mul, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_right h hT0.le
  have hFT2 : F T2 ≤ (Ra + ε) * T2 := by
    have h := (abs_le.1 (hbnd T2 hT21)).2
    have : cL η * T2 + E T2 * T2 ≤ (Ra + ε) * T2 := by
      have := mul_le_mul_of_nonneg_right (add_le_add hcR hET2) (by linarith : (0 : ℝ) ≤ T2)
      linarith
    linarith
  have ht00 : 0 ≤ t0 := by linarith
  have hsplit : ∫ t in t0..T, fL η t = F T - F t0 := by
    simp only [hF]
    rw [intervalIntegral.integral_interval_sub_left ((continuous_fL η).intervalIntegrable 0 T)
      ((continuous_fL η).intervalIntegrable 0 t0)]
  rw [hsplit]
  have hFt0 : F t0 ≤ F T2 := hFm t0 T2 ht00 (le_max_right _ _)
  have hFt00 := hF0 t0 ht00
  rcases le_or_gt T2 T with h | h
  · -- large `T`
    have hT1' : 1 ≤ T := hT21.trans h
    have hb := hbnd T hT1'
    have hET : E T ≤ ε := hT1 T ((le_max_left _ _).trans h)
    have hb' : |F T - cL η * T| ≤ ε * T := hb.trans
      (mul_le_mul_of_nonneg_right hET (by linarith))
    rw [abs_le] at hb' ⊢
    constructor
    · nlinarith
    · nlinarith
  · -- `t0 ≤ T < T2`
    have hFT : F T ≤ F T2 := hFm T T2 (by linarith) h.le
    have hFt0T : F t0 ≤ F T := hFm t0 T ht00 hT
    have hcT : cL η * T ≤ Ra * T2 := by
      have := mul_le_mul hcR h.le (by linarith) hRa0
      linarith
    have hcT0 : 0 ≤ cL η * T := mul_nonneg hc0 (by linarith)
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith

/-- **The Abelian limit**: `4δ ∫_{t₀}^∞ t^{−1−4δ} |L(25/4−δ+it)|² dt → B`. -/
theorem abel_L {t0 : ℝ} (ht0 : 1 ≤ t0) :
    Tendsto (fun δ : ℝ => 4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t) (𝓝[>] 0)
      (𝓝 (RS (25 / 2))) := by
  have h := abel_param (f := fL) (c := cL) (by linarith) continuous_fL fL_nonneg tendsto_cL
    (hG_unif ht0)
  have h4 : Tendsto (fun δ : ℝ => 4 * δ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((continuous_const_mul (4 : ℝ)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      show (0 : ℝ) < 4 * δ
      exact mul_pos (by norm_num) (mem_Ioi.1 hδ)
  exact h.comp h4

/-- The compact part. -/
lemma Psi_compact_bound' (t0 : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Icc (23 / 4 : ℝ) 6,
    ∀ u ∈ Icc (-t0) t0, RamanujanTau.Voronoi.Psi σ u ≤ M := by
  have hK : IsCompact (Icc (23 / 4 : ℝ) 6 ×ˢ Icc (-t0) t0) := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ × ℝ => RamanujanTau.Voronoi.Psi p.1 p.2)
      (Icc (23 / 4 : ℝ) 6 ×ˢ Icc (-t0) t0) := by
    unfold RamanujanTau.Voronoi.Psi
    refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
    refine ContinuousOn.div (tauLSeries_entire.continuous.comp (by fun_prop)).continuousOn
      (by fun_prop) fun p hp => RamanujanTau.Voronoi.ne_zero_of_re_pos (by linarith [hp.1.1]) p.2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun σ hσ u hu => ?_⟩
  have h := hM (σ, u) ⟨hσ, hu⟩
  rw [Real.norm_of_nonneg (RamanujanTau.Voronoi.Psi_nonneg _ _)] at h
  exact h.trans (le_max_left _ _)

/-- `Φ(δ) = (2π)⁻¹ ∫ Ψ_{23/4+δ}` (from `Voronoi`). -/
lemma Phi_eq_Psi {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    ∫ x in Ioi (1 : ℝ), RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) =
      (2 * π)⁻¹ * ∫ u : ℝ, RamanujanTau.Voronoi.Psi (23 / 4 + δ) u := by
  have e : ∀ x : ℝ, RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) =
      RamanujanTau.Voronoi.hR (23 / 4 + δ) x := by
    intro x; rw [RamanujanTau.Voronoi.hR]; congr 2; ring
  simp_rw [e]
  rw [RamanujanTau.Voronoi.integral_hR_eq (by linarith) (by linarith),
    RamanujanTau.Voronoi.integral_Fs_sq]

/-- Two-sided bounds for `δΦ(δ)`, for a fixed Stirling tolerance `ε`. -/
lemma delta_Phi_bounds {ε t0 M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (ht0 : 1 ≤ t0)
    (hR : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 4 → ∀ t : ℝ, t0 ≤ t → |Rf y t - 1| ≤ ε)
    (hM : ∀ σ ∈ Icc (23 / 4 : ℝ) 6, ∀ u ∈ Icc (-t0) t0, RamanujanTau.Voronoi.Psi σ u ≤ M)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    (1 - ε) * ((2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π)) *
        (4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t) ≤
      δ * ∫ x in Ioi (1 : ℝ), RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) ∧
    δ * ∫ x in Ioi (1 : ℝ), RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) ≤
      δ * ((2 * π)⁻¹ * (M * (2 * t0))) + (1 + ε) * ((2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π)) *
        (4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t) := by
  set y : ℝ := 1 / 4 - δ with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y < 1 / 4 := by rw [hy]; linarith
  have hσ : (23 / 4 + δ : ℝ) = 6 - y := by rw [hy]; ring
  set K : ℝ := (2 * π) ^ (-(4 * y)) with hK
  have hK0 : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  set g : ℝ → ℝ := fun t => t ^ (-1 - 4 * δ) * fL (4 * δ) t with hg
  have hPsi : ∀ t, t0 ≤ t → RamanujanTau.Voronoi.Psi (6 - y) t = K * Rf y t * g t := by
    intro t ht
    have ht0' : 0 < t := by linarith
    rw [Psi_eq hy0.le hy1.le ht0']
    simp only [hg, fL, hK]
    rw [show (6 + y : ℝ) = 25 / 4 - 4 * δ / 4 by rw [hy]; ring,
      show 4 * y - 2 = -1 - 4 * δ by rw [hy]; ring]
    ring
  have hg0 : ∀ t, t0 ≤ t → 0 ≤ g t := fun t ht => by
    simp only [hg]
    exact mul_nonneg (Real.rpow_pos_of_pos (by linarith) _).le (fL_nonneg _ _)
  have hRlo : ∀ t, t0 ≤ t → 1 - ε ≤ Rf y t := fun t ht => by
    have := (abs_le.1 (hR y hy0.le hy1.le t ht)).1; linarith
  have hRhi : ∀ t, t0 ≤ t → Rf y t ≤ 1 + ε := fun t ht => by
    have := (abs_le.1 (hR y hy0.le hy1.le t ht)).2; linarith
  -- integrability
  have hPi : Integrable (RamanujanTau.Voronoi.Psi (6 - y)) :=
    RamanujanTau.Voronoi.integrable_Psi hy0 hy1
  have hgi : IntegrableOn g (Ioi t0) := by
    have hb : IntegrableOn (fun t => (K * (1 - ε))⁻¹ * RamanujanTau.Voronoi.Psi (6 - y) t)
        (Ioi t0) := (hPi.integrableOn).const_mul _
    refine hb.mono' ?_ ?_
    · simp only [hg]
      exact ((Measurable.pow_const (by fun_prop) _).mul
        (continuous_fL _).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht' : t0 ≤ t := le_of_lt ht
      rw [Real.norm_of_nonneg (hg0 t ht'), hPsi t ht']
      have h1 : 0 < K * (1 - ε) := by have : 0 < 1 - ε := by linarith
                                      positivity
      rw [← mul_assoc, ← mul_assoc]
      have hgt := hg0 t ht'
      have : K * (1 - ε) * g t ≤ K * Rf y t * g t := by
        have := mul_le_mul_of_nonneg_left (hRlo t ht') hK0.le
        exact mul_le_mul_of_nonneg_right this hgt
      have hε' : (1 : ℝ) - ε ≠ 0 := by linarith
      calc g t = (K * (1 - ε))⁻¹ * (K * (1 - ε) * g t) := by field_simp
        _ ≤ (K * (1 - ε))⁻¹ * (K * Rf y t * g t) := by gcongr
        _ = _ := by ring
  -- the tail integral sandwich
  set J : ℝ := ∫ t in Ioi t0, g t with hJ
  have hTlo : (1 - ε) * K * J ≤ ∫ t in Ioi t0, RamanujanTau.Voronoi.Psi (6 - y) t := by
    rw [hJ, ← integral_const_mul]
    refine setIntegral_mono_on (hgi.const_mul _) hPi.integrableOn measurableSet_Ioi fun t ht => ?_
    have ht' : t0 ≤ t := le_of_lt ht
    rw [hPsi t ht']
    have := mul_le_mul_of_nonneg_left (hRlo t ht') hK0.le
    have := mul_le_mul_of_nonneg_right this (hg0 t ht')
    linarith
  have hThi : ∫ t in Ioi t0, RamanujanTau.Voronoi.Psi (6 - y) t ≤ (1 + ε) * K * J := by
    rw [hJ, ← integral_const_mul]
    refine setIntegral_mono_on hPi.integrableOn (hgi.const_mul _) measurableSet_Ioi fun t ht => ?_
    have ht' : t0 ≤ t := le_of_lt ht
    rw [hPsi t ht']
    have := mul_le_mul_of_nonneg_left (hRhi t ht') hK0.le
    have := mul_le_mul_of_nonneg_right this (hg0 t ht')
    linarith
  -- the compact part
  have hsplit := RamanujanTau.Voronoi.even_split (RamanujanTau.Voronoi.continuous_Psi
    (σ := 6 - y) (by linarith)) (RamanujanTau.Voronoi.Psi_neg _) (by linarith : (0 : ℝ) ≤ t0)
    hPi.integrableOn
  have hC0 : 0 ≤ ∫ u in Icc (-t0) t0, RamanujanTau.Voronoi.Psi (6 - y) u :=
    setIntegral_nonneg measurableSet_Icc fun u _ => RamanujanTau.Voronoi.Psi_nonneg _ _
  have hC1 : ∫ u in Icc (-t0) t0, RamanujanTau.Voronoi.Psi (6 - y) u ≤ M * (2 * t0) := by
    have hb : ∫ u in Icc (-t0) t0, RamanujanTau.Voronoi.Psi (6 - y) u ≤
        ∫ _ in Icc (-t0) t0, M := by
      refine setIntegral_mono_on hPi.integrableOn ?_ measurableSet_Icc fun u hu => ?_
      · exact integrableOn_const (by simp [Real.volume_Icc]) (by simp)
      · exact hM (6 - y) ⟨by linarith, by linarith⟩ u hu
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)] at hb
    linarith
  have hΦ := Phi_eq_Psi hδ0 (by linarith)
  rw [hσ, hsplit.2.2] at hΦ
  rw [hΦ]
  have hπ : 0 < π := Real.pi_pos
  have hJe : 4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t = 4 * δ * J := rfl
  rw [hJe]
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht => hg0 t (le_of_lt ht)
  constructor
  · have : (1 - ε) * (K / (4 * π)) * (4 * δ * J) = δ * ((2 * π)⁻¹ * (2 * ((1 - ε) * K * J))) := by
      field_simp <;> ring
    rw [this]
    gcongr <;> linarith
  · have : δ * ((2 * π)⁻¹ * (M * (2 * t0))) + (1 + ε) * (K / (4 * π)) * (4 * δ * J) =
        δ * ((2 * π)⁻¹ * (M * (2 * t0) + 2 * ((1 + ε) * K * J))) := by
      field_simp <;> ring
    rw [this]
    gcongr <;> linarith

/-- **Exact Mellin constant**: `δ ∫₁^∞ S(x)² x^{−25/2−2δ} dx → B/(8π²)`. -/
theorem delta_Phi_tendsto :
    Tendsto (fun δ : ℝ => δ * ∫ x in Ioi (1 : ℝ),
        RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ)) (𝓝[>] 0)
      (𝓝 (RS (25 / 2) / (8 * π ^ 2))) := by
  set L : ℝ := RS (25 / 2) / (8 * π ^ 2) with hL
  have hL0 : 0 < L := by rw [hL]; have := B_pos; positivity
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 / 8 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with δ h
    exact ⟨h.1, h.2.le⟩
  have hKl : Tendsto (fun δ : ℝ => (2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π)) (𝓝[>] 0)
      (𝓝 ((2 * π)⁻¹ / (4 * π))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π) :=
      ((Real.continuous_const_rpow (by positivity)).comp (by fun_prop)).div_const _
    convert hc.tendsto 0 using 2
    rw [show (-(4 * (1 / 4 - 0)) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hKv : (2 * π)⁻¹ / (4 * π) * RS (25 / 2) = L := by
    rw [hL]
    field_simp <;> ring
  have hδ0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  rw [tendsto_order]
  constructor
  · intro l hl
    rcases lt_or_ge l 0 with hl0 | hl0
    · filter_upwards [hpos] with δ hδ
      have : 0 ≤ δ * ∫ x in Ioi (1 : ℝ), RamanujanTau.Voronoi.S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) := by
        refine mul_nonneg hδ.1.le (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
        have : 0 < x := lt_trans one_pos hx
        positivity
      linarith
    · set ε : ℝ := (L - l) / (2 * L) with hε
      have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
      have hε1 : ε ≤ 1 / 2 := by
        rw [hε, div_le_iff₀ (by linarith)]; linarith
      obtain ⟨t0, ht0, hR⟩ := R_unif ε hε0
      obtain ⟨M, _, hM⟩ := Psi_compact_bound' t0
      have hlow : Tendsto (fun δ : ℝ => (1 - ε) * ((2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π)) *
          (4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t)) (𝓝[>] 0)
          (𝓝 ((1 - ε) * L)) := by
        have h := ((tendsto_const_nhds (x := 1 - ε)).mul hKl).mul (abel_L ht0)
        rw [← hKv]; convert h using 2; ring
      have hlt : l < (1 - ε) * L := by
        rw [hε]; field_simp; linarith
      filter_upwards [hlow.eventually (lt_mem_nhds hlt), hpos] with δ h1 h2
      exact lt_of_lt_of_le h1 (delta_Phi_bounds hε0 hε1 ht0 hR hM h2.1 h2.2).1
  · intro u hu
    set ε : ℝ := min (1 / 2) ((u - L) / (2 * L)) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    obtain ⟨t0, ht0, hR⟩ := R_unif ε hε0
    obtain ⟨M, _, hM⟩ := Psi_compact_bound' t0
    have hup : Tendsto (fun δ : ℝ => δ * ((2 * π)⁻¹ * (M * (2 * t0))) +
        (1 + ε) * ((2 * π) ^ (-(4 * (1 / 4 - δ))) / (4 * π)) *
        (4 * δ * ∫ t in Ioi t0, t ^ (-1 - 4 * δ) * fL (4 * δ) t)) (𝓝[>] 0)
        (𝓝 (0 * ((2 * π)⁻¹ * (M * (2 * t0))) + (1 + ε) * L)) := by
      have h := (hδ0.mul_const ((2 * π)⁻¹ * (M * (2 * t0)))).add
        (((tendsto_const_nhds (x := 1 + ε)).mul hKl).mul (abel_L ht0))
      rw [← hKv]; convert h using 2; ring
    have hlt : 0 * ((2 * π)⁻¹ * (M * (2 * t0))) + (1 + ε) * L < u := by
      have : ε * L ≤ (u - L) / (2 * L) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
      have e : (u - L) / (2 * L) * L = (u - L) / 2 := by field_simp
      linarith
    filter_upwards [hup.eventually (gt_mem_nhds hlt), hpos] with δ h1 h2
    exact lt_of_le_of_lt (delta_Phi_bounds hε0 hε1 ht0 hR hM h2.1 h2.2).2 h1

end RamanujanTau.CramerMeanSquare
