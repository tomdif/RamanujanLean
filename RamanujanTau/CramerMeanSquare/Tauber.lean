/-
# From the Mellin constant to the logarithmic Cramér asymptotic (Karamata, `ρ = 1`)

`tau_cramer_log_core`:  `(∫₁^X S(x)² x^{−25/2} dx) / log X → B/(4π²)`.

Discretize on the logarithmic scale: `a_n = ∫_{eⁿ}^{eⁿ⁺¹} S² x^{−25/2} ≥ 0`.  For `t > 0`,
`x^{−t} ∈ [e^{−(n+1)t}, e^{−nt}]` on the `n`-th block, so

    e^{−t} Σ aₙ e^{−nt} ≤ Φ(t/2) ≤ Σ aₙ e^{−nt},       Φ(δ) = ∫₁^∞ S² x^{−25/2−2δ},

and `tΦ(t/2) → B/(4π²)` by `delta_Phi_tendsto`.  Karamata's theorem
(`EisensteinReal.karamata`, `ρ = 1`) gives `Σ_{n≤N} aₙ / N → B/(4π²)`, and
`Σ_{n<⌊log X⌋} aₙ ≤ ∫₁^X ≤ Σ_{n≤⌊log X⌋} aₙ` finishes.
-/
import RamanujanTau.CramerMeanSquare.Limit
import RamanujanTau.EisensteinReal.Karamata

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Real MeasureTheory Set Filter Topology
open RamanujanTau.Voronoi (S psiR psiR_nonneg iI_psiR measurable_psiR)

/-- The Mellin transform `Φ(δ) = ∫₁^∞ S² x^{−25/2−2δ}`. -/
noncomputable def Phi (δ : ℝ) : ℝ := ∫ x in Ioi (1 : ℝ), S x ^ 2 * x ^ (-(25 / 2) - 2 * δ)

/-- The logarithmic blocks `aₙ = ∫_{eⁿ}^{eⁿ⁺¹} S² x^{−25/2}`. -/
noncomputable def ab (n : ℕ) : ℝ := ∫ x in exp n..exp (n + 1), psiR x

/-- The weighted integrand `S² x^{−25/2−t}`. -/
noncomputable def W (t x : ℝ) : ℝ := psiR x * x ^ (-t)

lemma one_le_exp_nat (n : ℕ) : 1 ≤ exp (n : ℝ) := Real.one_le_exp (Nat.cast_nonneg n)

lemma exp_nat_le_succ (n : ℕ) : exp (n : ℝ) ≤ exp ((n : ℝ) + 1) := Real.exp_le_exp.2 (by linarith)

lemma ab_nonneg (n : ℕ) : 0 ≤ ab n :=
  intervalIntegral.integral_nonneg (exp_nat_le_succ n) fun x hx =>
    psiR_nonneg (le_trans zero_le_one ((one_le_exp_nat n).trans hx.1))

lemma W_eq {t x : ℝ} (hx : 0 < x) : W t x = S x ^ 2 * x ^ (-(25 / 2) - 2 * (t / 2)) := by
  unfold W psiR
  rw [show -(25 / 2) - 2 * (t / 2) = -(25 / 2 : ℝ) + -t by ring, Real.rpow_add hx]
  ring

lemma W_nonneg (t : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ W t x :=
  mul_nonneg (psiR_nonneg hx) (Real.rpow_nonneg hx _)

lemma iI_W (t : ℝ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable (W t) volume a b := by
  have hc : ContinuousOn (fun x : ℝ => x ^ (-t)) (uIcc a b) := fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  exact (iI_psiR ha hab).mul_continuousOn hc

lemma intOn_W {t : ℝ} (ht : 0 < t) : IntegrableOn (W t) (Ioi 1) := by
  have h := RamanujanTau.Voronoi.tau_mean_square_convergent (σ := 23 / 4 + t / 2) (by linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [W_eq hx0]; congr 2; ring

lemma integral_W_eq {t : ℝ} : ∫ x in Ioi (1 : ℝ), W t x = Phi (t / 2) := by
  unfold Phi
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  exact W_eq (lt_trans one_pos hx)

/-- Block bounds. -/
lemma block_bounds {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ab n * exp (-(((n : ℝ) + 1) * t)) ≤ ∫ x in exp n..exp (n + 1), W t x ∧
      ∫ x in exp n..exp (n + 1), W t x ≤ ab n * exp (-((n : ℝ) * t)) := by
  have h1 := one_le_exp_nat n
  have hle := exp_nat_le_succ n
  have hab := iI_psiR h1 hle
  unfold ab
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
  constructor
  · refine intervalIntegral.integral_mono_on hle (hab.mul_const _) (iI_W t h1 hle) fun x hx => ?_
    have hx0 : 0 < x := lt_of_lt_of_le one_pos (h1.trans hx.1)
    unfold W
    refine mul_le_mul_of_nonneg_left ?_ (psiR_nonneg hx0.le)
    have : exp ((n : ℝ) + 1) ^ (-t) ≤ x ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith)
    rw [← Real.exp_mul] at this
    rw [show -(((n : ℝ) + 1) * t) = ((n : ℝ) + 1) * -t by ring]
    exact this
  · refine intervalIntegral.integral_mono_on hle (iI_W t h1 hle) (hab.mul_const _) fun x hx => ?_
    have hx0 : 0 < x := lt_of_lt_of_le one_pos (h1.trans hx.1)
    unfold W
    refine mul_le_mul_of_nonneg_left ?_ (psiR_nonneg hx0.le)
    have : x ^ (-t) ≤ exp (n : ℝ) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hx.1 (by linarith)
    rw [← Real.exp_mul] at this
    rw [show -((n : ℝ) * t) = (n : ℝ) * -t by ring]
    exact this

lemma sum_blocks (f : ℝ → ℝ) (hf : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable f volume a b)
    (N : ℕ) : ∑ n ∈ Finset.range N, ∫ x in exp n..exp (n + 1), f x = ∫ x in (1 : ℝ)..exp N, f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => exp (k : ℝ)) (n := N) (fun k _ => by
      have := hf (exp (k : ℝ)) (exp ((k + 1 : ℕ) : ℝ)) (one_le_exp_nat k)
        (Real.exp_le_exp.2 (by push_cast; linarith))
      simpa using this)
  simp only [Nat.cast_zero, Real.exp_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; rfl

lemma partial_le_Phi {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ∫ x in (1 : ℝ)..exp N, W t x ≤ Phi (t / 2) := by
  rw [← integral_W_eq, intervalIntegral.integral_of_le (one_le_exp_nat N)]
  refine setIntegral_mono_set (intOn_W ht) ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
    W_nonneg t (le_of_lt (lt_trans one_pos hx))

lemma tendsto_partial {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..exp N, W t x) atTop (𝓝 (Phi (t / 2))) := by
  rw [← integral_W_eq]
  exact intervalIntegral_tendsto_integral_Ioi 1 (intOn_W ht)
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)

lemma sum_range_le {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ab n * exp (-((n : ℝ) * t)) ≤ exp t * Phi (t / 2) := by
  have h1 : ∑ n ∈ Finset.range N, ab n * exp (-((n : ℝ) * t)) =
      exp t * ∑ n ∈ Finset.range N, ab n * exp (-(((n : ℝ) + 1) * t)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -((n : ℝ) * t) = t + -(((n : ℝ) + 1) * t) by ring, Real.exp_add]; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc ∑ n ∈ Finset.range N, ab n * exp (-(((n : ℝ) + 1) * t))
      ≤ ∑ n ∈ Finset.range N, ∫ x in exp n..exp (n + 1), W t x :=
        Finset.sum_le_sum fun n _ => (block_bounds ht n).1
    _ = ∫ x in (1 : ℝ)..exp N, W t x := sum_blocks (W t) (fun a b ha hab => iI_W t ha hab) N
    _ ≤ Phi (t / 2) := partial_le_Phi ht N

lemma summable_ab {t : ℝ} (ht : 0 < t) : Summable fun n : ℕ => ab n * exp (-((n : ℝ) * t)) :=
  summable_of_sum_range_le (fun n => mul_nonneg (ab_nonneg n) (Real.exp_pos _).le)
    (sum_range_le ht)

lemma Phi_le_tsum {t : ℝ} (ht : 0 < t) :
    Phi (t / 2) ≤ ∑' n : ℕ, ab n * exp (-((n : ℝ) * t)) := by
  refine le_of_tendsto' (tendsto_partial ht) fun N => ?_
  rw [← sum_blocks (W t) (fun a b ha hab => iI_W t ha hab) N]
  calc ∑ n ∈ Finset.range N, ∫ x in exp n..exp (n + 1), W t x
      ≤ ∑ n ∈ Finset.range N, ab n * exp (-((n : ℝ) * t)) :=
        Finset.sum_le_sum fun n _ => (block_bounds ht n).2
    _ ≤ _ := (summable_ab ht).sum_le_tsum _ fun n _ =>
        mul_nonneg (ab_nonneg n) (Real.exp_pos _).le

lemma tsum_le_Phi {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ, ab n * exp (-((n : ℝ) * t)) ≤ exp t * Phi (t / 2) :=
  Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (ab_nonneg n) (Real.exp_pos _).le)
    (sum_range_le ht)

/-- `t Φ(t/2) → B/(4π²)`. -/
lemma tendsto_tPhi : Tendsto (fun t : ℝ => t * Phi (t / 2)) (𝓝[>] 0)
    (𝓝 (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2))) := by
  have h2 : Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show (0 : ℝ) < t / 2
      exact div_pos (mem_Ioi.1 ht) (by norm_num)
  have h := (delta_Phi_tendsto.comp h2).const_mul 2
  have e : 2 * (RamanujanTau.MeanSquare.RS (25 / 2) / (8 * π ^ 2)) =
      RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2) := by
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp; ring
  rw [e] at h
  refine h.congr fun t => ?_
  simp only [Function.comp, Phi]
  ring

/-- **Karamata hypothesis.** -/
lemma karHyp_ab : RamanujanTau.EisensteinReal.KarHyp ab 1
    (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2)) where
  nonneg := ab_nonneg
  summ t ht := summable_ab ht
  lim := by
    have hup : Tendsto (fun t : ℝ => exp t * (t * Phi (t / 2))) (𝓝[>] 0)
        (𝓝 (1 * (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2)))) := by
      have he : Tendsto (fun t : ℝ => exp t) (𝓝[>] 0) (𝓝 1) := by
        have := Real.continuous_exp.tendsto 0
        rw [Real.exp_zero] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      exact he.mul tendsto_tPhi
    rw [one_mul] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_tPhi hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Phi_le_tsum ht0) ht0.le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      rw [Real.rpow_one]
      have := mul_le_mul_of_nonneg_left (tsum_le_Phi ht0) ht0.le
      linarith

lemma karamata_ab : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), ab n) / (N : ℝ)) atTop
    (𝓝 (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2))) := by
  have h := RamanujanTau.EisensteinReal.karamata karHyp_ab le_rfl
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.Gamma_two, div_one] at h
  refine h.congr fun N => ?_
  rw [Real.rpow_one]

/-- `∫₁^X S² x^{−25/2}` sits between consecutive partial sums. -/
lemma integral_between {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Finset.range ⌊Real.log X⌋₊, ab n ≤ ∫ x in (1 : ℝ)..X, psiR x ∧
      ∫ x in (1 : ℝ)..X, psiR x ≤ ∑ n ∈ Finset.range (⌊Real.log X⌋₊ + 1), ab n := by
  set N := ⌊Real.log X⌋₊ with hN
  have hX0 : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hNl : (N : ℝ) ≤ Real.log X := Nat.floor_le hlog0
  have hlN : Real.log X < N + 1 := Nat.lt_floor_add_one _
  have he1 : exp (N : ℝ) ≤ X := by
    calc exp (N : ℝ) ≤ exp (Real.log X) := Real.exp_le_exp.2 hNl
      _ = X := Real.exp_log hX0
  have he2 : X ≤ exp ((N : ℝ) + 1) := by
    calc X = exp (Real.log X) := (Real.exp_log hX0).symm
      _ ≤ exp ((N : ℝ) + 1) := Real.exp_le_exp.2 hlN.le
  have hii : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable psiR volume a b :=
    fun a b ha hab => iI_psiR ha hab
  have hsN := sum_blocks psiR hii N
  have hsplit : ∫ x in (1 : ℝ)..X, psiR x =
      (∫ x in (1 : ℝ)..exp N, psiR x) + ∫ x in exp N..X, psiR x :=
    (intervalIntegral.integral_add_adjacent_intervals (hii 1 _ le_rfl (one_le_exp_nat N))
      (hii _ X (one_le_exp_nat N) he1)).symm
  have hr0 : 0 ≤ ∫ x in exp N..X, psiR x :=
    intervalIntegral.integral_nonneg he1 fun x hx =>
      psiR_nonneg (le_trans zero_le_one ((one_le_exp_nat N).trans hx.1))
  have hr1 : ∫ x in exp N..X, psiR x ≤ ab N := by
    unfold ab
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ X (one_le_exp_nat N) he1)
      (hii X _ (le_trans (one_le_exp_nat N) he1) he2)]
    have := intervalIntegral.integral_nonneg (μ := volume) he2 fun x hx =>
      psiR_nonneg (le_trans zero_le_one (hX.trans hx.1))
    linarith
  have hab : ∑ n ∈ Finset.range N, ab n = ∫ x in (1 : ℝ)..exp N, psiR x := hsN
  rw [Finset.sum_range_succ, hab, hsplit]
  constructor <;> linarith

/-- **The logarithmic Cramér asymptotic.** -/
theorem tau_cramer_log_core :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, psiR x) / Real.log X) atTop
      (𝓝 (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2))) := by
  set A := RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2) with hA
  have hk := karamata_ab
  -- the lower sequence `Σ_{n<N} aₙ / (N+1)`
  have hlow : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ab n) / ((N : ℝ) + 1)) atTop (𝓝 A) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hr : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 2)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => 1 - 2 / ((N : ℝ) + 2)) atTop (𝓝 (1 - 0)) := by
        refine tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop ?_)
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      rw [sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards with N
      have : (0 : ℝ) < N + 2 := by positivity
      field_simp; ring
    have h := hk.mul hr
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    push_cast
    field_simp
    ring
  have hfl : Tendsto (fun X : ℝ => ⌊Real.log X⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop
  have hL := hlow.comp hfl
  have hU := hk.comp hfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hX1 : 1 ≤ X := le_trans (Real.one_le_exp zero_le_one) hX
    have hl1 : 1 ≤ Real.log X := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
    obtain ⟨h1, _⟩ := integral_between hX1
    have hlN : Real.log X < ⌊Real.log X⌋₊ + 1 := Nat.lt_floor_add_one _
    have hs0 : 0 ≤ ∑ n ∈ Finset.range ⌊Real.log X⌋₊, ab n :=
      Finset.sum_nonneg fun n _ => ab_nonneg n
    simp only [Function.comp]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have := mul_le_mul_of_nonneg_left hlN.le hs0
    nlinarith
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hX1 : 1 ≤ X := le_trans (Real.one_le_exp zero_le_one) hX
    have hl1 : 1 ≤ Real.log X := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
    obtain ⟨_, h2⟩ := integral_between hX1
    have hN1 : (1 : ℝ) ≤ ⌊Real.log X⌋₊ := by
      have : 1 ≤ ⌊Real.log X⌋₊ := Nat.le_floor (by exact_mod_cast hl1)
      exact_mod_cast this
    have hNl : (⌊Real.log X⌋₊ : ℝ) ≤ Real.log X := Nat.floor_le (by linarith)
    have hI0 : 0 ≤ ∫ x in (1 : ℝ)..X, psiR x :=
      intervalIntegral.integral_nonneg hX1 fun x hx => psiR_nonneg (by linarith [hx.1])
    simp only [Function.comp]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have := mul_le_mul_of_nonneg_left hNl hI0
    nlinarith

end RamanujanTau.CramerMeanSquare
