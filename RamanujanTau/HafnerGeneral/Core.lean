/-
# The core count for a general cusp form: `≥ T/(8r)` zeros of `Y` in `(0, 3T]`

The assembly of `HardyCountHafner.Main.core_count_linear`, with
* the normalised entire function `g(s) = n₀^s a_f(n₀)^{−1} L(f,s)` (`Window.exists_normalized`)
  in the rectangle, `|g(σ₁+iy) − 1| ≤ 1/4`;
* horizontal sides `F(c) = ∫_{p+1}^{σ₁} |g(x+ic)| dx ≤ (n₀^{σ₁}/|a_f(n₀)|) ∫ |L(f,x+ic)| dx`,
  averaged by `Horizontal.horizontal_mean`;
* `Windows.mean_sq_Iw`, `Windows.Iw_lower` for `Y` (`Z = Y·c`, `‖c‖ = 1`);
* `HardyCountHafner.many_zeros_of_mean_sq_exc` (Chebyshev, exceptional set, covering).

`r = 256 π^{2p+4} M² e⁶ / (c_Z² ρ₀²) + 128 C + 1` with `ρ₀ = |a_f(n₀)|/n₀^{p+1}`: a constant.
-/
import RamanujanTau.HafnerGeneral.Windows
import RamanujanTau.HardyCountHafner.Count

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
open scoped Real MatrixGroups

/-- Chebyshev on `[T, 2T]`. -/
lemma vol_ge_le {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) {T l B : ℝ}
    (hl : 0 < l) (hB : ∫ t in Icc T (2 * T), G t ≤ B) :
    volume.real ({t | l ≤ G t} ∩ Icc T (2 * T)) ≤ B / l := by
  have hint : Integrable G (volume.restrict (Icc T (2 * T))) := hG.integrableOn_Icc
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Icc T (2 * T)))
    (Eventually.of_forall hG0) hint l
  have hmeas : MeasurableSet {t | l ≤ G t} := measurableSet_le measurable_const hG.measurable
  rw [measureReal_restrict_apply hmeas] at hcheb
  rw [le_div_iff₀ hl]
  linarith

lemma Icc_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, f t = ∫ t in a..b, f t := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- Shifted dyadic means: `∫_T^{2T} F(t+s) dt ≤ 4 C T` for `|s| ≤ T/2`. -/
lemma integral_shift_le {F : ℝ → ℝ} (hFc : Continuous F) (hF0 : ∀ t, 0 ≤ F t) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ S : ℝ, 1 ≤ S → ∫ t in Icc S (2 * S), F t ≤ C * S) {T s : ℝ}
    (hT : 2 ≤ T) (hs : |s| ≤ T / 2) :
    ∫ t in Icc T (2 * T), F (t + s) ≤ 4 * C * T := by
  have hS : ∀ S : ℝ, 1 ≤ S → ∫ t in S..2 * S, F t ≤ C * S := by
    intro S hS1
    rw [← Icc_eq_interval (by linarith)]; exact hC S hS1
  have hs1 := neg_abs_le s
  have hs2 := le_abs_self s
  rw [Icc_eq_interval (by linarith), intervalIntegral.integral_comp_add_right (fun t => F t)]
  have hmono : ∫ t in (T + s)..(2 * T + s), F t ≤ ∫ t in (T / 2)..(4 * T), F t :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun t => hF0 t) (hFc.intervalIntegrable _ _)
  refine hmono.trans ?_
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := T) (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := T) (b := 2 * T)
      (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  have h1 := hS (T / 2) (by linarith)
  have h2 := hS T (by linarith)
  have h3 := hS (2 * T) (by linarith)
  rw [show 2 * (T / 2) = T by ring] at h1
  rw [show 2 * (2 * T) = 4 * T by ring] at h3
  nlinarith

/-- `1/cos^n(π/2 − 1/T) ≤ (πT/2)^n`. -/
lemma inv_cos_pow_le {T : ℝ} (hT : 1 ≤ T) (n : ℕ) :
    1 / Real.cos (π / 2 - 1 / T) ^ n ≤ (π * T / 2) ^ n := by
  have hTpos : 0 < T := by linarith
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hcos : 2 / π * (1 / T) ≤ Real.cos (π / 2 - 1 / T) := by
    rw [Real.cos_pi_div_two_sub]
    exact Real.mul_le_sin hinvpos.le (by linarith [Real.pi_gt_three])
  have hcpos : 0 < 2 / π * (1 / T) := by positivity
  have hc6 : (2 / π * (1 / T)) ^ n ≤ Real.cos (π / 2 - 1 / T) ^ n :=
    pow_le_pow_left₀ hcpos.le hcos n
  rw [div_le_iff₀ (pow_pos (hcpos.trans_le hcos) n)]
  have e : (π * T / 2) ^ n * (2 / π * (1 / T)) ^ n = 1 := by
    rw [← mul_pow]; field_simp; simp
  calc (1 : ℝ) = (π * T / 2) ^ n * (2 / π * (1 / T)) ^ n := e.symm
    _ ≤ _ := by gcongr

variable {p : ℕ}

/-- The normalised function `g(s) = n₀^s / a₀ · L(f,s)`. -/
noncomputable def gN (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (n₀ : ℕ) (a₀ : ℂ) (s : ℂ) : ℂ :=
  (n₀ : ℂ) ^ s / a₀ * fL f s

lemma gN_entire (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (a₀ : ℂ) :
    Differentiable ℂ (gN f n₀ a₀) := by
  have hn : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (show n₀ ≠ 0 by omega)
  exact ((differentiable_id.const_cpow (Or.inl hn)).div_const a₀).mul (fL_entire f (by omega))

lemma norm_gN (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (a₀ : ℂ)
    (σ t : ℝ) : ‖gN f n₀ a₀ ((σ : ℂ) + t * I)‖ =
      (n₀ : ℝ) ^ σ / ‖a₀‖ * ‖fL f ((σ : ℂ) + t * I)‖ := by
  rw [gN, norm_mul, norm_div, norm_natCast_cpow_of_pos (by omega)]
  simp

set_option maxHeartbeats 1000000 in
/-- **Core count**: `≥ T/(8r)` zeros of `Y` in `(0, 3T]`, with `r` a constant. -/
theorem core_count_linear (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2)
    (hf : f ≠ 0) {Y : ℝ → ℝ} {c : ℂ} (hRep : Rep f Y c) :
    ∃ r T₀ : ℝ, 0 < r ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ Y γ = 0) ∧ T / (8 * r) ≤ S.card := by
  have hk1 : 1 ≤ 2 * p + 2 := by omega
  have hp1 : 1 ≤ p := by omega
  obtain ⟨n₀, hn₀1, ha₀, σ₁, hσ₁, hρ⟩ := exists_normalized f hf hk1 (σa := (p : ℝ) + 2)
    (by push_cast; linarith) (ρ := 1 / 4) (by norm_num)
  set a₀ := coef f n₀ with ha₀def
  set g := gN f n₀ a₀ with hgdef
  have hgd : Differentiable ℂ g := gN_entire f hn₀1 a₀
  have hgc : Continuous g := hgd.continuous
  have hρg : ∀ y : ℝ, ‖g ((σ₁ : ℂ) + y * I) - 1‖ ≤ 1 / 4 := fun y => hρ y
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀1
  have ha₀n : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hκσ : (p : ℝ) + 1 ≤ σ₁ := by linarith
  -- horizontal sides of `g`
  obtain ⟨C₀, hC₀0, hC₀⟩ := horizontal_mean f hk (σ₁ := σ₁) hσ₁
  set B : ℝ := (n₀ : ℝ) ^ σ₁ / ‖a₀‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hFg : ∀ t, Fh g ((p : ℝ) + 1) σ₁ t ≤ B * Fh (fL f) ((p : ℝ) + 1) σ₁ t := by
    refine Fh_le_of_le hgc (fL_entire f hk1).continuous hκσ (fun σ hσ t => ?_)
    rw [hgdef, norm_gN f hn₀1]
    gcongr
    rw [hB]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn₀R hσ.2) ha₀n.le
  set C : ℝ := B * C₀ with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hFc : Continuous (Fh g ((p : ℝ) + 1) σ₁) := continuous_Fh hgc _ _
  have hF0 : ∀ t, 0 ≤ Fh g ((p : ℝ) + 1) σ₁ t := Fh_nonneg g hκσ
  have hC : ∀ S : ℝ, 1 ≤ S → ∫ t in Icc S (2 * S), Fh g ((p : ℝ) + 1) σ₁ t ≤ C * S := by
    intro S hS
    calc ∫ t in Icc S (2 * S), Fh g ((p : ℝ) + 1) σ₁ t
        ≤ ∫ t in Icc S (2 * S), B * Fh (fL f) ((p : ℝ) + 1) σ₁ t :=
          setIntegral_mono_on hFc.integrableOn_Icc
            (((continuous_Fh (fL_entire f hk1).continuous _ _).const_mul B).integrableOn_Icc)
            measurableSet_Icc fun t _ => hFg t
      _ = B * ∫ t in Icc S (2 * S), Fh (fL f) ((p : ℝ) + 1) σ₁ t := integral_const_mul _ _
      _ ≤ B * (C₀ * S) := by gcongr; exact hC₀ S hS
      _ = C * S := by rw [hCdef]; ring
  -- the critical line: `|g(p+1+it)| = |L(f,p+1+it)| / ρ₀`
  set ρ₀ : ℝ := ‖a₀‖ / (n₀ : ℝ) ^ ((p : ℝ) + 1) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hgL : ∀ t : ℝ, ρ₀ * ‖g ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ =
      ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ := by
    intro t
    rw [hgdef, norm_gN f hn₀1, hρ₀]
    have : 0 < (n₀ : ℝ) ^ ((p : ℝ) + 1) := by positivity
    field_simp
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Iw f hk
  have hcZ := cZ_pos p
  set D : ℝ := 256 * π ^ (2 * p + 4) * M ^ 2 * Real.exp 6 / (cZ p ^ 2 * ρ₀ ^ 2) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set r : ℝ := D + 128 * C + 1 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hDr : D ≤ r := by rw [hrdef]; linarith
  have hCr : 128 * C ≤ r := by rw [hrdef]; linarith
  refine ⟨r, max 2 (4 * r), hrpos, (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _),
    fun T hT => ?_⟩
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT4r : 4 * r ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  set α : ℝ := π / 2 - 1 / T with hα
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT1
  have hinvpos : 0 < 1 / T := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three]
  have hαπ : α < π / 2 := by rw [hα]; linarith
  obtain ⟨hIc, hIm⟩ := hmean Y c hRep α hα0 hαπ (2 * r) (by positivity)
  set P : ℝ := (T / 2) ^ ((p : ℝ) + 1 / 2) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  set A : ℝ := r * Real.exp (-3) * cZ p * P * (r * ρ₀) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  -- the exceptional set
  set E : Set ℝ := {t | r / 4 ≤ Fh g ((p : ℝ) + 1) σ₁ (t + -r)} ∪
    {t | r / 4 ≤ Fh g ((p : ℝ) + 1) σ₁ (t + r)} with hE
  have hEvol : volume.real (E ∩ Icc T (2 * T)) ≤ T / 4 := by
    have hs1 : |(-r)| ≤ T / 2 := by rw [abs_neg, abs_of_pos hrpos]; linarith
    have hs2 : |r| ≤ T / 2 := by rw [abs_of_pos hrpos]; linarith
    have hv1 := vol_ge_le (G := fun t => Fh g ((p : ℝ) + 1) σ₁ (t + -r))
      (hFc.comp (by fun_prop)) (fun t => hF0 _) (l := r / 4) (by positivity)
      (integral_shift_le hFc hF0 hC0 hC hT2 hs1)
    have hv2 := vol_ge_le (G := fun t => Fh g ((p : ℝ) + 1) σ₁ (t + r))
      (hFc.comp (by fun_prop)) (fun t => hF0 _) (l := r / 4) (by positivity)
      (integral_shift_le hFc hF0 hC0 hC hT2 hs2)
    rw [hE, union_inter_distrib_right]
    refine (measureReal_union_le _ _).trans ?_
    have hb : 4 * C * T / (r / 4) ≤ T / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hCr hTpos.le
      nlinarith
    linarith
  -- the lower bound off `E`
  have hlow : ∀ t₀ ∈ Icc T (2 * T), t₀ ∉ E →
      (∀ t ∈ Icc (t₀ - 2 * r) (t₀ + 2 * r), Y t ≠ 0) → A ≤ |Iw Y α (2 * r) t₀| := by
    intro t₀ ht₀ hnE hno
    have hn1 : Fh g ((p : ℝ) + 1) σ₁ (t₀ - r) ≤ ((t₀ + r) - (t₀ - r)) / 8 := by
      have : ¬ (r / 4 ≤ Fh g ((p : ℝ) + 1) σ₁ (t₀ + -r)) := fun h => hnE (Or.inl h)
      rw [← sub_eq_add_neg] at this
      push Not at this
      linarith
    have hn2 : Fh g ((p : ℝ) + 1) σ₁ (t₀ + r) ≤ ((t₀ + r) - (t₀ - r)) / 8 := by
      have : ¬ (r / 4 ≤ Fh g ((p : ℝ) + 1) σ₁ (t₀ + r)) := fun h => hnE (Or.inr h)
      push Not at this
      linarith
    have hw := window_lower_gen hgd hκσ hρg (by linarith) hn1 hn2
    have hwL : r * ρ₀ ≤ ∫ t in (t₀ - r)..(t₀ + r), ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ := by
      have e : (∫ t in (t₀ - r)..(t₀ + r), ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖) =
          ρ₀ * ∫ t in (t₀ - r)..(t₀ + r), ‖g ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun t _ => (hgL t).symm
      rw [e]
      have hw' : r ≤ ∫ t in (t₀ - r)..(t₀ + r), ‖g ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ := by
        have : ((t₀ + r) - (t₀ - r)) / 2 = r := by ring
        rw [this] at hw; exact hw
      calc r * ρ₀ = ρ₀ * r := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hw' hρ₀pos.le
    have hl := Iw_lower f hk hRep hT1 ht₀.1 ht₀.2 hrpos (by linarith) hno
    have hc : 0 ≤ r * Real.exp (-3) * cZ p * P := by positivity
    calc A = r * Real.exp (-3) * cZ p * P * (r * ρ₀) := rfl
      _ ≤ r * Real.exp (-3) * cZ p * P *
          ∫ t in (t₀ - r)..(t₀ + r), ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ :=
        mul_le_mul_of_nonneg_left hwL hc
      _ ≤ |Iw Y α (2 * r) t₀| := hl
  -- the mean-square comparison
  have hm : ∫ t₀ in Icc T (2 * T), Iw Y α (2 * r) t₀ ^ 2 ≤ A ^ 2 * T / 4 := by
    refine (hIm T hTpos).trans ?_
    have hS : 2 * π * M / Real.cos α ^ (p + 1) ≤ 2 * π * M * (π * T / 2) ^ (p + 1) := by
      have := inv_cos_pow_le hT1 (p + 1)
      rw [← hα] at this
      calc 2 * π * M / Real.cos α ^ (p + 1) = 2 * π * M * (1 / Real.cos α ^ (p + 1)) := by ring
        _ ≤ _ := by gcongr
    have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαπ⟩
    have hS0 : 0 ≤ 2 * π * M / Real.cos α ^ (p + 1) := by positivity
    have hP2 : P ^ 2 = (T / 2) ^ (2 * p + 1) := by
      rw [hP]; exact rpow_half_sq (by linarith) p
    have hDe : D * Real.exp (-6) * (cZ p ^ 2 * ρ₀ ^ 2) = 256 * π ^ (2 * p + 4) * M ^ 2 := by
      rw [hD]
      have hE6 : Real.exp 6 * Real.exp (-6) = 1 := by rw [← Real.exp_add]; simp
      have h0 : cZ p ^ 2 * ρ₀ ^ 2 ≠ 0 := by positivity
      field_simp
      rw [mul_assoc, hE6]; ring
    have hkey : 256 * π ^ (2 * p + 4) * M ^ 2 ≤ r * Real.exp (-6) * (cZ p ^ 2 * ρ₀ ^ 2) := by
      rw [← hDe]; gcongr
    have hAeq : A ^ 2 * T / 4 =
        (r * Real.exp (-6) * (cZ p ^ 2 * ρ₀ ^ 2)) * (r ^ 3 * (T / 2) ^ (2 * p + 2)) / 2 := by
      have hE : Real.exp (-3) ^ 2 = Real.exp (-6) := by
        rw [← Real.exp_nat_mul]; norm_num
      have h12 : (T / 2) ^ (2 * p + 2) = P ^ 2 * (T / 2) := by rw [hP2]; ring
      clear_value A P r
      rw [h12, ← hE, hA]; ring
    have hT12 : 0 ≤ r ^ 3 * (T / 2) ^ (2 * p + 2) := by positivity
    calc 4 * (2 * π * M / Real.cos α ^ (p + 1)) ^ 2 * (2 * r) ^ 3
        ≤ 4 * (2 * π * M * (π * T / 2) ^ (p + 1)) ^ 2 * (2 * r) ^ 3 := by gcongr
      _ = (256 * π ^ (2 * p + 4) * M ^ 2) * (r ^ 3 * (T / 2) ^ (2 * p + 2)) / 2 := by ring
      _ ≤ (r * Real.exp (-6) * (cZ p ^ 2 * ρ₀ ^ 2)) * (r ^ 3 * (T / 2) ^ (2 * p + 2)) / 2 := by
          gcongr
      _ = A ^ 2 * T / 4 := hAeq.symm
  obtain ⟨S, hS, hcard⟩ := HardyCountHafner.many_zeros_of_mean_sq_exc (Z := Y) hIc hTpos
    (by positivity : 0 < 2 * r) hEvol hlow hm hApos
  refine ⟨S, fun γ hγ => ?_, ?_⟩
  · obtain ⟨hγI, hz⟩ := hS γ hγ
    exact ⟨by linarith [hγI.1], by linarith [hγI.2], hz⟩
  · calc T / (8 * r) = T / (4 * (2 * r)) := by ring_nf
      _ ≤ S.card := hcard

end RamanujanTau.HafnerGeneral
