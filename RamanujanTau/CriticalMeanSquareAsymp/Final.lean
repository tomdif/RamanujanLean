/-
# (A) The sharp asymptotic `∫_0^T |L(Δ, 6+it)|² dt ~ 2c · T log T`

`c = (3/π)(4π)¹²‖Δ‖²/11!` is Rankin's constant (`RankinExact.rankinSelberg_exact`).

Karamata (`KarC`) for `m(x) = x¹¹|L(6+ix)|²`, `ρ = 12`, `K = Kc` (`Laplace`), applied to the
test function `gK(x)·Q_ε(x)` with `Q_ε(e^{-u}) = max(u, ε)^{-11}` (`u ∈ [0,1]`), gives at
`t = 1/T`

    T^{11} (F(T) − F(εT)) ≤ S_{1/T} ≤ T^{11} F(T),     F(T) = ∫_0^T |L(6+it)|² dt,

and `S_{1/T}/(T¹² log T) → Kc Λ_ε` with `(1−ε)/11! ≤ Λ_ε ≤ 1/11!`.  The a-priori bound
`F(εT) ≤ C εT log T` (`CriticalMeanSquare.critical_mean_square_upper`) closes the gap as `ε → 0`.
-/
import RamanujanTau.CriticalMeanSquareAsymp.Laplace
import RamanujanTau.RankinExact.Main

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare RamanujanTau.CriticalMeanSquareLower
open RamanujanTau.EisensteinReal (Lam kw gK)
open scoped Real

/-- `m(x) = x¹¹ |L(6+ix)|²`. -/
noncomputable def mL (x : ℝ) : ℝ := x ^ 11 * Lsq x

lemma karHyp_mL : KarHypC mL 12 Kc where
  nonneg x hx := by unfold mL; have := Lsq_nonneg x; positivity
  integ t ht := integrableOn_Lap ht
  lim := by
    refine laplace_asymptotic.congr fun t => ?_
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl

/-! ### The test function `Q_ε` -/

/-- `Q_ε(x) = max(−log max(x, e⁻¹/2), ε)^{-11}`. -/
noncomputable def Qe (ε x : ℝ) : ℝ := ((max (-Real.log (max x (Real.exp (-1) / 2))) ε)⁻¹) ^ 11

lemma continuous_Qe {ε : ℝ} (hε : 0 < ε) : Continuous (Qe ε) := by
  unfold Qe
  have h1 : Continuous fun x : ℝ => max x (Real.exp (-1) / 2) := continuous_id.max continuous_const
  have h2 : Continuous fun x : ℝ => Real.log (max x (Real.exp (-1) / 2)) :=
    h1.log fun x => (lt_max_of_lt_right (by positivity : (0 : ℝ) < Real.exp (-1) / 2)).ne'
  exact ((h2.neg.max continuous_const).inv₀ fun x =>
    (lt_max_of_lt_right hε).ne').pow 11

lemma Qe_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ Qe ε x := by
  unfold Qe
  have : 0 < max (-Real.log (max x (Real.exp (-1) / 2))) ε := lt_max_of_lt_right hε
  positivity

lemma Qe_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : Qe ε x ≤ (ε⁻¹) ^ 11 := by
  unfold Qe
  have h : ε ≤ max (-Real.log (max x (Real.exp (-1) / 2))) ε := le_max_right _ _
  have : 0 < max (-Real.log (max x (Real.exp (-1) / 2))) ε := lt_max_of_lt_right hε
  gcongr

lemma Qe_exp {ε u : ℝ} (hu1 : u ≤ 1) : Qe ε (Real.exp (-u)) = ((max u ε)⁻¹) ^ 11 := by
  unfold Qe
  have h : Real.exp (-1) / 2 ≤ Real.exp (-u) := by
    have h1 : Real.exp (-1) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 0 < Real.exp (-1) := Real.exp_pos _
    linarith
  rw [max_eq_left h, Real.log_exp, neg_neg]

lemma gK_exp {u : ℝ} : gK (Real.exp (-u)) = if u ≤ 1 then (Real.exp (-u))⁻¹ else 0 := by
  unfold gK
  by_cases h : u ≤ 1
  · rw [if_pos (Real.exp_le_exp.mpr (by linarith)), if_pos h]
  · rw [if_neg (fun h' => h (by have := Real.exp_le_exp.mp h'; linarith)), if_neg h]

/-! ### `Λ_ε` -/

lemma Lam_gQ_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) / (Nat.factorial 11 : ℝ) ≤ Lam 12 (fun x => gK x * Qe ε x) ∧
      Lam 12 (fun x => gK x * Qe ε x) ≤ 1 / (Nat.factorial 11 : ℝ) := by
  set φ : ℝ → ℝ := fun u => (u / max u ε) ^ 11 with hφ
  have hφc : Continuous φ := (continuous_id.div (continuous_id.max continuous_const) fun u =>
    (lt_max_of_lt_right hε).ne').pow 11
  have hpt : ∀ u ∈ Ioi (0 : ℝ), gK (Real.exp (-u)) * Qe ε (Real.exp (-u)) * kw 12 u =
      (Iic (1 : ℝ)).indicator φ u := by
    intro u hu
    have hu0 : 0 < u := hu
    rw [gK_exp]
    unfold kw
    rw [show (12 : ℝ) - 1 = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    by_cases h1 : u ≤ 1
    · rw [if_pos h1, Qe_exp h1, indicator_of_mem (show u ∈ Iic (1 : ℝ) from h1), hφ]
      simp only
      have : 0 < max u ε := lt_max_of_lt_right hε
      field_simp
    · rw [if_neg h1, indicator_of_notMem (show u ∉ Iic (1 : ℝ) from h1)]; ring
  have hI : ∫ u in Ioi 0, gK (Real.exp (-u)) * Qe ε (Real.exp (-u)) * kw 12 u =
      ∫ u in (0 : ℝ)..1, φ u := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic, intervalIntegral.integral_of_le zero_le_one]
  have hΓ : Real.Gamma 12 = (Nat.factorial 11 : ℝ) := by
    rw [show (12 : ℝ) = ((11 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  have hφ1 : ∀ u, 0 ≤ u → φ u ≤ 1 := by
    intro u hu
    simp only [hφ]
    have hm : 0 < max u ε := lt_max_of_lt_right hε
    exact pow_le_one₀ (div_nonneg hu hm.le) ((div_le_one hm).mpr (le_max_left _ _))
  have hφ0 : ∀ u, 0 ≤ u → 0 ≤ φ u := by
    intro u hu
    simp only [hφ]
    have hm : 0 < max u ε := lt_max_of_lt_right hε
    positivity
  have hup : ∫ u in (0 : ℝ)..1, φ u ≤ 1 := by
    have := intervalIntegral.integral_mono_on zero_le_one (hφc.intervalIntegrable 0 1)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun u hu => hφ1 u hu.1
    simpa using this
  have hlo : 1 - ε ≤ ∫ u in (0 : ℝ)..1, φ u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable 0 ε)
      (hφc.intervalIntegrable ε 1)]
    have h0 : 0 ≤ ∫ u in (0 : ℝ)..ε, φ u :=
      intervalIntegral.integral_nonneg hε.le fun u hu => hφ0 u hu.1
    have h1 : ∫ u in ε..1, φ u = ∫ u in ε..1, (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hε1.le] at hu
      simp only [hφ]
      rw [max_eq_left hu.1, div_self (by linarith [hu.1]), one_pow]
    rw [h1]
    simp
    linarith
  unfold Lam
  rw [hI, hΓ]
  have hf : (0 : ℝ) < (Nat.factorial 11 : ℝ) := by positivity
  constructor
  · exact div_le_div_of_nonneg_right hlo hf.le
  · exact div_le_div_of_nonneg_right hup hf.le

/-! ### `S_{1/T}` in terms of `F` -/

lemma SC_bounds {ε T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) :
    T ^ 11 * ∫ x in Ioc (ε * T) T, Lsq x ≤ SC mL (fun x => gK x * Qe ε x) T⁻¹ ∧
      SC mL (fun x => gK x * Qe ε x) T⁻¹ ≤ T ^ 11 * ∫ x in Ioc 0 T, Lsq x := by
  set I : ℝ → ℝ := fun x => mL x * Real.exp (-(x * T⁻¹)) *
    (gK (Real.exp (-(x * T⁻¹))) * Qe ε (Real.exp (-(x * T⁻¹)))) with hIdef
  have hεT : 0 < ε * T := by positivity
  -- pointwise description
  have hI : ∀ x, 0 < x → x ≤ T → I x = x ^ 11 * Lsq x * ((max (x / T) ε)⁻¹) ^ 11 := by
    intro x hx hxT
    have hu : x * T⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hT]; exact hxT
    simp only [hIdef, mL]
    rw [gK_exp, if_pos hu, Qe_exp hu, ← div_eq_mul_inv x T]
    have := Real.exp_pos (-(x / T))
    field_simp
  have hI0 : ∀ x, T < x → I x = 0 := by
    intro x hx
    have hu : ¬ x * T⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hT]; linarith
    simp only [hIdef]
    rw [gK_exp, if_neg hu]; ring
  have hInn : ∀ x, 0 < x → 0 ≤ I x := by
    intro x hx
    simp only [hIdef, mL]
    have := Lsq_nonneg x
    have := Qe_nonneg hε (Real.exp (-(x * T⁻¹)))
    have hg : 0 ≤ gK (Real.exp (-(x * T⁻¹))) := by
      rw [gK_exp]; split_ifs
      · exact (inv_pos.2 (Real.exp_pos _)).le
      · exact le_rfl
    positivity
  have hIi : IntegrableOn I (Ioi 0) := by
    have := integrableOn_SC karHyp_mL
      (f := fun x => gK x * Qe ε x) ?_ (inv_pos.2 hT)
    · refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [hIdef]
    · obtain ⟨hm1, B, hB⟩ := EisensteinReal.adm_gK
      refine ⟨hm1.mul (continuous_Qe hε).measurable, B * (ε⁻¹) ^ 11, fun x hx => ?_⟩
      rw [abs_mul, abs_of_nonneg (Qe_nonneg hε x)]
      exact mul_le_mul (hB x hx) (Qe_le hε x) (Qe_nonneg hε x) ((abs_nonneg _).trans (hB x hx))
  have hSC : SC mL (fun x => gK x * Qe ε x) T⁻¹ = ∫ x in Ioc 0 T, I x := by
    have e1 : SC mL (fun x => gK x * Qe ε x) T⁻¹ = ∫ x in Ioi 0, I x := by
      unfold SC; rfl
    rw [e1, ← Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hIi.mono_set Ioc_subset_Ioi_self) (hIi.mono_set (Ioi_subset_Ioi hT.le)),
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioi T) (fun x hx => hI0 x hx), add_zero]
  have hLi : ∀ a b : ℝ, IntegrableOn Lsq (Ioc a b) := fun a b =>
    (continuous_Lsq.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  rw [hSC]
  constructor
  · have hsub : ∫ x in Ioc (ε * T) T, I x ≤ ∫ x in Ioc 0 T, I x :=
      setIntegral_mono_set (hIi.mono_set Ioc_subset_Ioi_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hInn x hx.1)
        (Eventually.of_forall (Ioc_subset_Ioc_left hεT.le))
    refine le_trans (le_of_eq ?_) hsub
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx0 : 0 < x := lt_trans hεT hx.1
    rw [hI x hx0 hx.2]
    have hm : max (x / T) ε = x / T := max_eq_left (by rw [le_div_iff₀ hT]; exact hx.1.le)
    rw [hm]
    field_simp
  · rw [← integral_const_mul]
    refine setIntegral_mono_on (hIi.mono_set Ioc_subset_Ioi_self) ((hLi 0 T).const_mul _)
      measurableSet_Ioc fun x hx => ?_
    rw [hI x hx.1 hx.2]
    have hL := Lsq_nonneg x
    have hm : x / T ≤ max (x / T) ε := le_max_left _ _
    have hxT : 0 < x / T := div_pos hx.1 hT
    have h1 : x ^ 11 * ((max (x / T) ε)⁻¹) ^ 11 ≤ T ^ 11 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg hx.1.le (inv_nonneg.2 (le_trans hxT.le hm)))
      rw [← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le hxT hm)]
      calc x = T * (x / T) := by field_simp
        _ ≤ T * max (x / T) ε := by gcongr
    calc x ^ 11 * Lsq x * ((max (x / T) ε)⁻¹) ^ 11 = x ^ 11 * ((max (x / T) ε)⁻¹) ^ 11 * Lsq x := by
          ring
      _ ≤ T ^ 11 * Lsq x := mul_le_mul_of_nonneg_right h1 hL

/-! ### The constants -/

/-- Rankin's constant `c = (3/π)(4π)¹²‖Δ‖²/11!`, as in `RankinExact.rankinSelberg_exact`. -/
noncomputable def rankinC : ℝ :=
  3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ)

/-- Good's constant `c_Δ = 2c`. -/
noncomputable def cDelta : ℝ := 2 * rankinC

lemma Kc_div_eq : Kc / (Nat.factorial 11 : ℝ) = cDelta := by
  unfold Kc cDelta rankinC
  field_simp
  ring

lemma Kc_nonneg : 0 ≤ Kc := KC_nonneg karHyp_mL

/-- **(A) Good's theorem (1982) for `Δ`:**
`∫_0^T |L(Δ, 6+it)|² dt / (T log T) → 2c`, `c = (3/π)(4π)¹²‖Δ‖²/11!` (Rankin's constant). -/
theorem critical_mean_square_asymptotic :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2) / (T * Real.log T)) atTop
      (𝓝 cDelta) := by
  obtain ⟨CU, hCU0, hCU⟩ := critical_mean_square_upper
  set F : ℝ → ℝ := fun T => ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 with hF
  have hFioc : ∀ T, F T = ∫ x in Ioc 0 T, Lsq x := fun T => by
    simp only [hF]; rw [integral_Icc_eq_integral_Ioc]; rfl
  have hLi : ∀ a b : ℝ, IntegrableOn Lsq (Ioc a b) := fun a b =>
    (continuous_Lsq.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have hdiff : ∀ a T : ℝ, 0 ≤ a → a ≤ T → ∫ x in Ioc a T, Lsq x = F T - F a := by
    intro a T ha haT
    rw [hFioc, hFioc, ← intervalIntegral.integral_of_le haT,
      ← intervalIntegral.integral_of_le (ha.trans haT), ← intervalIntegral.integral_of_le ha]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (continuous_Lsq.intervalIntegrable 0 a) (continuous_Lsq.intervalIntegrable a T)]
    ring
  have hF0 : ∀ T, 0 ≤ F T := fun T => setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _
  set cD := cDelta
  have hcD : cD = Kc / (Nat.factorial 11 : ℝ) := Kc_div_eq.symm
  have hf : (0 : ℝ) < (Nat.factorial 11 : ℝ) := by positivity
  rw [Metric.tendsto_atTop]
  intro e he
  set ε : ℝ := min (1 / 2) (e / (4 * (Kc / (Nat.factorial 11 : ℝ) + CU + 1))) with hεdef
  have hKf : 0 ≤ Kc / (Nat.factorial 11 : ℝ) := div_nonneg Kc_nonneg hf.le
  have hden : 0 < 4 * (Kc / (Nat.factorial 11 : ℝ) + CU + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos he hden)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεe : ε * (Kc / (Nat.factorial 11 : ℝ) + CU) ≤ e / 4 := by
    have h1 : ε ≤ e / (4 * (Kc / (Nat.factorial 11 : ℝ) + CU + 1)) := min_le_right _ _
    rw [le_div_iff₀ hden] at h1
    nlinarith
  -- the Karamata limit at `t = 1/T`
  have hconv := convC_gKQ karHyp_mL (by norm_num) (continuous_Qe hε) (Qe_nonneg hε) (Qe_le hε)
  unfold ConvC at hconv
  have hZ := hconv.comp tendsto_inv_atTop_nhdsGT_zero
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hZ (e / 4) (by positivity)
  obtain ⟨hΛlo, hΛhi⟩ := Lam_gQ_bounds hε hε1
  set Λε := Lam 12 (fun x => gK x * Qe ε x)
  refine ⟨max (max N₁ 2) (Real.exp 1 / ε), fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTN : N₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTe : Real.exp 1 / ε ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hTL : 0 < T * Real.log T := mul_pos hT0 hlogT
  have hZT := hN₁ T hTN
  simp only [Function.comp] at hZT
  rw [one_div (T⁻¹), inv_inv, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.dist_eq] at hZT
  set S := SC mL (fun x => gK x * Qe ε x) T⁻¹
  set Z := T⁻¹ ^ 12 / Real.log T * S with hZ
  obtain ⟨hS1, hS2⟩ := SC_bounds hε hε1 hT0
  rw [hdiff (ε * T) T (by positivity) (by nlinarith)] at hS1
  rw [← hFioc] at hS2
  -- `Z` vs `F/(T log T)`
  have hZeq : Z = S / (T ^ 12 * Real.log T) := by
    rw [hZ]; field_simp
  have hZup : Z ≤ F T / (T * Real.log T) := by
    rw [hZeq, div_le_div_iff₀ (by positivity) hTL]
    calc S * (T * Real.log T) ≤ T ^ 11 * F T * (T * Real.log T) := by gcongr
      _ = F T * (T ^ 12 * Real.log T) := by ring
  have hZlo : (F T - F (ε * T)) / (T * Real.log T) ≤ Z := by
    rw [hZeq, div_le_div_iff₀ hTL (by positivity)]
    calc (F T - F (ε * T)) * (T ^ 12 * Real.log T) = T ^ 11 * (F T - F (ε * T)) *
        (T * Real.log T) := by ring
      _ ≤ S * (T * Real.log T) := by gcongr
  -- a priori bound for `F(εT)`
  have hεT : Real.exp 1 ≤ ε * T := by
    rw [div_le_iff₀ hε] at hTe; linarith
  have hFε : F (ε * T) / (T * Real.log T) ≤ CU * ε := by
    have h1 := hCU (ε * T) hεT
    have h2 : Real.log (ε * T) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [div_le_iff₀ hTL]
    calc F (ε * T) ≤ CU * (ε * T) * Real.log (ε * T) := h1
      _ ≤ CU * (ε * T) * Real.log T := by gcongr
      _ = CU * ε * (T * Real.log T) := by ring
  have hsplitF : F T / (T * Real.log T) =
      (F T - F (ε * T)) / (T * Real.log T) + F (ε * T) / (T * Real.log T) := by ring
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hZT
  have hKΛlo : Kc * ((1 - ε) / (Nat.factorial 11 : ℝ)) ≤ Kc * Λε :=
    mul_le_mul_of_nonneg_left hΛlo Kc_nonneg
  have hKΛhi : Kc * Λε ≤ Kc * (1 / (Nat.factorial 11 : ℝ)) :=
    mul_le_mul_of_nonneg_left hΛhi Kc_nonneg
  have e1 : Kc * ((1 - ε) / (Nat.factorial 11 : ℝ)) = cD - ε * (Kc / (Nat.factorial 11 : ℝ)) := by
    rw [hcD]; ring
  have e2 : Kc * (1 / (Nat.factorial 11 : ℝ)) = cD := by rw [hcD]; ring
  have hFε0 : 0 ≤ F (ε * T) / (T * Real.log T) := div_nonneg (hF0 _) hTL.le
  constructor
  · nlinarith
  · nlinarith

/-- The constant, spelled out. -/
theorem cDelta_eq : cDelta = 2 * (3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq /
    (Nat.factorial 11 : ℝ)) := rfl

/-- Normalization check: `cDelta / 2` is exactly the constant in `RankinExact.rankinSelberg_exact`. -/
theorem rankin_normalization : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - cDelta / 2 * N| ≤
      C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC⟩ := RankinExact.rankinSelberg_exact
  refine ⟨C, fun N hN => ?_⟩
  have e : cDelta / 2 = 3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) := by
    unfold cDelta rankinC; ring
  rw [e]; exact hC N hN

end RamanujanTau.CriticalMeanSquareAsymp
