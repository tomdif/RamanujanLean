/-
# An abstract Tauberian step: from a Laplace asymptotic with a `log` to `∫_0^T g ~ c T log T`

Let `g ≥ 0` be continuous on `ℝ`, `n : ℕ`, and suppose that

    λ^{n+1} ∫_0^∞ x^n g(x) e^{−λx} dx / log(1/λ) → K       (λ → 0⁺).

Then `∫_0^T g / (T log T) → K / n!` (`tendsto_of_laplace`).

* The a-priori bound `∫_0^T g ≤ C T log T` (`upper_of_laplace`) comes from the Laplace bound
  itself: on `[T, 2T]`, `g(x) ≤ e T^{−n} x^n g(x) e^{−x/(2T)}`, so
  `∫_T^{2T} g ≤ e T^{−n} Lap(1/(2T)) ≪ T log T`; then sum dyadically.
* Karamata (`CriticalMeanSquareAsymp.KarC`) for `m(x) = x^n g(x)`, `ρ = n+1`, with the test
  function `gK·Q_ε`, `Q_ε(e^{−u}) = max(u, ε)^{−n}`, sandwiches `∫_0^T g` exactly as in
  `CriticalMeanSquareAsymp.Final` (the case `n = 11`, `g = |L(Δ,6+it)|²`).
-/
import RamanujanTau.CriticalMeanSquareAsymp.KarC

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.CriticalMeanSquareAsymp
open RamanujanTau.EisensteinReal (Lam kw gK)
open scoped Real

section

variable {g : ℝ → ℝ} {n : ℕ} {K : ℝ}

/-- The Laplace transform `∫_0^∞ x^n g(x) e^{−λx} dx`. -/
noncomputable def LapG (g : ℝ → ℝ) (n : ℕ) (l : ℝ) : ℝ :=
  ∫ x in Ioi 0, x ^ n * g x * Real.exp (-(x * l))

/-- Hypotheses of the abstract Tauberian step. -/
structure LapHyp (g : ℝ → ℝ) (n : ℕ) (K : ℝ) : Prop where
  cont : Continuous g
  nonneg : ∀ x, 0 ≤ g x
  integ : ∀ l : ℝ, 0 < l → IntegrableOn (fun x => x ^ n * g x * Real.exp (-(x * l))) (Ioi 0)
  lim : Tendsto (fun l : ℝ => l ^ (n + 1) / Real.log (1 / l) * LapG g n l) (𝓝[>] 0) (𝓝 K)

/-- `m(x) = x^n g(x)`. -/
noncomputable def mG (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := x ^ n * g x

lemma karHyp_of (h : LapHyp g n K) : KarHypC (mG g n) ((n + 1 : ℕ) : ℝ) K where
  nonneg x hx := by unfold mG; have := h.nonneg x; positivity
  integ t ht := h.integ t ht
  lim := by
    refine h.lim.congr fun t => ?_
    rw [Real.rpow_natCast]
    rfl

lemma K_nonneg (h : LapHyp g n K) : 0 ≤ K := KC_nonneg (karHyp_of h)

/-! ### The a-priori upper bound -/

lemma lap_bound (h : LapHyp g n K) : ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ < 1 ∧ ∀ l, 0 < l → l < l₀ →
    LapG g n l ≤ (K + 1) * Real.log (1 / l) / l ^ (n + 1) := by
  have hev := (tendsto_order.1 h.lim).2 (K + 1) (by linarith)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min u (1 / 2), lt_min hu (by norm_num), by
    have := min_le_right u (1 / 2 : ℝ); linarith, fun l hl0 hl => ?_⟩
  have hlu : l < u := lt_of_lt_of_le hl (min_le_left _ _)
  have hl1 : l < 1 := by have := min_le_right u (1 / 2 : ℝ); linarith
  have hb := hsub ⟨hl0, hlu⟩
  simp only [mem_setOf_eq] at hb
  have hlog : 0 < Real.log (1 / l) := Real.log_pos (by rw [lt_div_iff₀ hl0]; linarith)
  rw [le_div_iff₀ (by positivity)]
  have e : l ^ (n + 1) / Real.log (1 / l) * LapG g n l * Real.log (1 / l) =
      LapG g n l * l ^ (n + 1) := by field_simp
  have := mul_le_mul_of_nonneg_right hb.le hlog.le
  rw [e] at this
  linarith

lemma setIntegral_Icc_eq_interval' (hc : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, g t = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- Dyadic bound `∫_T^{2T} g ≤ C T (1 + log T)`, `T ≥ 1`. -/
lemma dyadic_of_laplace (h : LapHyp g n K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), g t ≤ C * T * (1 + Real.log T) := by
  obtain ⟨l₀, hl₀, hl₀1, hLb⟩ := lap_bound h
  have hK := K_nonneg h
  set T₁ : ℝ := 1 / l₀ with hT₁
  have hT₁1 : 1 ≤ T₁ := by rw [hT₁, le_div_iff₀ hl₀]; linarith
  set B : ℝ := ∫ t in Icc 0 (2 * T₁), g t with hB
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Icc fun t _ => h.nonneg t
  set C₀ : ℝ := Real.exp 1 * (K + 1) * 2 ^ (n + 1) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + B, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT := Real.log_nonneg hT
  have hgi : ∀ a b : ℝ, IntegrableOn g (Icc a b) := fun a b => h.cont.integrableOn_Icc
  rcases le_or_gt T T₁ with hTT | hTT
  · -- small `T`
    have h1 : ∫ t in Icc T (2 * T), g t ≤ B :=
      setIntegral_mono_set (hgi 0 (2 * T₁))
        (ae_restrict_of_forall_mem measurableSet_Icc fun t _ => h.nonneg t)
        (Eventually.of_forall (Icc_subset_Icc (by linarith) (by linarith)))
    have h2 : B ≤ B * T * (1 + Real.log T) := by
      have : 1 ≤ T * (1 + Real.log T) := by nlinarith
      nlinarith
    have h3 : 0 ≤ C₀ * T * (1 + Real.log T) := by positivity
    nlinarith
  · -- large `T`: compare with the Laplace transform at `l = 1/(2T)`
    set l : ℝ := 1 / (2 * T) with hl
    have hl0 : 0 < l := by positivity
    have hll₀ : l < l₀ := by
      rw [hl, div_lt_iff₀ (by positivity)]
      rw [hT₁, div_lt_iff₀ hl₀] at hTT
      nlinarith
    have hLap := hLb l hl0 hll₀
    have hpt : ∀ x ∈ Icc T (2 * T), g x ≤
        Real.exp 1 / T ^ n * (x ^ n * g x * Real.exp (-(x * l))) := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hxn : T ^ n ≤ x ^ n := pow_le_pow_left₀ hT0.le hx.1 n
      have hexp : Real.exp (-1) ≤ Real.exp (-(x * l)) := by
        apply Real.exp_le_exp.mpr
        have : x * l ≤ 1 := by
          rw [hl, mul_one_div, div_le_one (by positivity)]; linarith [hx.2]
        linarith
      have hg := h.nonneg x
      have hE : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc g x * T ^ n = g x * T ^ n * (Real.exp 1 * Real.exp (-1)) := by rw [hE, mul_one]
        _ ≤ g x * x ^ n * (Real.exp 1 * Real.exp (-(x * l))) := by gcongr
        _ = _ := by ring
    have hI : ∫ t in Icc T (2 * T), g t ≤
        Real.exp 1 / T ^ n * ∫ x in Icc T (2 * T), x ^ n * g x * Real.exp (-(x * l)) := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hgi _ _) (((h.integ l hl0).mono_set (fun x hx =>
        show (0 : ℝ) < x by linarith [hx.1])).const_mul _) measurableSet_Icc hpt
    have hsub : ∫ x in Icc T (2 * T), x ^ n * g x * Real.exp (-(x * l)) ≤ LapG g n l := by
      unfold LapG
      refine setIntegral_mono_set (h.integ l hl0)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
        (Eventually.of_forall (fun x hx => show (0 : ℝ) < x by linarith [hx.1]))
      have : (0 : ℝ) < x := hx
      have := h.nonneg x
      positivity
    have hlog2 : Real.log (1 / l) ≤ 1 + Real.log T := by
      rw [hl, one_div_one_div, Real.log_mul (by norm_num) hT0.ne']
      have : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith
    have hl' : l ^ (n + 1) = 1 / (2 * T) ^ (n + 1) := by rw [hl, one_div_pow]
    have hfinal : Real.exp 1 / T ^ n * LapG g n l ≤ C₀ * T * (1 + Real.log T) := by
      have h1 : LapG g n l ≤ (K + 1) * (1 + Real.log T) * (2 * T) ^ (n + 1) := by
        refine hLap.trans ?_
        rw [hl', div_div_eq_mul_div, div_one]
        gcongr
      calc Real.exp 1 / T ^ n * LapG g n l ≤
          Real.exp 1 / T ^ n * ((K + 1) * (1 + Real.log T) * (2 * T) ^ (n + 1)) := by gcongr
        _ = C₀ * T * (1 + Real.log T) := by
          rw [hC₀]; field_simp; ring
    have := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ Real.exp 1 / T ^ n)
    have h3 : 0 ≤ B * T * (1 + Real.log T) := by positivity
    nlinarith

/-- `∫_1^T g ≤ 2C T (1 + log T)` for `1 ≤ T ≤ 2ⁿ`. -/
lemma cum_aux_gen (hcont : Continuous g) (hnn : ∀ x, 0 ≤ g x) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ T : ℝ, 1 ≤ T → ∫ t in Icc T (2 * T), g t ≤ C * T * (1 + Real.log T)) :
    ∀ N : ℕ, ∀ T : ℝ, 1 ≤ T → T ≤ 2 ^ N →
      ∫ t in (1 : ℝ)..T, g t ≤ 2 * C * T * (1 + Real.log T) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hcont.intervalIntegrable a b
  have base : ∀ T : ℝ, 1 ≤ T → T ≤ 2 → ∫ t in (1 : ℝ)..T, g t ≤ 2 * C * T * (1 + Real.log T) := by
    intro T h1 h2
    have hlog := Real.log_nonneg h1
    have hmono : ∫ t in (1 : ℝ)..T, g t ≤ ∫ t in (1 : ℝ)..2, g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 T) (hii T 2)]
      have := intervalIntegral.integral_nonneg (μ := volume) h2 (fun t _ => hnn t)
      linarith
    have h12 := hC 1 le_rfl
    rw [mul_one, Real.log_one, setIntegral_Icc_eq_interval' hcont (by norm_num : (1 : ℝ) ≤ 2)] at h12
    have : C * 1 * (1 + 0) ≤ 2 * C * T * (1 + Real.log T) := by
      have h3 : 1 ≤ 2 * T * (1 + Real.log T) := by nlinarith
      nlinarith
    linarith
  intro N
  induction N with
  | zero => intro T h1 h2; exact base T h1 (by simp at h2; linarith)
  | succ N ih =>
    intro T h1 h2
    rcases le_or_gt T 2 with hT2 | hT2
    · exact base T h1 hT2
    have hh1 : 1 ≤ T / 2 := by linarith
    have hh2 : T / 2 ≤ 2 ^ N := by rw [pow_succ] at h2; linarith
    have hIH := ih (T / 2) hh1 hh2
    have hD := hC (T / 2) hh1
    rw [show 2 * (T / 2) = T by ring, setIntegral_Icc_eq_interval' hcont (by linarith)] at hD
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 (T / 2)) (hii (T / 2) T)]
    have hlog : Real.log (T / 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (T / 2) := Real.log_nonneg hh1
    have e1 : 2 * C * (T / 2) * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by
      have : C * T * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by gcongr
      linarith
    have e2 : C * (T / 2) * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) / 2 := by
      have : C * T * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by gcongr
      linarith
    have e3 : 0 ≤ C * T * (1 + Real.log T) := by
      have := Real.log_nonneg h1; positivity
    linarith

/-- **A-priori bound** `∫_0^T g ≤ C T log T` for `T ≥ e`. -/
theorem upper_of_laplace (h : LapHyp g n K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc 0 T, g t ≤ C * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := dyadic_of_laplace h
  set B : ℝ := ∫ t in (0 : ℝ)..1, g t with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (μ := volume) zero_le_one
    (fun t _ => h.nonneg t)
  refine ⟨2 * (B + 2 * C), by positivity, fun T hT => ?_⟩
  have h1 : 1 ≤ T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hT
  have hl : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
  have hc := cum_aux_gen h.cont h.nonneg hC0 hC N T h1 hN.le
  have hii : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    h.cont.intervalIntegrable a b
  rw [setIntegral_Icc_eq_interval' h.cont (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 1) (hii 1 T), ← hB]
  have hT1 : 1 ≤ T * Real.log T := by nlinarith
  have : B ≤ B * T * Real.log T := by nlinarith
  have h4 : 2 * C * T * (1 + Real.log T) ≤ 2 * (2 * C) * T * Real.log T := by
    have : 0 ≤ C * T := by positivity
    nlinarith
  nlinarith

/-! ### The test function `Q_ε` -/

/-- `Q_ε(x) = max(−log max(x, e⁻¹/2), ε)^{-n}`. -/
noncomputable def QeN (n : ℕ) (ε x : ℝ) : ℝ :=
  ((max (-Real.log (max x (Real.exp (-1) / 2))) ε)⁻¹) ^ n

lemma continuous_QeN {ε : ℝ} (hε : 0 < ε) : Continuous (QeN n ε) := by
  unfold QeN
  have h1 : Continuous fun x : ℝ => max x (Real.exp (-1) / 2) := continuous_id.max continuous_const
  have h2 : Continuous fun x : ℝ => Real.log (max x (Real.exp (-1) / 2)) :=
    h1.log fun x => (lt_max_of_lt_right (by positivity : (0 : ℝ) < Real.exp (-1) / 2)).ne'
  exact ((h2.neg.max continuous_const).inv₀ fun x =>
    (lt_max_of_lt_right hε).ne').pow n

lemma QeN_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ QeN n ε x := by
  unfold QeN
  have : 0 < max (-Real.log (max x (Real.exp (-1) / 2))) ε := lt_max_of_lt_right hε
  positivity

lemma QeN_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : QeN n ε x ≤ (ε⁻¹) ^ n := by
  unfold QeN
  have h : ε ≤ max (-Real.log (max x (Real.exp (-1) / 2))) ε := le_max_right _ _
  have : 0 < max (-Real.log (max x (Real.exp (-1) / 2))) ε := lt_max_of_lt_right hε
  gcongr

lemma QeN_exp {ε u : ℝ} (hu1 : u ≤ 1) : QeN n ε (Real.exp (-u)) = ((max u ε)⁻¹) ^ n := by
  unfold QeN
  have h : Real.exp (-1) / 2 ≤ Real.exp (-u) := by
    have h1 : Real.exp (-1) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 0 < Real.exp (-1) := Real.exp_pos _
    linarith
  rw [max_eq_left h, Real.log_exp, neg_neg]

lemma gK_exp' {u : ℝ} : gK (Real.exp (-u)) = if u ≤ 1 then (Real.exp (-u))⁻¹ else 0 := by
  unfold gK
  by_cases h : u ≤ 1
  · rw [if_pos (Real.exp_le_exp.mpr (by linarith)), if_pos h]
  · rw [if_neg (fun h' => h (by have := Real.exp_le_exp.mp h'; linarith)), if_neg h]

lemma Lam_gQN_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) / (Nat.factorial n : ℝ) ≤ Lam ((n + 1 : ℕ) : ℝ) (fun x => gK x * QeN n ε x) ∧
      Lam ((n + 1 : ℕ) : ℝ) (fun x => gK x * QeN n ε x) ≤ 1 / (Nat.factorial n : ℝ) := by
  set φ : ℝ → ℝ := fun u => (u / max u ε) ^ n with hφ
  have hφc : Continuous φ := (continuous_id.div (continuous_id.max continuous_const) fun u =>
    (lt_max_of_lt_right hε).ne').pow n
  have hpt : ∀ u ∈ Ioi (0 : ℝ), gK (Real.exp (-u)) * QeN n ε (Real.exp (-u)) *
      kw ((n + 1 : ℕ) : ℝ) u = (Iic (1 : ℝ)).indicator φ u := by
    intro u hu
    have hu0 : 0 < u := hu
    rw [gK_exp']
    unfold kw
    rw [show ((n + 1 : ℕ) : ℝ) - 1 = ((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    by_cases h1 : u ≤ 1
    · rw [if_pos h1, QeN_exp h1, indicator_of_mem (show u ∈ Iic (1 : ℝ) from h1), hφ]
      simp only
      have : 0 < max u ε := lt_max_of_lt_right hε
      rw [div_pow, inv_pow]
      have hE := Real.exp_pos (-u)
      field_simp
    · rw [if_neg h1, indicator_of_notMem (show u ∉ Iic (1 : ℝ) from h1)]; ring
  have hI : ∫ u in Ioi 0, gK (Real.exp (-u)) * QeN n ε (Real.exp (-u)) * kw ((n + 1 : ℕ) : ℝ) u =
      ∫ u in (0 : ℝ)..1, φ u := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic, intervalIntegral.integral_of_le zero_le_one]
  have hΓ : Real.Gamma ((n + 1 : ℕ) : ℝ) = (Nat.factorial n : ℝ) := by
    rw [show ((n + 1 : ℕ) : ℝ) = ((n : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
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
  have hf : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  constructor
  · exact div_le_div_of_nonneg_right hlo hf.le
  · exact div_le_div_of_nonneg_right hup hf.le

lemma SCN_bounds (h : LapHyp g n K) {ε T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) :
    T ^ n * ∫ x in Ioc (ε * T) T, g x ≤ SC (mG g n) (fun x => gK x * QeN n ε x) T⁻¹ ∧
      SC (mG g n) (fun x => gK x * QeN n ε x) T⁻¹ ≤ T ^ n * ∫ x in Ioc 0 T, g x := by
  set I : ℝ → ℝ := fun x => mG g n x * Real.exp (-(x * T⁻¹)) *
    (gK (Real.exp (-(x * T⁻¹))) * QeN n ε (Real.exp (-(x * T⁻¹)))) with hIdef
  have hεT : 0 < ε * T := by positivity
  have hI : ∀ x, 0 < x → x ≤ T → I x = x ^ n * g x * ((max (x / T) ε)⁻¹) ^ n := by
    intro x hx hxT
    have hu : x * T⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hT]; exact hxT
    simp only [hIdef, mG]
    rw [gK_exp', if_pos hu, QeN_exp hu, ← div_eq_mul_inv x T]
    have := Real.exp_pos (-(x / T))
    field_simp
  have hI0 : ∀ x, T < x → I x = 0 := by
    intro x hx
    have hu : ¬ x * T⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hT]; linarith
    simp only [hIdef]
    rw [gK_exp', if_neg hu]; ring
  have hInn : ∀ x, 0 < x → 0 ≤ I x := by
    intro x hx
    simp only [hIdef, mG]
    have := h.nonneg x
    have := QeN_nonneg (n := n) hε (Real.exp (-(x * T⁻¹)))
    have hg : 0 ≤ gK (Real.exp (-(x * T⁻¹))) := by
      rw [gK_exp']; split_ifs
      · exact (inv_pos.2 (Real.exp_pos _)).le
      · exact le_rfl
    positivity
  have hIi : IntegrableOn I (Ioi 0) := by
    have := integrableOn_SC (karHyp_of h)
      (f := fun x => gK x * QeN n ε x) ?_ (inv_pos.2 hT)
    · refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [hIdef]
    · obtain ⟨hm1, B, hB⟩ := RamanujanTau.EisensteinReal.adm_gK
      refine ⟨hm1.mul (continuous_QeN hε).measurable, B * (ε⁻¹) ^ n, fun x hx => ?_⟩
      rw [abs_mul, abs_of_nonneg (QeN_nonneg hε x)]
      exact mul_le_mul (hB x hx) (QeN_le hε x) (QeN_nonneg hε x) ((abs_nonneg _).trans (hB x hx))
  have hSC : SC (mG g n) (fun x => gK x * QeN n ε x) T⁻¹ = ∫ x in Ioc 0 T, I x := by
    have e1 : SC (mG g n) (fun x => gK x * QeN n ε x) T⁻¹ = ∫ x in Ioi 0, I x := by
      unfold SC; rfl
    rw [e1, ← Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hIi.mono_set Ioc_subset_Ioi_self) (hIi.mono_set (Ioi_subset_Ioi hT.le)),
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioi T) (fun x hx => hI0 x hx), add_zero]
  have hLi : ∀ a b : ℝ, IntegrableOn g (Ioc a b) := fun a b =>
    (h.cont.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
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
    rw [inv_div, div_pow]
    field_simp
  · rw [← integral_const_mul]
    refine setIntegral_mono_on (hIi.mono_set Ioc_subset_Ioi_self) ((hLi 0 T).const_mul _)
      measurableSet_Ioc fun x hx => ?_
    rw [hI x hx.1 hx.2]
    have hL := h.nonneg x
    have hm : x / T ≤ max (x / T) ε := le_max_left _ _
    have hxT : 0 < x / T := div_pos hx.1 hT
    have h1 : x ^ n * ((max (x / T) ε)⁻¹) ^ n ≤ T ^ n := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg hx.1.le (inv_nonneg.2 (le_trans hxT.le hm)))
      rw [← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le hxT hm)]
      calc x = T * (x / T) := by field_simp
        _ ≤ T * max (x / T) ε := by gcongr
    calc x ^ n * g x * ((max (x / T) ε)⁻¹) ^ n = x ^ n * ((max (x / T) ε)⁻¹) ^ n * g x := by
          ring
      _ ≤ T ^ n * g x := mul_le_mul_of_nonneg_right h1 hL

/-- **The abstract Tauberian theorem**: `∫_0^T g / (T log T) → K / n!`. -/
theorem tendsto_of_laplace (h : LapHyp g n K) :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, g t) / (T * Real.log T)) atTop
      (𝓝 (K / (Nat.factorial n : ℝ))) := by
  obtain ⟨CU, hCU0, hCU⟩ := upper_of_laplace h
  set F : ℝ → ℝ := fun T => ∫ t in Icc 0 T, g t with hF
  have hFioc : ∀ T, F T = ∫ x in Ioc 0 T, g x := fun T => by
    simp only [hF]; rw [integral_Icc_eq_integral_Ioc]
  have hdiff : ∀ a T : ℝ, 0 ≤ a → a ≤ T → ∫ x in Ioc a T, g x = F T - F a := by
    intro a T ha haT
    rw [hFioc, hFioc, ← intervalIntegral.integral_of_le haT,
      ← intervalIntegral.integral_of_le (ha.trans haT), ← intervalIntegral.integral_of_le ha]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (h.cont.intervalIntegrable 0 a) (h.cont.intervalIntegrable a T)]
    ring
  have hF0 : ∀ T, 0 ≤ F T := fun T => setIntegral_nonneg measurableSet_Icc fun t _ => h.nonneg t
  have hK0 := K_nonneg h
  set cD := K / (Nat.factorial n : ℝ) with hcD
  have hf : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  rw [Metric.tendsto_atTop]
  intro e he
  set ε : ℝ := min (1 / 2) (e / (4 * (K / (Nat.factorial n : ℝ) + CU + 1))) with hεdef
  have hKf : 0 ≤ K / (Nat.factorial n : ℝ) := div_nonneg hK0 hf.le
  have hden : 0 < 4 * (K / (Nat.factorial n : ℝ) + CU + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos he hden)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεe : ε * (K / (Nat.factorial n : ℝ) + CU) ≤ e / 4 := by
    have h1 : ε ≤ e / (4 * (K / (Nat.factorial n : ℝ) + CU + 1)) := min_le_right _ _
    rw [le_div_iff₀ hden] at h1
    nlinarith
  have hconv := convC_gKQ (karHyp_of h) (by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    (continuous_QeN (n := n) hε) (QeN_nonneg hε) (QeN_le hε)
  unfold ConvC at hconv
  have hZ := hconv.comp tendsto_inv_atTop_nhdsGT_zero
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hZ (e / 4) (by positivity)
  obtain ⟨hΛlo, hΛhi⟩ := Lam_gQN_bounds (n := n) hε hε1
  set Λε := Lam ((n + 1 : ℕ) : ℝ) (fun x => gK x * QeN n ε x)
  refine ⟨max (max N₁ 2) (Real.exp 1 / ε), fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTN : N₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTe : Real.exp 1 / ε ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hTL : 0 < T * Real.log T := mul_pos hT0 hlogT
  have hZT := hN₁ T hTN
  simp only [Function.comp] at hZT
  rw [one_div (T⁻¹), inv_inv, Real.rpow_natCast, Real.dist_eq] at hZT
  set S := SC (mG g n) (fun x => gK x * QeN n ε x) T⁻¹
  set Z := T⁻¹ ^ (n + 1) / Real.log T * S with hZ
  obtain ⟨hS1, hS2⟩ := SCN_bounds h hε hε1 hT0
  rw [hdiff (ε * T) T (by positivity) (by nlinarith)] at hS1
  rw [← hFioc] at hS2
  have hZeq : Z = S / (T ^ (n + 1) * Real.log T) := by
    rw [hZ, inv_pow]; field_simp
  have hZup : Z ≤ F T / (T * Real.log T) := by
    rw [hZeq, div_le_div_iff₀ (by positivity) hTL]
    calc S * (T * Real.log T) ≤ T ^ n * F T * (T * Real.log T) := by gcongr
      _ = F T * (T ^ (n + 1) * Real.log T) := by ring
  have hZlo : (F T - F (ε * T)) / (T * Real.log T) ≤ Z := by
    rw [hZeq, div_le_div_iff₀ hTL (by positivity)]
    calc (F T - F (ε * T)) * (T ^ (n + 1) * Real.log T) = T ^ n * (F T - F (ε * T)) *
        (T * Real.log T) := by ring
      _ ≤ S * (T * Real.log T) := by gcongr
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
  have hKΛlo : K * ((1 - ε) / (Nat.factorial n : ℝ)) ≤ K * Λε :=
    mul_le_mul_of_nonneg_left hΛlo hK0
  have hKΛhi : K * Λε ≤ K * (1 / (Nat.factorial n : ℝ)) :=
    mul_le_mul_of_nonneg_left hΛhi hK0
  have e1 : K * ((1 - ε) / (Nat.factorial n : ℝ)) = cD - ε * (K / (Nat.factorial n : ℝ)) := by
    rw [hcD]; ring
  have e2 : K * (1 / (Nat.factorial n : ℝ)) = cD := by rw [hcD]; ring
  have hFε0 : 0 ≤ F (ε * T) / (T * Real.log T) := div_nonneg (hF0 _) hTL.le
  constructor
  · nlinarith
  · nlinarith

end

end RamanujanTau.GeneralCuspMoments
