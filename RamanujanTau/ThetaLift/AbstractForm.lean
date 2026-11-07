import RamanujanTau.ThetaLift.HalfExpansion
import RamanujanTau.ThetaLift.TaylorExtract

/-!
# Modular forms from `q`-series

A polynomially bounded `q`-series which transforms with weight `k` under `Γ₀(M)` is a modular form with that
`q`-expansion. Boundedness at the other cusps follows from moderate growth, by the removable singularity
theorem.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open UpperHalfPlane ModularForm Filter Asymptotics Function Set
open scoped MatrixGroups Manifold Real Topology Nat

noncomputable section

local notation "𝕢" => Periodic.qParam

variable (c : ℕ → ℂ) {C : ℝ} {K : ℕ}

/-- The sum of a power series. -/
def qS (q : ℂ) : ℂ := ∑' n : ℕ, c n * q ^ n

lemma summable_coef_pow (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖c n‖ * r ^ n := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hc 1 le_rfl)
    simpa using this
  have hbase := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) K (r := r)
    (by rwa [Real.norm_of_nonneg hr0])).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hbase ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  calc _ ≤ (C * (n : ℝ) ^ K) * r ^ n := by gcongr; exact hc n hn
    _ = _ := by ring

lemma summable_qterm (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖c n * q ^ n‖ := by
  simpa [norm_mul, norm_pow] using summable_coef_pow c hc (norm_nonneg q) hq

lemma qS_diff (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) :
    DifferentiableOn ℂ (qS c) (Metric.ball 0 1) := by
  intro q hq
  have hq' : ‖q‖ < 1 := by simpa using hq
  obtain ⟨R, hR1, hR2⟩ := exists_between hq'
  have hR0 : 0 ≤ R := (norm_nonneg q).trans hR1.le
  have hS := summable_coef_pow c hc hR0 hR2
  have hd := Complex.differentiableOn_tsum_of_summable_norm (F := fun (n : ℕ) (q : ℂ) => c n * q ^ n)
    (U := Metric.ball (0 : ℂ) R) hS (fun n => by fun_prop) Metric.isOpen_ball (fun n w hw => by
      have hw' : ‖w‖ ≤ R := by
        have : ‖w‖ < R := by simpa using hw
        exact this.le
      rw [norm_mul, norm_pow]
      gcongr)
  have hU : Metric.ball (0 : ℂ) R ∈ 𝓝 q := Metric.isOpen_ball.mem_nhds (by simpa using hR1)
  exact (hd.differentiableAt hU).differentiableWithinAt

/-- The Taylor coefficients of the sum. -/
lemma qS_taylor (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) (k : ℕ) :
    iteratedDeriv k (qS c) 0 = (k ! : ℂ) * c k := by
  have hS := summable_coef_pow c hc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h := hasSum_iteratedDeriv (F := fun (n : ℕ) (q : ℂ) => c n * q ^ n)
    (U := Metric.ball (0 : ℂ) (1 / 2)) hS Metric.isOpen_ball
    (fun n => by fun_prop) (fun n w hw => by
      have hw' : ‖w‖ ≤ 1 / 2 := by
        have : ‖w‖ < 1 / 2 := by simpa using hw
        exact this.le
      rw [norm_mul, norm_pow]
      gcongr) k (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hterm : ∀ n : ℕ, iteratedDeriv k (fun q : ℂ => c n * q ^ n) 0 =
      if n = k then (k ! : ℂ) * c k else 0 := by
    intro n
    have hp : (fun q : ℂ => c n * q ^ n) =
        fun q => (Polynomial.C (c n) * Polynomial.X ^ n : Polynomial ℂ).eval q := by
      funext q
      simp
    rw [hp, DiscriminantBridge.iteratedDeriv_poly_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hnk : n = k
    · subst hnk
      simp
    · have hkn : k ≠ n := fun h => hnk h.symm
      simp [hnk, hkn]
  simp only [hterm] at h
  have hs := hasSum_ite_eq k ((k ! : ℂ) * c k)
  exact h.unique hs

/-- The function on `ℍ`. -/
def fS (t : ℍ) : ℂ := qS c (𝕢 (1 : ℝ) t)

lemma norm_q (t : ℍ) : ‖𝕢 (1 : ℝ) (t : ℂ)‖ < 1 := by
  simpa using norm_qParam_lt_one 1 t

lemma good_fS (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) : Good (fS c) where
  per := by
    apply periodic_of
    intro t
    unfold fS
    rw [qParam_vadd]
  holo := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have h : DifferentiableOn ℂ (fun z : ℂ => qS c (𝕢 (1 : ℝ) z)) upperHalfPlaneSet := by
      refine (qS_diff c hc).comp (by fun_prop) fun z hz => ?_
      simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
    refine h.congr fun z hz => ?_
    simp only [comp_apply, ofComplex_apply_of_im_pos hz]
    rfl
  bdd := by
    set r : ℝ := Real.exp (-(2 * π)) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; linarith)
    have hS := summable_coef_pow c hc hr0 hr1
    refine IsBigO.of_bound (∑' n : ℕ, ‖c n‖ * r ^ n) ?_
    filter_upwards [(atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩] with t ht
    have ht' : 1 ≤ t.im := ht
    have hq : ‖𝕢 (1 : ℝ) (t : ℂ)‖ ≤ r := by
      rw [Periodic.norm_qParam, hr]
      apply Real.exp_le_exp.mpr
      have him : (t : ℂ).im = t.im := rfl
      rw [him, div_one]
      nlinarith [Real.pi_pos]
    simp only [Pi.one_apply, norm_one, mul_one]
    unfold fS qS
    refine (norm_tsum_le_tsum_norm (summable_qterm c hc (norm_q t))).trans ?_
    refine (summable_qterm c hc (norm_q t)).tsum_le_tsum (fun n => ?_) hS
    rw [norm_mul, norm_pow]
    gcongr

/-- **The `q`-expansion of the series.** -/
theorem qExp_fS (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) :
    qExpansion (1 : ℝ) (fS c) = PowerSeries.mk c := by
  ext k
  have hev : cuspFunction (1 : ℝ) (fS c) =ᶠ[𝓝 0] qS c := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    exact cusp_eq_of (good_fS c hc) (qS_diff c hc) (fun _ => rfl) (by simpa using hq)
  rw [qExpansion_coeff, (DiscriminantBridge.eventuallyEq_iteratedDeriv hev k).eq_of_nhds,
    qS_taylor c hc, PowerSeries.coeff_mk, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast k.factorial_ne_zero

/-- **Moderate growth.** -/
theorem norm_fS_le (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K) (t : ℍ) :
    ‖fS c t‖ ≤ ‖c 0‖ + C * (K ! : ℝ) * (π * t.im)⁻¹ ^ (K + 1) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hc 1 le_rfl)
    simpa using this
  have hπ := Real.pi_pos
  have hv := t.im_pos
  set a : ℝ := π * t.im with ha
  have hapos : 0 < a := by positivity
  have hS := summable_qterm c hc (norm_q t)
  have hnormq : ‖𝕢 (1 : ℝ) (t : ℂ)‖ = Real.exp (-(2 * a)) := by
    rw [Periodic.norm_qParam]
    congr 1
    have him : (t : ℂ).im = t.im := rfl
    rw [him, ha]
    simp
    ring
  have hterm : ∀ n : ℕ, ‖c (n + 1) * 𝕢 (1 : ℝ) (t : ℂ) ^ (n + 1)‖ ≤
      C * (K ! : ℝ) * a⁻¹ ^ K * Real.exp (-(a * ((n : ℝ) + 1))) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := hc (n + 1) (by omega)
    push_cast at h1
    have h2 : (a * ((n : ℝ) + 1)) ^ K / (K ! : ℝ) ≤ Real.exp (a * ((n : ℝ) + 1)) :=
      Real.pow_div_factorial_le_exp _ (by positivity) K
    have hf : (0 : ℝ) < (K ! : ℝ) := by exact_mod_cast K.factorial_pos
    have h3 : ((n : ℝ) + 1) ^ K ≤ (K ! : ℝ) * a⁻¹ ^ K * Real.exp (a * ((n : ℝ) + 1)) := by
      rw [div_le_iff₀ hf, mul_pow] at h2
      have hap := pow_pos hapos K
      calc ((n : ℝ) + 1) ^ K = (a ^ K)⁻¹ * (a ^ K * ((n : ℝ) + 1) ^ K) := by field_simp
        _ ≤ (a ^ K)⁻¹ * (Real.exp (a * ((n : ℝ) + 1)) * (K ! : ℝ)) := by gcongr
        _ = _ := by rw [inv_pow]; ring
    rw [norm_mul, norm_pow, hnormq, ← Real.exp_nat_mul]
    have e : Real.exp ((n + 1 : ℕ) * -(2 * a)) = Real.exp (-(a * ((n : ℝ) + 1))) *
        Real.exp (-(a * ((n : ℝ) + 1))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    have hE : Real.exp (a * ((n : ℝ) + 1)) * Real.exp (-(a * ((n : ℝ) + 1))) = 1 := by
      rw [← Real.exp_add]
      simp
    calc _ ≤ (C * ((K ! : ℝ) * a⁻¹ ^ K * Real.exp (a * ((n : ℝ) + 1)))) *
          (Real.exp (-(a * ((n : ℝ) + 1))) * Real.exp (-(a * ((n : ℝ) + 1)))) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = C * (K ! : ℝ) * a⁻¹ ^ K * (Real.exp (a * ((n : ℝ) + 1)) * Real.exp (-(a * ((n : ℝ) + 1)))) *
          Real.exp (-(a * ((n : ℝ) + 1))) := by ring
      _ = _ := by rw [hE, mul_one]
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-a))
  have hexp : ∀ n : ℕ, Real.exp (-(a * ((n : ℝ) + 1))) = Real.exp (-a) * Real.exp (-a) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hval : ∑' n : ℕ, Real.exp (-a) * Real.exp (-a) ^ n ≤ a⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    have h1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
    have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    rw [inv_eq_one_div, div_mul_eq_mul_div, one_mul, le_div_iff₀ hapos]
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]
  have hS2 : Summable fun n : ℕ => ‖c (n + 1) * 𝕢 (1 : ℝ) (t : ℂ) ^ (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr hS
  have hsum : ∑' n : ℕ, ‖c n * 𝕢 (1 : ℝ) (t : ℂ) ^ n‖ =
      ‖c 0‖ + ∑' n : ℕ, ‖c (n + 1) * 𝕢 (1 : ℝ) (t : ℂ) ^ (n + 1)‖ := by
    rw [hS.tsum_eq_zero_add]
    simp
  have hb : ∑' n : ℕ, ‖c (n + 1) * 𝕢 (1 : ℝ) (t : ℂ) ^ (n + 1)‖ ≤
      C * (K ! : ℝ) * a⁻¹ ^ (K + 1) := by
    have hle : ∀ n : ℕ, ‖c (n + 1) * 𝕢 (1 : ℝ) (t : ℂ) ^ (n + 1)‖ ≤
        C * (K ! : ℝ) * a⁻¹ ^ K * (Real.exp (-a) * Real.exp (-a) ^ n) := fun n => by
      rw [← hexp]
      exact hterm n
    refine (hS2.tsum_le_tsum hle (hgeo.mul_left _)).trans ?_
    rw [tsum_mul_left, pow_succ, ← mul_assoc]
    gcongr
  unfold fS qS
  refine (norm_tsum_le_tsum_norm hS).trans ?_
  rw [hsum]
  linarith

/-- **Moderate growth at `i∞` gives boundedness at `i∞`.** -/
theorem bdd_of_moderate {h : ℍ → ℂ} {M : ℝ} (hM : 0 < M) (per : Periodic (h ∘ ofComplex) M)
    (hol : MDiff h) {B : ℝ} {K : ℕ} (hb : ∀ t : ℍ, 1 ≤ t.im → ‖h t‖ ≤ B * t.im ^ K) :
    IsBoundedAtImInfty h := by
  have hdiff : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (h ∘ ofComplex) z := by
    exact eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
      fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hol ⟨z, hz⟩)
  set F := Periodic.cuspFunction M (h ∘ ofComplex) with hF
  have hd := per.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hdiff
  have hinv : Tendsto (fun q : ℂ => (Periodic.invQParam M q).im) (𝓝[≠] 0) atTop :=
    tendsto_comap_iff.mp (Periodic.invQParam_tendsto hM)
  have hdecay : Tendsto (fun v : ℝ => v ^ K * Real.exp (-(2 * π / M * v))) atTop (𝓝 0) := by
    have hbpos : 0 < 2 * π / M := by
      have := Real.pi_pos
      positivity
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K : ℝ) _ hbpos
    refine h1.congr fun v => ?_
    rw [Real.rpow_natCast, neg_mul]
  have hnq : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 1 ≤ (Periodic.invQParam M q).im ∧
      ‖q‖ = Real.exp (-(2 * π / M * (Periodic.invQParam M q).im)) ∧
      ‖F q‖ ≤ B * (Periodic.invQParam M q).im ^ K := by
    filter_upwards [hinv.eventually_ge_atTop 1, self_mem_nhdsWithin] with q hq1 hq0
    have hq0' : q ≠ 0 := hq0
    refine ⟨hq1, ?_, ?_⟩
    · have h1 := Periodic.norm_qParam M (Periodic.invQParam M q)
      rw [Periodic.qParam_right_inv hM.ne' hq0'] at h1
      rw [h1]
      congr 1
      ring
    · have him : 0 < (Periodic.invQParam M q).im := by linarith
      rw [hF, Periodic.cuspFunction_eq_of_nonzero _ _ hq0', comp_apply,
        ofComplex_apply_of_im_pos him]
      exact hb ⟨_, him⟩ hq1
  have ho : (fun q => F q - F 0) =o[𝓝[≠] (0 : ℂ)] fun q => (q - 0)⁻¹ := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq hq2
      exact absurd hq2 (inv_ne_zero (sub_ne_zero.mpr hq))
    · have h0 : Tendsto (fun q : ℂ => |B| * ((Periodic.invQParam M q).im ^ K *
          Real.exp (-(2 * π / M * (Periodic.invQParam M q).im))) + ‖F 0‖ * ‖q‖) (𝓝[≠] 0) (𝓝 0) := by
        have h1 := (hdecay.comp hinv).const_mul |B|
        have h2 : Tendsto (fun q : ℂ => ‖q‖) (𝓝[≠] 0) (𝓝 0) :=
          (tendsto_norm_zero).mono_left nhdsWithin_le_nhds
        have h3 := h1.add (h2.const_mul ‖F 0‖)
        simpa using h3
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [hnq, self_mem_nhdsWithin] with q hq hq0
      obtain ⟨h0v, h1, h2⟩ := hq
      rw [sub_zero, div_inv_eq_mul, norm_mul]
      have hvK : 0 ≤ (Periodic.invQParam M q).im ^ K := by
        have : 0 ≤ (Periodic.invQParam M q).im := by linarith
        positivity
      have hF1 : ‖F q - F 0‖ ≤ |B| * (Periodic.invQParam M q).im ^ K + ‖F 0‖ := by
        refine (norm_sub_le _ _).trans ?_
        have : B * (Periodic.invQParam M q).im ^ K ≤ |B| * (Periodic.invQParam M q).im ^ K :=
          mul_le_mul_of_nonneg_right (le_abs_self B) hvK
        linarith
      calc _ ≤ (|B| * (Periodic.invQParam M q).im ^ K + ‖F 0‖) * ‖q‖ := by gcongr
        _ = |B| * ((Periodic.invQParam M q).im ^ K * ‖q‖) + ‖F 0‖ * ‖q‖ := by ring
        _ = _ := by rw [← h1]
  have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd ho
  have hcomp := hlim.comp (Periodic.qParam_tendsto hM)
  have hcomp2 : Tendsto (fun t : ℍ => h t) atImInfty (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) F)) := by
    refine (hcomp.comp tendsto_coe_atImInfty).congr fun t => ?_
    simp only [comp_apply]
    rw [Periodic.eq_cuspFunction hM.ne' per]
    simp
  exact hcomp2.isBigO_one ℝ

/-- Periodicity on `ℍ` with a real period extends through `ofComplex`. -/
lemma periodic_of_real {f : ℍ → ℂ} {M : ℝ} (hM : 0 < M) (h : ∀ t : ℍ, ∀ z : ℂ, (z = (t : ℂ) + M) →
    ∀ hz : 0 < z.im, f ⟨z, hz⟩ = f t) : Periodic (f ∘ ofComplex) M := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + (M : ℂ)).im := by simpa using hz
    simp only [comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
    exact h ⟨z, hz⟩ _ rfl hz'
  · have hz' : ¬ 0 < (z + (M : ℂ)).im := by simpa using hz
    simp only [comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
      ofComplex_apply_of_im_nonpos (not_lt.mp hz')]

/-- The conjugate of a power of the translation lies in `Γ₀(M)`. -/
lemma conj_T_dvd (M : ℕ) (δ : SL(2, ℤ)) :
    (M : ℤ) ∣ (δ * ModularGroup.T ^ (M : ℤ) * δ⁻¹) 1 0 := by
  have h : (δ * ModularGroup.T ^ (M : ℤ) * δ⁻¹) 1 0 = -(δ 1 0) ^ 2 * M := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_two]
    ring
  rw [h]
  exact dvd_mul_left _ _

/-- The slash of the series is periodic. -/
lemma slash_periodic {k : ℕ} {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ}
    (hinv : ∀ ε : SL(2, ℤ), (M : ℤ) ∣ ε 1 0 → f ∣[(k : ℤ)] ε = f) (δ : SL(2, ℤ)) :
    Periodic ((f ∣[(k : ℤ)] δ) ∘ ofComplex) (M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set Tm : SL(2, ℤ) := ModularGroup.T ^ (M : ℤ) with hTm
  have hsl : (f ∣[(k : ℤ)] δ) ∣[(k : ℤ)] Tm = f ∣[(k : ℤ)] δ := by
    rw [← SlashAction.slash_mul]
    have e : δ * Tm = (δ * Tm * δ⁻¹) * δ := by group
    rw [e, SlashAction.slash_mul, hinv _ (conj_T_dvd M δ)]
  refine periodic_of_real hMR fun t z hz him => ?_
  have h1 := congrFun hsl t
  rw [ModularForm.SL_slash_apply] at h1
  have hmat : Tm.1 = !![1, (M : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hb0 : Tm 1 0 = 0 := by
    change Tm.1 1 0 = 0
    rw [hmat]
    rfl
  have hb1 : Tm 1 1 = 1 := by
    change Tm.1 1 1 = 1
    rw [hmat]
    rfl
  have hden : denom Tm t = 1 := by
    have e : denom Tm t = ((Tm 1 0 : ℤ) : ℂ) * t + ((Tm 1 1 : ℤ) : ℂ) := by simp [denom]
    rw [e, hb0, hb1]
    simp
  have hact : Tm • t = ⟨z, him⟩ := by
    apply UpperHalfPlane.ext
    change ((Tm • t : ℍ) : ℂ) = z
    have := ModularGroup.coe_T_zpow_smul_eq (z := t) (n := (M : ℤ))
    rw [hz, hTm, this]
    simp
  rw [hden, one_zpow, mul_one, hact] at h1
  exact h1

/-- **Boundedness at every cusp.** -/
theorem slash_bdd {k : ℕ} {M : ℕ} (hM : 0 < M) (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K)
    (hinv : ∀ ε : SL(2, ℤ), (M : ℤ) ∣ ε 1 0 → fS c ∣[(k : ℤ)] ε = fS c) (δ : SL(2, ℤ)) :
    IsBoundedAtImInfty (fS c ∣[(k : ℤ)] δ) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hc 1 le_rfl)
    simpa using this
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hπ := Real.pi_pos
  have hper := slash_periodic hM hinv δ
  have hhol : MDiff (fS c ∣[(k : ℤ)] δ) := by
    have := (good_fS c hc).holo.slash (k : ℤ) ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ)
    exact this
  set cc : ℝ := ((δ 1 0 : ℤ) : ℝ) with hcc
  set dd : ℝ := ((δ 1 1 : ℤ) : ℝ) with hdd
  set A : ℝ := (|cc| * M + |dd|) ^ 2 + cc ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set B : ℝ := ‖c 0‖ + C * (K ! : ℝ) * (A / π) ^ (K + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  refine bdd_of_moderate hMR hper hhol (B := B) (K := K + 1) fun t ht => ?_
  -- reduce to the period strip
  set n : ℤ := ⌊t.re / M⌋ with hn
  have hu0 : 0 ≤ t.re - n * M := by
    have := Int.floor_le (t.re / M)
    rw [div_eq_mul_inv] at this
    have h2 : (n : ℝ) * M ≤ t.re := by
      rw [hn]
      calc _ ≤ t.re * (M : ℝ)⁻¹ * M := mul_le_mul_of_nonneg_right this hMR.le
        _ = _ := by field_simp
    linarith
  have hu1 : t.re - n * M < M := by
    have := Int.lt_floor_add_one (t.re / M)
    have h2 : t.re < ((n : ℝ) + 1) * M := by
      rw [div_lt_iff₀ hMR] at this
      exact this
    linarith
  have him' : 0 < ((t : ℂ) - (n : ℂ) * (M : ℝ)).im := by simpa using t.im_pos
  set t' : ℍ := ⟨(t : ℂ) - (n : ℂ) * (M : ℝ), him'⟩ with ht'
  have hsame : (fS c ∣[(k : ℤ)] δ) t = (fS c ∣[(k : ℤ)] δ) t' := by
    have h := hper.sub_zsmul_eq (x := (t : ℂ)) n
    simp only [comp_apply] at h
    have e : ((t : ℂ) - n • (((M : ℝ) : ℂ))) = (t : ℂ) - (n : ℂ) * (M : ℝ) := by
      simp
    rw [e, ofComplex_apply_of_im_pos him', ofComplex_apply] at h
    exact h.symm
  have hv : t'.im = t.im := by
    change ((t : ℂ) - (n : ℂ) * (M : ℝ)).im = t.im
    simp
  have hu : t'.re = t.re - n * M := by
    change ((t : ℂ) - (n : ℂ) * (M : ℝ)).re = _
    simp
  rw [hsame, ModularForm.SL_slash_apply]
  set v := t.im with hvdef
  have hv1 : 1 ≤ v := ht
  have hvpos : 0 < v := by linarith
  set J := denom δ t' with hJ
  have hJne : J ≠ 0 := denom_ne_zero _ _
  have hJe : J = ((cc * t'.re + dd : ℝ) : ℂ) + ((cc * v : ℝ) : ℂ) * Complex.I := by
    have e : J = ((δ 1 0 : ℤ) : ℂ) * (t' : ℂ) + ((δ 1 1 : ℤ) : ℂ) := by
      simp [hJ, denom]
    have hcr : ((δ 1 0 : ℤ) : ℝ) = cc := rfl
    have hdr : ((δ 1 1 : ℤ) : ℝ) = dd := rfl
    have hre' : (t' : ℂ).re = t'.re := rfl
    have him'' : (t' : ℂ).im = v := hv
    rw [e]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre', him'', hcr, hdr]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre', him'', hcr]
      ring
  have hnorm : ‖J‖ ^ 2 = (cc * t'.re + dd) ^ 2 + (cc * v) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hJe, Complex.normSq_add_mul_I]
  have hupper : ‖J‖ ^ 2 ≤ A * v ^ 2 := by
    rw [hnorm, hA]
    have hu' : |cc * t'.re + dd| ≤ |cc| * M + |dd| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      gcongr
      rw [hu, abs_of_nonneg hu0]
      exact hu1.le
    have h1 : (cc * t'.re + dd) ^ 2 ≤ (|cc| * M + |dd|) ^ 2 := by
      rw [← sq_abs (cc * t'.re + dd)]
      gcongr
    have h2 : 1 ≤ v ^ 2 := one_le_pow₀ hv1
    have h3 : 0 ≤ (|cc| * M + |dd|) ^ 2 := by positivity
    nlinarith
  have hlower : 1 ≤ ‖J‖ := by
    have hint : (1 : ℝ) ≤ ‖J‖ ^ 2 := by
      rw [hnorm]
      by_cases h0 : δ 1 0 = 0
      · have hdet := δ.property
        rw [Matrix.det_fin_two, h0] at hdet
        have hd1 : δ 1 1 ∣ 1 := ⟨δ 0 0, by linarith⟩
        have hd2 : (δ 1 1) ^ 2 = 1 := by
          rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd1) with h | h <;> rw [h] <;> norm_num
        have hd3 : dd ^ 2 = 1 := by
          rw [hdd]
          exact_mod_cast hd2
        have hc0 : cc = 0 := by rw [hcc, h0]; simp
        rw [hc0]
        nlinarith
      · have hsq : (1 : ℤ) ≤ (δ 1 0) ^ 2 := by
          have := sq_nonneg (δ 1 0)
          have h2 : (δ 1 0) ^ 2 ≠ 0 := pow_ne_zero 2 h0
          omega
        have hsqR : (1 : ℝ) ≤ cc ^ 2 := by
          rw [hcc]
          exact_mod_cast hsq
        have h2 : 1 ≤ v ^ 2 := one_le_pow₀ hv1
        have h3 := sq_nonneg (cc * t'.re + dd)
        rw [mul_pow]
        nlinarith
    by_contra hc
    have : ‖J‖ ^ 2 < 1 := by
      have h1 := norm_nonneg J
      nlinarith [not_le.mp hc]
    linarith
  have him2 : (δ • t').im = v / ‖J‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, hv]
  have hJpow : ‖J ^ (-(k : ℤ))‖ ≤ 1 := by
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hlower)
  have hmod := norm_fS_le c hc (δ • t')
  have hJpos : 0 < ‖J‖ ^ 2 := by positivity
  have hinvim : (π * (δ • t').im)⁻¹ ≤ A / π * v := by
    have e : (π * (δ • t').im)⁻¹ = ‖J‖ ^ 2 / (π * v) := by
      rw [him2]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    refine hupper.trans (le_of_eq ?_)
    field_simp
  have hpos2 : 0 ≤ (π * (δ • t').im)⁻¹ := by
    have := (δ • t').im_pos
    positivity
  have hvpow : 1 ≤ v ^ (K + 1) := one_le_pow₀ hv1
  have hc0 := norm_nonneg (c 0)
  rw [norm_mul]
  calc _ ≤ ‖fS c (δ • t')‖ * 1 := by gcongr
    _ ≤ ‖c 0‖ + C * (K ! : ℝ) * (π * (δ • t').im)⁻¹ ^ (K + 1) := by rw [mul_one]; exact hmod
    _ ≤ ‖c 0‖ + C * (K ! : ℝ) * (A / π * v) ^ (K + 1) := by gcongr
    _ = ‖c 0‖ + C * (K ! : ℝ) * (A / π) ^ (K + 1) * v ^ (K + 1) := by rw [mul_pow]; ring
    _ ≤ ‖c 0‖ * v ^ (K + 1) + C * (K ! : ℝ) * (A / π) ^ (K + 1) * v ^ (K + 1) := by
      have := mul_le_mul_of_nonneg_left hvpow hc0
      linarith
    _ = _ := by rw [hB]; ring

/-- **A modular form from a `q`-series.** -/
theorem exists_form {k : ℕ} {M : ℕ} [NeZero M] (hc : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ K)
    (hinv : ∀ ε : SL(2, ℤ), (M : ℤ) ∣ ε 1 0 → fS c ∣[(k : ℤ)] ε = fS c) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) (k : ℤ),
      qExpansion (1 : ℝ) g = PowerSeries.mk c := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  let g : ModularForm (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :=
    { toFun := fS c
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        exact hinv γ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ)
      holo' := (good_fS c hc).holo
      bdd_at_cusps' := by
        intro x hx
        have hx' : IsCusp x 𝒮ℒ := by
          rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hx
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hx']
        intro δ _
        exact slash_bdd c hM hc hinv δ }
  exact ⟨g, qExp_fS c hc⟩

end

end RamanujanTau.ThetaLift
