/-
# The Hardy–Ramanujan asymptotic formula

**`p(n) ~ e^{π√(2n/3)} / (4n√3)`** (Hardy–Ramanujan 1918).

`2πp(n) = ∫_{−π}^{π} F(e^{−z})e^{nz} dθ` with `z = t + iθ`, `t = π/√(6n)`, `A = nt`.
* major arc `|θ| ≤ t`: `F(e^{−z}) = √(z/2π)e^{π²/(6z) − z/24}F(e^{−4π²/z})`. The main part is
  `(t/√A)·√(t/2π)·e^{2A}·J_n` with `J_n → √π` (Laplace), and `F(e^{−4π²/z}) − 1 = O(e^{−2π²/t})`;
* minor arc `t ≤ |θ| ≤ π`: `‖F(e^{−z})‖ ≤ ‖F(e^{−t})‖e^{−1/(200t)}`.
The normalizing factor `4√3 n e^{−2A}/(2π)` times the main part is exactly `J_n/√π`; the error terms are
`O(n e^{−c√n})`.
-/
import RamanujanTau.HardyRamanujan.Bounds

set_option autoImplicit false

namespace HardyRamanujan
open Complex Filter Metric MeasureTheory intervalIntegral
open scoped Real Topology

/-! ### continuity -/

lemma cexp_zt_mem {t : ℝ} (ht : 0 < t) (θ : ℝ) : cexp (-zt t θ) ∈ ball (0 : ℂ) 1 :=
  norm_cexp_neg_lt_one (by simp [zt]; exact ht)

lemma g_cont (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous fun θ : ℝ => F (cexp (-zt t θ)) * cexp (n * zt t θ) := by
  have h1 : Continuous fun θ : ℝ => F (cexp (-zt t θ)) :=
    F_diff.continuousOn.comp_continuous (by fun_prop) (cexp_zt_mem ht)
  exact h1.mul (by fun_prop)

lemma zt_mem_slit {t : ℝ} (ht : 0 < t) (θ : ℝ) : zt t θ / (2 * π) ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
  simp [zt]; positivity

lemma Mfun_cont (n : ℕ) {t : ℝ} (ht : 0 < t) : Continuous fun θ : ℝ => Mfun n t θ := by
  unfold Mfun sq
  have hl : Continuous fun θ : ℝ => log (zt t θ / (2 * π)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      ContinuousAt.clog (f := fun θ : ℝ => zt t θ / (2 * π)) (by fun_prop) (zt_mem_slit ht θ)
  have hd : Continuous fun θ : ℝ => (π : ℂ) ^ 2 / (6 * zt t θ) :=
    continuous_const.div (by fun_prop) fun θ => mul_ne_zero (by norm_num) (zt_ne_zero ht)
  fun_prop

lemma g_eq_major (n : ℕ) {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    F (cexp (-zt t θ)) * cexp (n * zt t θ) =
      Mfun n t θ + Mfun n t θ * (F (cexp (-(4 * π ^ 2 / zt t θ))) - 1) := by
  rw [F_modular (by simp [zt]; exact ht), Mfun]; ring

/-! ### the normalization -/

/-- `P_n = (4√3 n/2π)·(t/√A)·√(t/2π)`. -/
noncomputable def Pn (n : ℕ) : ℝ := 4 * √3 * n / (2 * π) * (tn n / √(An n)) * √(tn n / (2 * π))

lemma Pn_eq {n : ℕ} (hn : 1 ≤ n) : Pn n = 1 / √π := by
  have ht := tn_pos hn
  have hA := An_pos hn
  have hπ := Real.pi_pos
  have hP : 0 < Pn n := by unfold Pn; positivity
  have hsq : Pn n ^ 2 = 1 / π := by
    have h6 : (0 : ℝ) < 6 * n := by positivity
    have ht2 : tn n ^ 2 = π ^ 2 / (6 * n) := by
      unfold tn; rw [div_pow, Real.sq_sqrt h6.le]
    have s1 : √(An n) ^ 2 = An n := Real.sq_sqrt hA.le
    have s2 : √(tn n / (2 * π)) ^ 2 = tn n / (2 * π) := Real.sq_sqrt (by positivity)
    have s3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsA : 0 < √(An n) := Real.sqrt_pos.mpr hA
    have e : Pn n ^ 2 = (4 * n / (2 * π)) ^ 2 * √3 ^ 2 * (tn n ^ 2 / √(An n) ^ 2) * √(tn n / (2 * π)) ^ 2 := by
      unfold Pn; field_simp
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [e, s1, s2, s3]
    unfold An
    have htn : tn n ≠ 0 := ht.ne'
    field_simp
    rw [ht2]
    field_simp
    ring
  have h1 : 0 < 1 / √π := by positivity
  have h2 : (1 / √π) ^ 2 = 1 / π := by rw [div_pow, Real.sq_sqrt hπ.le, one_pow]
  nlinarith [sq_nonneg (Pn n - 1 / √π), sq_nonneg (Pn n + 1 / √π)]

/-- the main-arc integral. -/
lemma major_main {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (-tn n)..tn n, Mfun n (tn n) θ = ((tn n / √(An n) * √(tn n / (2 * π)) * Real.exp (2 * An n) : ℝ) : ℂ) *
      ∫ v in (-√(An n))..√(An n), hfun (v / √(An n)) (tn n) v := by
  have ht := tn_pos hn
  have hA := An_pos hn
  have hsA : 0 < √(An n) := Real.sqrt_pos.mpr hA
  set c : ℝ := tn n / √(An n) with hc
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  have hsub := intervalIntegral.integral_comp_mul_left (fun θ => Mfun n (tn n) θ) hc0
    (a := -√(An n)) (b := √(An n))
  have hcA : c * √(An n) = tn n := by rw [hc]; field_simp
  rw [mul_neg, hcA] at hsub
  have : ∫ θ in (-tn n)..tn n, Mfun n (tn n) θ = c • ∫ v in (-√(An n))..√(An n), Mfun n (tn n) (c * v) := by
    rw [hsub, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [this]
  simp only [hc, Mfun_scale hn]
  rw [intervalIntegral.integral_const_mul, Complex.real_smul]
  push_cast; ring

/-! ### the error terms -/

lemma tendsto_n_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(c / tn n))) atTop (𝓝 0) := by
  set κ : ℝ := c * √6 / π with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hct : ∀ n : ℕ, 1 ≤ n → c / tn n = κ * √n := by
    intro n hn
    unfold tn
    rw [hκ, Real.sqrt_mul (by norm_num)]
    field_simp
  have hsq : Tendsto (fun n : ℕ => κ * √(n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ0
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hsq).const_mul (1 / κ ^ 2)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp, hct n hn]
  have : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  field_simp
  try rw [mul_pow]
  try rw [this]
  try ring

/-! ### the theorem -/

/-- the normalized coefficient `(4√3 n e^{−2A}) p(n)`. -/
noncomputable def Kn (n : ℕ) : ℝ := 4 * √3 * n / Real.exp (2 * An n)

lemma tn_le_half : ∀ᶠ n : ℕ in atTop, tn n ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop 7] with n hn
  unfold tn
  have h6 : (0 : ℝ) < 6 * n := by positivity
  have hs : 2 * π ≤ √(6 * n) := by
    rw [Real.le_sqrt (by positivity) h6.le]
    have : (7 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr h6)]; linarith

lemma tn_tendsto : Tendsto tn atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => √(6 * (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  exact tendsto_const_nhds.div_atTop this

lemma An_tendsto : Tendsto An atTop atTop := by
  have h : ∀ n : ℕ, 1 ≤ n → An n = π / √6 * √(n : ℝ) := by
    intro n hn
    unfold An tn
    rw [Real.sqrt_mul (by norm_num)]
    have : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    field_simp
    rw [this]
  have h2 : Tendsto (fun n : ℕ => π / √6 * √(n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (h n hn).symm

/-- **the decomposition** `K_n p(n) = P_n J_n + E₁ + E₂`. -/
lemma decomp {n : ℕ} (hn : 1 ≤ n) (ht2 : tn n ≤ 1 / 2) :
    ((Kn n * p n : ℝ) : ℂ) = (Pn n : ℂ) * (∫ v in (-√(An n))..√(An n), hfun (v / √(An n)) (tn n) v) +
      ((Kn n / (2 * π) : ℝ) : ℂ) * ((∫ θ in (-tn n)..tn n, Mfun n (tn n) θ * (F (cexp (-(4 * π ^ 2 / zt (tn n) θ))) - 1))
        + ((∫ θ in (-π)..(-tn n), F (cexp (-zt (tn n) θ)) * cexp (n * zt (tn n) θ)) +
          ∫ θ in (tn n)..π, F (cexp (-zt (tn n) θ)) * cexp (n * zt (tn n) θ))) := by
  have ht := tn_pos hn
  have htπ : tn n ≤ π := by linarith [Real.pi_gt_three]
  have hcoef := coeff_integral n ht
  set g := fun θ : ℝ => F (cexp (-zt (tn n) θ)) * cexp (n * zt (tn n) θ) with hg
  have hgc := g_cont n ht
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  have hsplit : ∫ θ in (-π)..π, g θ = (∫ θ in (-π)..(-tn n), g θ) + (∫ θ in (-tn n)..tn n, g θ) +
      ∫ θ in (tn n)..π, g θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hMc := Mfun_cont n ht
  have hEint : IntervalIntegrable (fun θ => Mfun n (tn n) θ * (F (cexp (-(4 * π ^ 2 / zt (tn n) θ))) - 1))
      volume (-tn n) (tn n) := by
    have : (fun θ => Mfun n (tn n) θ * (F (cexp (-(4 * π ^ 2 / zt (tn n) θ))) - 1)) =
        fun θ => g θ - Mfun n (tn n) θ := by
      funext θ; rw [hg]; simp only; rw [g_eq_major n ht θ]; ring
    rw [this]; exact (hint _ _).sub (hMc.intervalIntegrable _ _)
  have hmaj : ∫ θ in (-tn n)..tn n, g θ = (∫ θ in (-tn n)..tn n, Mfun n (tn n) θ) +
      ∫ θ in (-tn n)..tn n, Mfun n (tn n) θ * (F (cexp (-(4 * π ^ 2 / zt (tn n) θ))) - 1) := by
    rw [← intervalIntegral.integral_add (hMc.intervalIntegrable _ _) hEint]
    congr 1; funext θ; rw [hg]; simp only; rw [g_eq_major n ht θ]
  rw [hsplit, hmaj, major_main hn] at hcoef
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hK : ((Kn n * p n : ℝ) : ℂ) = ((Kn n / (2 * π) : ℝ) : ℂ) * ((2 * π : ℂ) * p n) := by
    push_cast; field_simp
  rw [hK, hcoef]
  have hP : (Pn n : ℂ) = ((Kn n / (2 * π) : ℝ) : ℂ) *
      ((tn n / √(An n) * √(tn n / (2 * π)) * Real.exp (2 * An n) : ℝ) : ℂ) := by
    unfold Pn Kn
    have : Real.exp (2 * An n) ≠ 0 := (Real.exp_pos _).ne'
    push_cast
    field_simp
  rw [hP]
  ring

/-- **The Hardy–Ramanujan asymptotic formula**: `p(n)·4√3 n / e^{π√(2n/3)} → 1`. -/
theorem hardy_ramanujan :
    Tendsto (fun n : ℕ => (p n : ℝ) * (4 * √3 * n) / Real.exp (π * √(2 * n / 3))) atTop (𝓝 1) := by
  -- the complex statement
  have hJ := J_tendsto (A := fun n => An (n + 1)) (t := fun n => tn (n + 1))
    (An_tendsto.comp (tendsto_add_atTop_nat 1)) (fun n => An_pos (by omega))
    (tn_tendsto.comp (tendsto_add_atTop_nat 1)) (fun n => (tn_pos (by omega)).le)
  simp only at hJ
  rw [← tendsto_add_atTop_iff_nat 1]
  -- main term → 1
  have hmain : Tendsto (fun n : ℕ => (Pn (n + 1) : ℂ) * ∫ v in (-√(An (n + 1)))..√(An (n + 1)),
      hfun (v / √(An (n + 1))) (tn (n + 1)) v) atTop (𝓝 1) := by
    have hP : ∀ n : ℕ, (Pn (n + 1) : ℂ) = ((1 / √π : ℝ) : ℂ) := fun n => by rw [Pn_eq (by omega)]
    simp only [hP]
    have := hJ.const_mul ((1 / √π : ℝ) : ℂ)
    convert this using 2
    have : (√π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    push_cast; field_simp
  -- error terms → 0
  set E : ℕ → ℂ := fun n => ((Kn (n + 1) / (2 * π) : ℝ) : ℂ) *
    ((∫ θ in (-tn (n + 1))..tn (n + 1), Mfun (n + 1) (tn (n + 1)) θ *
        (F (cexp (-(4 * π ^ 2 / zt (tn (n + 1)) θ))) - 1)) +
      ((∫ θ in (-π)..(-tn (n + 1)), F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ)) +
        ∫ θ in (tn (n + 1))..π, F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ))) with hE
  have hbound : ∀ᶠ n : ℕ in atTop, ‖E n‖ ≤
      (4 * √3 / (2 * π) * (4 * C0)) * ((n + 1 : ℕ) * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) +
      (4 * √3 * (1 + C0)) * ((n + 1 : ℕ) * Real.exp (-(1 / 200 / tn (n + 1)))) := by
    have hev := (tendsto_add_atTop_nat 1).eventually tn_le_half
    filter_upwards [hev] with n ht2
    have hn : 1 ≤ n + 1 := by omega
    have ht := tn_pos hn
    have hK0 : 0 ≤ Kn (n + 1) / (2 * π) := by unfold Kn; positivity
    have h1 : ‖∫ θ in (-tn (n + 1))..tn (n + 1), Mfun (n + 1) (tn (n + 1)) θ *
        (F (cexp (-(4 * π ^ 2 / zt (tn (n + 1)) θ))) - 1)‖ ≤
        Real.exp (2 * An (n + 1)) * (2 * C0 * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) * (2 * tn (n + 1)) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := Real.exp (2 * An (n + 1)) * (2 * C0 * Real.exp (-(2 * π ^ 2 / tn (n + 1))))) fun θ hθ => ?_).trans
        (le_of_eq ?_)
      · refine major_err_bound hn ht2 ?_
        rw [Set.uIoc_of_le (by linarith)] at hθ
        rw [abs_le]; exact ⟨hθ.1.le, hθ.2⟩
      · rw [show tn (n + 1) - -tn (n + 1) = 2 * tn (n + 1) by ring, abs_of_pos (by linarith)]
    have hmin : ∀ a b : ℝ, (∀ θ ∈ Set.uIoc a b, tn (n + 1) ≤ |θ| ∧ |θ| ≤ π) → |b - a| ≤ π →
        ‖∫ θ in a..b, F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ)‖ ≤
          (1 + C0) * Real.exp (2 * An (n + 1)) * Real.exp (-(1 / (200 * tn (n + 1)))) * π := by
      intro a b hab hba
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := (1 + C0) * Real.exp (2 * An (n + 1)) * Real.exp (-(1 / (200 * tn (n + 1))))) fun θ hθ => ?_).trans ?_
      · exact minor_integrand_bound hn ht2 (hab θ hθ).1 (hab θ hθ).2
      · gcongr
        · have := C0_nonneg; positivity
    have hπ3 := Real.pi_gt_three
    have h2 := hmin (-π) (-tn (n + 1)) (fun θ hθ => by
      rw [Set.uIoc_of_le (by linarith)] at hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      have hneg : θ < 0 := by linarith
      rw [abs_of_neg hneg]; constructor <;> linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    have h3 := hmin (tn (n + 1)) π (fun θ hθ => by
      rw [Set.uIoc_of_le (by linarith)] at hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      have hpos : 0 < θ := by linarith
      rw [abs_of_pos hpos]; constructor <;> linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    rw [hE]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0]
    have hsum := norm_add_le (∫ θ in (-tn (n + 1))..tn (n + 1), Mfun (n + 1) (tn (n + 1)) θ *
        (F (cexp (-(4 * π ^ 2 / zt (tn (n + 1)) θ))) - 1))
      ((∫ θ in (-π)..(-tn (n + 1)), F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ)) +
        ∫ θ in (tn (n + 1))..π, F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ))
    have hsum2 := norm_add_le (∫ θ in (-π)..(-tn (n + 1)), F (cexp (-zt (tn (n + 1)) θ)) *
        cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ))
      (∫ θ in (tn (n + 1))..π, F (cexp (-zt (tn (n + 1)) θ)) * cexp ((n + 1 : ℕ) * zt (tn (n + 1)) θ))
    have hexp : Real.exp (2 * An (n + 1)) > 0 := Real.exp_pos _
    have hKe : Kn (n + 1) / (2 * π) * Real.exp (2 * An (n + 1)) = 4 * √3 * ((n + 1 : ℕ) : ℝ) / (2 * π) := by
      unfold Kn; field_simp
    have hdiv : 1 / (200 * tn (n + 1)) = 1 / 200 / tn (n + 1) := by field_simp
    calc Kn (n + 1) / (2 * π) * ‖_‖
        ≤ Kn (n + 1) / (2 * π) * (Real.exp (2 * An (n + 1)) * (2 * C0 * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) *
            (2 * tn (n + 1)) + ((1 + C0) * Real.exp (2 * An (n + 1)) * Real.exp (-(1 / (200 * tn (n + 1)))) * π +
            (1 + C0) * Real.exp (2 * An (n + 1)) * Real.exp (-(1 / (200 * tn (n + 1)))) * π)) := by
          gcongr
          exact hsum.trans (add_le_add h1 (hsum2.trans (add_le_add h2 h3)))
      _ = (Kn (n + 1) / (2 * π) * Real.exp (2 * An (n + 1))) * (4 * C0 * tn (n + 1) *
            Real.exp (-(2 * π ^ 2 / tn (n + 1)))) + (Kn (n + 1) / (2 * π) * Real.exp (2 * An (n + 1))) *
            (2 * π * (1 + C0) * Real.exp (-(1 / (200 * tn (n + 1))))) := by ring
      _ ≤ _ := by
          rw [hKe, hdiv]
          have hC := C0_nonneg
          have htle : tn (n + 1) ≤ 1 := by linarith
          have he1 : 0 ≤ Real.exp (-(2 * π ^ 2 / tn (n + 1))) := (Real.exp_pos _).le
          have hπ := Real.pi_pos
          have hfirst : 4 * √3 * ((n + 1 : ℕ) : ℝ) / (2 * π) * (4 * C0 * tn (n + 1) *
              Real.exp (-(2 * π ^ 2 / tn (n + 1)))) ≤ 4 * √3 / (2 * π) * (4 * C0) *
              (((n + 1 : ℕ) : ℝ) * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) := by
            have : 4 * √3 * ((n + 1 : ℕ) : ℝ) / (2 * π) * (4 * C0 * tn (n + 1) *
                Real.exp (-(2 * π ^ 2 / tn (n + 1)))) = 4 * √3 / (2 * π) * (4 * C0) *
                (((n + 1 : ℕ) : ℝ) * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) * tn (n + 1) := by ring
            rw [this]
            have h0 : 0 ≤ 4 * √3 / (2 * π) * (4 * C0) * (((n + 1 : ℕ) : ℝ) * Real.exp (-(2 * π ^ 2 / tn (n + 1)))) := by
              positivity
            nlinarith
          have hsecond : 4 * √3 * ((n + 1 : ℕ) : ℝ) / (2 * π) * (2 * π * (1 + C0) *
              Real.exp (-(1 / 200 / tn (n + 1)))) = 4 * √3 * (1 + C0) *
              (((n + 1 : ℕ) : ℝ) * Real.exp (-(1 / 200 / tn (n + 1)))) := by
            field_simp
          linarith
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have h1 := ((tendsto_n_exp (c := 2 * π ^ 2) (by positivity)).comp (tendsto_add_atTop_nat 1)).const_mul
      (4 * √3 / (2 * π) * (4 * C0))
    have h2 := ((tendsto_n_exp (c := 1 / 200) (by norm_num)).comp (tendsto_add_atTop_nat 1)).const_mul
      (4 * √3 * (1 + C0))
    have h12 := h1.add h2
    simp only [mul_zero, add_zero, Function.comp] at h12
    refine squeeze_zero_norm' hbound ?_
    convert h12 using 2
  -- assemble
  have hsum := hmain.add hE0
  rw [add_zero] at hsum
  have hC : Tendsto (fun n : ℕ => ((Kn (n + 1) * p (n + 1) : ℝ) : ℂ)) atTop (𝓝 1) := by
    refine hsum.congr' ?_
    have hev := (tendsto_add_atTop_nat 1).eventually tn_le_half
    filter_upwards [hev] with n ht2
    rw [decomp (by omega) ht2]
  have hR : Tendsto (fun n : ℕ => Kn (n + 1) * p (n + 1)) atTop (𝓝 1) := by
    have := (Complex.continuous_re.tendsto _).comp hC
    simpa [Function.comp_def] using this
  refine hR.congr fun n => ?_
  unfold Kn
  rw [← two_An (by omega)]
  push_cast
  ring

/-- **Hardy–Ramanujan**, as an asymptotic equivalence: `p(n) ~ e^{π√(2n/3)}/(4n√3)`. -/
theorem hardy_ramanujan_isEquivalent :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (p n : ℝ))
      (fun n : ℕ => Real.exp (π * √(2 * n / 3)) / (4 * √3 * n)) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  · refine hardy_ramanujan.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.div_apply]
    field_simp

end HardyRamanujan
