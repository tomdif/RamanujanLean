/-
# A double-exponential kernel and a pointwise lower bound for `∫ |L(Δ,6+it)|` over short windows

Kernel `ψ(z) = exp(−exp(z²))`.  It is entire, `0 < ψ(x) ≤ 1` on `ℝ`, `ψ(x) ≥ e^{−3}` for `|x| ≤ 1`,
and on thin strips it decays doubly exponentially: for `|y| ≤ 1/2`, `|xy| ≤ 1/2`,
`|ψ(x+iy)| ≤ exp(−e^{x²}/4) ≤ 4/(1+x²)`.

Contour shift of `(L(Δ,s) − 1) ψ((s − 6 − it₀)/(ih))` around `[6,σ₁] × [t₀−κh, t₀+κh]`, where
`‖L(Δ,σ₁+iy) − 1‖ ≤ e^{−3}/(8π)` (far right), gives

    h e^{−3} ≤ ∫_{t₀−κh}^{t₀+κh} |L(Δ,6+it)| dt

as soon as `2κβ ≤ h` (`β = σ₁ − 6`) and the horizontal sides, of size
`≪ T exp(−e^{κ²}/4)` by convexity, are `≤ e^{−3}/4`.  This needs only `κ ≍ √(log log T)`:
the double-exponential decay of the kernel is what replaces the Hardy–Littlewood mean-square
estimate for the horizontal sides.
-/
import RamanujanTau.HardyCount.Contour

set_option autoImplicit false

namespace RamanujanTau.HardyCountLinear

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HardyCount
open scoped Real

/-- `‖L(Δ, σ₁ + iy) − 1‖ ≤ ρ` on some line `Re s = σ₁ ≥ 7`. -/
theorem norm_tauL_sub_one_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ σ₁ : ℝ, 7 ≤ σ₁ ∧ ∀ y : ℝ, ‖tauL (σ₁ + y * I) - 1‖ ≤ ρ := by
  have hsum7 : LSeriesSummable tauC (7 : ℂ) := LSeriesSummable_tau_of_gt_13_2 (by norm_num)
  set S : ℝ := ∑' n, ‖LSeries.term tauC 7 n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ρ / (S + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨7 + k, by linarith [Nat.cast_nonneg (α := ℝ) k], fun y => ?_⟩
  set s : ℂ := ((7 + k : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = 7 + k := by simp [hs]
  have hsum : LSeriesSummable tauC s :=
    LSeriesSummable_tau_of_gt_13_2 (by rw [hsre]; linarith [Nat.cast_nonneg (α := ℝ) k])
  rw [tauL_eq_LSeries_of_gt (by rw [hsre]; linarith [Nat.cast_nonneg (α := ℝ) k]), LSeries,
    hsum.tsum_eq_add_tsum_ite 1]
  have h1 : LSeries.term tauC s 1 = 1 := by
    rw [LSeries.term_def]; simp [tauC, RamanujanTau.tau_one]
  rw [h1, add_sub_cancel_left]
  have hpt : ∀ n : ℕ, ‖(if n = 1 then 0 else LSeries.term tauC s n)‖ ≤
      (1 / 2) ^ k * ‖LSeries.term tauC 7 n‖ := by
    intro n
    split_ifs with hn1
    · simp only [norm_zero]; positivity
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp
    have hn2 : (2 : ℝ) ≤ n := by
      have : 2 ≤ n := by omega
      exact_mod_cast this
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg (by omega), if_neg (by omega), hsre]
    have e7 : ((7 : ℂ)).re = 7 := by norm_num
    rw [e7]
    have hnp : (0 : ℝ) < n := by linarith
    have hsplit : (n : ℝ) ^ ((7 : ℝ) + k) = (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k := by
      rw [Real.rpow_add hnp, Real.rpow_natCast]
    rw [hsplit]
    have hnk : (2 : ℝ) ^ k ≤ (n : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hn2 k
    have h7 : 0 < (n : ℝ) ^ (7 : ℝ) := Real.rpow_pos_of_pos hnp _
    have hk2 : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
    rw [hk2]
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc ‖tauC n‖ = ‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ) := by field_simp
      _ ≤ 1 / 2 ^ k * (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k) := by
        rw [show 1 / 2 ^ k * (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k) =
          (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ k / 2 ^ k) by
            field_simp]
        have : 1 ≤ (n : ℝ) ^ k / 2 ^ k := by rw [le_div_iff₀ h2k]; linarith
        have h0 : 0 ≤ ‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ) := by positivity
        nlinarith
  have hsum7' : Summable fun n => (1 / 2 : ℝ) ^ k * ‖LSeries.term tauC 7 n‖ :=
    hsum7.norm.mul_left _
  have hnorm : Summable fun n : ℕ => ‖(if n = 1 then 0 else LSeries.term tauC s n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum7'
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (Summable.tsum_le_tsum hpt hnorm hsum7').trans ?_
  rw [tsum_mul_left, ← hS]
  have h := hk.le
  rw [le_div_iff₀ (by positivity)] at h
  have : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  nlinarith

/-- The kernel `ψ(z) = exp(−exp(z²))`. -/
noncomputable def kerC (z : ℂ) : ℂ := cexp (-cexp (z ^ 2))

lemma kerC_entire : Differentiable ℂ kerC := by unfold kerC; fun_prop

lemma norm_kerC (z : ℂ) : ‖kerC z‖ = Real.exp (-(cexp (z ^ 2)).re) := by
  rw [kerC, Complex.norm_exp, Complex.neg_re]

lemma re_cexp_sq_ge {x y : ℝ} (hy : |y| ≤ 1 / 2) (hxy : |x * y| ≤ 1 / 2) :
    Real.exp (x ^ 2) / 4 ≤ (cexp (((x : ℂ) + y * I) ^ 2)).re := by
  have e : ((x : ℂ) + y * I) ^ 2 = ((x ^ 2 - y ^ 2 : ℝ) : ℂ) + ((2 * x * y : ℝ) : ℂ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hre : (((x ^ 2 - y ^ 2 : ℝ) : ℂ) + ((2 * x * y : ℝ) : ℂ) * I).re = x ^ 2 - y ^ 2 := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re]; ring
  have him : (((x ^ 2 - y ^ 2 : ℝ) : ℂ) + ((2 * x * y : ℝ) : ℂ) * I).im = 2 * x * y := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im]; ring
  rw [e, Complex.exp_re, hre, him]
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_abs y
    nlinarith [abs_nonneg y]
  have hE : 3 / 4 ≤ Real.exp (-y ^ 2) := by
    have := Real.add_one_le_exp (-y ^ 2); linarith
  have hc : 1 / 2 ≤ Real.cos (2 * x * y) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * x * y)
    have h2 : (2 * x * y) ^ 2 ≤ 1 := by
      have : |2 * x * y| ≤ 1 := by
        rw [show 2 * x * y = 2 * (x * y) by ring, abs_mul, abs_two]; linarith
      have := sq_abs (2 * x * y)
      nlinarith [abs_nonneg (2 * x * y)]
    linarith
  rw [sub_eq_add_neg, Real.exp_add]
  have hx := Real.exp_pos (x ^ 2)
  have h3 : 3 / 4 * (1 / 2) ≤ Real.exp (-y ^ 2) * Real.cos (2 * x * y) :=
    mul_le_mul hE hc (by norm_num) (Real.exp_pos _).le
  have h4 := mul_le_mul_of_nonneg_left h3 hx.le
  nlinarith

lemma norm_kerC_le {x y : ℝ} (hy : |y| ≤ 1 / 2) (hxy : |x * y| ≤ 1 / 2) :
    ‖kerC (x + y * I)‖ ≤ Real.exp (-(Real.exp (x ^ 2) / 4)) := by
  rw [norm_kerC]
  exact Real.exp_le_exp.mpr (by linarith [re_cexp_sq_ge hy hxy])

lemma exp_neg_exp_sq_le (x : ℝ) : Real.exp (-(Real.exp (x ^ 2) / 4)) ≤ 4 * (1 + x ^ 2)⁻¹ := by
  set a := Real.exp (x ^ 2) / 4 with ha
  have ha1 : 1 + x ^ 2 ≤ 4 * a := by have := Real.add_one_le_exp (x ^ 2); rw [ha]; linarith
  have h1 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hpos := Real.exp_pos (-a)
  nlinarith

lemma kerC_ofReal (x : ℝ) : kerC x = ((Real.exp (-Real.exp (x ^ 2)) : ℝ) : ℂ) := by
  rw [kerC, show (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_exp,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp]

lemma arg_eq {h : ℝ} (hh : h ≠ 0) (σ t t₀ : ℝ) :
    ((σ : ℂ) + t * I - (6 + t₀ * I)) * (-I) / h =
      (((t - t₀) / h : ℝ) : ℂ) + ((-(σ - 6) / h : ℝ) : ℂ) * I := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

lemma psi_le_one (t₀ h t : ℝ) : Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith [Real.exp_pos (((t - t₀) / h) ^ 2)]

lemma main_term {t₀ h κ : ℝ} (hh : 0 < h) (hκ : 1 ≤ κ) :
    2 * h * Real.exp (-3) ≤
      ∫ t in (t₀ - κ * h)..(t₀ + κ * h), Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) := by
  have hc : Continuous fun t : ℝ => Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) := by fun_prop
  have hκh' : h ≤ κ * h := le_mul_of_one_le_left hh.le hκ
  have hsub : (∫ t in (t₀ - h)..(t₀ + h), Real.exp (-Real.exp (((t - t₀) / h) ^ 2))) ≤
      ∫ t in (t₀ - κ * h)..(t₀ + κ * h), Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun t => (Real.exp_pos _).le) (hc.intervalIntegrable (μ := volume) _ _)
  refine le_trans ?_ hsub
  have hlow : ∀ t ∈ Icc (t₀ - h) (t₀ + h),
      Real.exp (-3) ≤ Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) := by
    intro t ht
    apply Real.exp_le_exp.mpr
    have hx : ((t - t₀) / h) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity)]
      have : |t - t₀| ≤ h := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have := sq_abs (t - t₀)
      nlinarith [abs_nonneg (t - t₀)]
    have : Real.exp (((t - t₀) / h) ^ 2) ≤ 3 := by
      calc Real.exp (((t - t₀) / h) ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hx
        _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have := intervalIntegral.integral_mono_on (by linarith : t₀ - h ≤ t₀ + h)
    (intervalIntegrable_const (c := Real.exp (-3))) (hc.intervalIntegrable (μ := volume) _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma integral_inv_one_add_div_sq_le {t₀ h : ℝ} (hh : 0 < h) (a b : ℝ) :
    (∫ y in a..b, (1 + ((y - t₀) / h) ^ 2)⁻¹) ≤ h * π := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => (1 + (u / h) ^ 2)⁻¹) t₀,
    intervalIntegral.integral_comp_div (fun v => (1 + v ^ 2)⁻¹) hh.ne']
  have := integral_inv_one_add_sq (a := (a - t₀) / h) (b := (b - t₀) / h)
  simp only [smul_eq_mul]
  rw [show (∫ x in (a - t₀) / h..(b - t₀) / h, (1 + x ^ 2)⁻¹) =
    Real.arctan ((b - t₀) / h) - Real.arctan ((a - t₀) / h) by simp [this]]
  have := Real.arctan_lt_pi_div_two ((b - t₀) / h)
  have := Real.neg_pi_div_two_lt_arctan ((a - t₀) / h)
  nlinarith

/-- **Pointwise lower bound for `∫ |L(Δ, 6+it)|` over windows of length `2κh`.** -/
theorem kernel_lower : ∃ β C : ℝ, 0 < β ∧ 0 ≤ C ∧ ∀ T t₀ h κ : ℝ, 1 ≤ T → T ≤ t₀ →
    t₀ ≤ 2 * T → 1 ≤ h → 1 ≤ κ → 2 * κ * β ≤ h → κ * h ≤ T →
    (4 * C + 1) * β * T * Real.exp (-(Real.exp (κ ^ 2) / 4)) ≤ Real.exp (-3) / 4 →
    h * Real.exp (-3) ≤ ∫ t in (t₀ - κ * h)..(t₀ + κ * h), ‖tauL (6 + t * I)‖ := by
  obtain ⟨σ₁, hσ₁, hρ⟩ := norm_tauL_sub_one_le (ρ := Real.exp (-3) / (8 * π)) (by positivity)
  obtain ⟨C, hC0, hC⟩ := tauL_right_half_bound (ε := 1 / 2) (by norm_num) le_rfl
  have hC' : ∀ σ t : ℝ, 6 ≤ σ → ‖tauL ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) := by
    intro σ t hσ
    have := hC σ t hσ
    rwa [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at this
  refine ⟨σ₁ - 6, C, by linarith, hC0, fun T t₀ h κ hT ht₀ ht₀' hh hκ hβ hκh hsmall => ?_⟩
  set β : ℝ := σ₁ - 6 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hhpos : 0 < h := by linarith
  set a : ℝ := t₀ - κ * h with ha
  set b : ℝ := t₀ + κ * h with hb
  have hκh0 : 0 ≤ κ * h := by positivity
  have hab : a ≤ b := by rw [ha, hb]; linarith
  set K : ℂ → ℂ := fun s => kerC ((s - (6 + t₀ * I)) * (-I) / h) with hKdef
  set f : ℂ → ℂ := fun s => (tauL s - 1) * K s with hfdef
  have hKd : Differentiable ℂ K := kerC_entire.comp (by fun_prop)
  have hfd : Differentiable ℂ f := (tauLSeries_entire.sub_const 1).mul hKd
  have hK : ∀ σ t : ℝ, K (σ + t * I) =
      kerC ((((t - t₀) / h : ℝ) : ℂ) + ((-(σ - 6) / h : ℝ) : ℂ) * I) := by
    intro σ t; simp only [hKdef]; rw [arg_eq hhpos.ne']
  have hK6 : ∀ t : ℝ, K ((6 : ℝ) + t * I) = ((Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) : ℝ) : ℂ) := by
    intro t
    rw [hK, show (-((6 : ℝ) - 6) / h : ℝ) = 0 by ring, Complex.ofReal_zero, zero_mul, add_zero,
      kerC_ofReal]
  -- bounds on `‖K‖` on the right line and the horizontal sides
  have hyb : ∀ σ : ℝ, 6 ≤ σ → σ ≤ σ₁ → |(-(σ - 6) / h)| ≤ β / h := by
    intro σ h6 h1
    rw [abs_div, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 6), abs_of_pos hhpos]
    gcongr; rw [hβdef]; linarith
  have hβh : β / h ≤ 1 / (2 * κ) := by
    rw [div_le_div_iff₀ hhpos (by positivity)]; linarith
  have hβh2 : κ * (β / h) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hβh (by linarith : (0 : ℝ) ≤ κ)
    rwa [show κ * (1 / (2 * κ)) = 1 / 2 by field_simp] at this
  have hKle : ∀ σ t : ℝ, 6 ≤ σ → σ ≤ σ₁ → |(t - t₀) / h| ≤ κ →
      ‖K (σ + t * I)‖ ≤ Real.exp (-(Real.exp (((t - t₀) / h) ^ 2) / 4)) := by
    intro σ t h6 h1 hx
    rw [hK]
    have hy := hyb σ h6 h1
    refine norm_kerC_le ?_ ?_
    · refine hy.trans (hβh.trans ?_)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    · rw [abs_mul]
      calc |(t - t₀) / h| * |(-(σ - 6) / h)| ≤ κ * (β / h) :=
            mul_le_mul hx hy (abs_nonneg _) (by linarith)
        _ ≤ 1 / 2 := hβh2
  -- the rectangle
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((6 : ℂ) + a * I) ((σ₁ : ℂ) + b * I) hfd.differentiableOn
  have e1 : ((6 : ℂ) + a * I).re = 6 := by simp
  have e2 : ((6 : ℂ) + a * I).im = a := by simp
  have e3 : ((σ₁ : ℂ) + b * I).re = σ₁ := by simp
  have e4 : ((σ₁ : ℂ) + b * I).im = b := by simp
  rw [e1, e2, e3, e4] at hrect
  set Ha := ∫ x : ℝ in (6 : ℝ)..σ₁, f (x + a * I) with hHa
  set Hb := ∫ x : ℝ in (6 : ℝ)..σ₁, f (x + b * I) with hHb
  set X := ∫ y : ℝ in a..b, f (σ₁ + y * I) with hX
  set Y := ∫ y : ℝ in a..b, f (((6 : ℝ) : ℂ) + y * I) with hY
  have hEq : I • Y = Ha - Hb + I • X := by linear_combination -hrect
  -- horizontal sides
  have hside : ∀ c : ℝ, (c = a ∨ c = b) →
      ‖∫ x : ℝ in (6 : ℝ)..σ₁, f (x + c * I)‖ ≤ Real.exp (-3) / 4 := by
    intro c hc
    have hc0 : 0 ≤ c := by rcases hc with hc | hc <;> rw [hc] <;> [rw [ha]; rw [hb]] <;> linarith
    have hc3 : c ≤ 3 * T := by rcases hc with hc | hc <;> rw [hc] <;> [rw [ha]; rw [hb]] <;> linarith
    have hcx : ((c - t₀) / h) ^ 2 = κ ^ 2 := by
      rcases hc with hc | hc <;> rw [hc] <;> [rw [ha]; rw [hb]] <;> field_simp <;> ring
    have hcx' : |(c - t₀) / h| ≤ κ := by
      have h1 : |(c - t₀) / h| ^ 2 = κ ^ 2 := by rw [sq_abs, hcx]
      have : |(c - t₀) / h| = κ := by
        have := abs_nonneg ((c - t₀) / h)
        nlinarith
      rw [this]
    have hbd : ∀ x ∈ Set.uIoc (6 : ℝ) σ₁, ‖f (x + c * I)‖ ≤
        (4 * C + 1) * T * Real.exp (-(Real.exp (κ ^ 2) / 4)) := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      simp only [hfdef]
      rw [norm_mul]
      have hL := hC' x c hx.1.le
      have hK1 := hKle x c hx.1.le hx.2 hcx'
      rw [hcx] at hK1
      have hn : ‖tauL (↑x + ↑c * I) - 1‖ ≤ (4 * C + 1) * T := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, abs_of_nonneg hc0] at *
        nlinarith
      exact mul_le_mul hn hK1 (norm_nonneg _) (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ₁ - 6)] at this
    refine this.trans ?_
    calc (4 * C + 1) * T * Real.exp (-(Real.exp (κ ^ 2) / 4)) * (σ₁ - 6)
        = (4 * C + 1) * β * T * Real.exp (-(Real.exp (κ ^ 2) / 4)) := by rw [hβdef]; ring
      _ ≤ _ := hsmall
  have hHa' := hside a (Or.inl rfl)
  have hHb' := hside b (Or.inr rfl)
  rw [← hHa] at hHa'
  rw [← hHb] at hHb'
  -- right side
  have hXb : ‖X‖ ≤ h * Real.exp (-3) / 2 := by
    have hbd : ∀ y ∈ Ioc a b, ‖f (σ₁ + y * I)‖ ≤
        Real.exp (-3) / (8 * π) * (4 * (1 + ((y - t₀) / h) ^ 2)⁻¹) := by
      intro y hy
      simp only [hfdef]
      rw [norm_mul]
      have hx : |(y - t₀) / h| ≤ κ := by
        rw [abs_div, abs_of_pos hhpos, div_le_iff₀ hhpos, abs_le]
        constructor <;> linarith [hy.1, hy.2]
      have hK1 := (hKle σ₁ y (by linarith) le_rfl hx).trans (exp_neg_exp_sq_le _)
      exact mul_le_mul (hρ y) hK1 (norm_nonneg _) (by positivity)
    have hgc : Continuous fun y : ℝ => Real.exp (-3) / (8 * π) * (4 * (1 + ((y - t₀) / h) ^ 2)⁻¹) := by
      refine continuous_const.mul (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y => ?_))
      positivity
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall fun y hy => hbd y hy) (hgc.intervalIntegrable (μ := volume) a b)
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hcomp := integral_inv_one_add_div_sq_le (t₀ := t₀) hhpos a b
    have hpi := Real.pi_pos
    calc Real.exp (-3) / (8 * π) * (4 * ∫ y in a..b, (1 + ((y - t₀) / h) ^ 2)⁻¹)
        ≤ Real.exp (-3) / (8 * π) * (4 * (h * π)) := by gcongr
      _ = h * Real.exp (-3) / 2 := by field_simp; ring
  have hYb : ‖Y‖ ≤ h * Real.exp (-3) := by
    have hn : ‖Y‖ = ‖I • Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [hn, hEq]
    have h1 := norm_add_le (Ha - Hb) (I • X)
    have h2 := norm_sub_le Ha Hb
    have h3 : ‖I • X‖ = ‖X‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h4 : Real.exp (-3) / 4 ≤ h * Real.exp (-3) / 4 := by
      have := Real.exp_pos (-3); nlinarith
    linarith
  -- the main term `∫ K ≥ 2h e^{−3}`
  set ψ : ℝ → ℝ := fun t => Real.exp (-Real.exp (((t - t₀) / h) ^ 2)) with hψ
  have hψc : Continuous ψ := by rw [hψ]; fun_prop
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => (Real.exp_pos _).le
  have hψ1 : ∀ t, ψ t ≤ 1 := fun t => psi_le_one t₀ h t
  have hmain : 2 * h * Real.exp (-3) ≤ ∫ t in a..b, ψ t := main_term hhpos hκ
  -- combine
  have hLc : Continuous fun t : ℝ => tauL (6 + t * I) :=
    tauLSeries_entire.continuous.comp (by fun_prop)
  have hYeq : (∫ t in a..b, tauL (6 + t * I) * (ψ t : ℂ)) = Y + ((∫ t in a..b, ψ t : ℝ) : ℂ) := by
    rw [hY, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hfdef]
      rw [hK6, Complex.ofReal_ofNat]
      ring
    · exact ((hfd.continuous.comp (by fun_prop : Continuous fun y : ℝ =>
        (((6 : ℝ) : ℂ) + y * I))).intervalIntegrable a b)
    · exact (Complex.continuous_ofReal.comp hψc).intervalIntegrable a b
  have hlow1 : h * Real.exp (-3) ≤ ‖∫ t in a..b, tauL (6 + t * I) * (ψ t : ℂ)‖ := by
    rw [hYeq]
    have h1 := norm_sub_norm_le (((∫ t in a..b, ψ t : ℝ) : ℂ)) (-Y)
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : 0 ≤ ∫ t in a..b, ψ t := by
      have := mul_pos (mul_pos two_pos hhpos) (Real.exp_pos (-3)); linarith
    rw [abs_of_nonneg h2, add_comm] at h1
    linarith
  refine hlow1.trans ?_
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun t _ => ?_) ((hLc.norm).intervalIntegrable a b)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 t)]
  exact mul_le_of_le_one_right (norm_nonneg _) (hψ1 t)

end RamanujanTau.HardyCountLinear
