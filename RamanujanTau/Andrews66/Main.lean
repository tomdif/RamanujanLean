/-
# Andrews 1966, the `k = 1` term with a power saving

`α(n) = [qⁿ] f(q)`, `f(q) = Σ q^{n²}/(−q;q)_n²`. We prove (`andrews_k1`, `andrews_k1_isBigO`)

  `α(n) = (−1)^{n+1} · (√24/√(24n−1)) · sinh(π√(24n−1)/12) + O(e^{π√(n/6) − √n/(500π)})`,

i.e. Andrews' (1966) formula truncated at its first term `k = 1`
(`π(24n−1)^{−1/4}·(−1)·A_2(n)·I_{1/2}(π√(24n−1)/12)`, `A_2(n) = (−1)ⁿ`, `I_{1/2}(x) = √(2/(πx)) sinh x`),
with an error smaller than the main term `≍ e^{π√(n/6)}/√n` by a fixed power `e^{−√n/(500π)}`.

Ingredients: Dragonette's decomposition (`Dragonette.decomp_D`, all errors explicit and exponentially smaller),
and the exact evaluation of the major-arc integral (`Andrews66.major_chord` + order-3/2 Bessel line).
-/
import RamanujanTau.Andrews66.MainArc

set_option autoImplicit false

namespace Andrews66
open Complex Filter Metric MeasureTheory Set intervalIntegral HardyRamanujan
open scoped Real Topology

noncomputable section

/-! ### the line `Re ζ = c` -/

lemma norm_hfun_line {Y c v : ℝ} (hc : 0 < c) :
    ‖hfun Y ((c : ℂ) + v * I)‖ = ‖(c : ℂ) + v * I‖ ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y * c / (c ^ 2 + v ^ 2)) := by
  set s : ℂ := (c : ℂ) + v * I with hs
  have hsre : s.re = c := by simp [hs]
  have hsim : s.im = v := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hn2 : Complex.normSq s = c ^ 2 + v ^ 2 := by rw [Complex.normSq_apply, hsre, hsim]; ring
  unfold hfun
  rw [norm_mul, norm_cpow_of_ne_zero hs0, norm_exp]
  simp only [neg_re, neg_im, div_ofNat_re, div_ofNat_im, re_ofNat, im_ofNat, zero_div, neg_zero, mul_zero,
    Real.exp_zero, div_one]
  congr 2
  rw [add_re, hsre, div_re, hn2]
  simp [hsre]

lemma norm_line_ge {c v : ℝ} : |v| ≤ ‖(c : ℂ) + v * I‖ := by
  have := Complex.abs_im_le_norm ((c : ℂ) + v * I); simpa using this

lemma norm_line_ge_c {c v : ℝ} (hc : 0 < c) : c ≤ ‖(c : ℂ) + v * I‖ := by
  have := Complex.abs_re_le_norm ((c : ℂ) + v * I); simp at this; rwa [abs_of_pos hc] at this

lemma exp_part_le {Y c v : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) : Y * c / (c ^ 2 + v ^ 2) ≤ Y / c := by
  rw [div_le_div_iff₀ (by positivity) hc]; nlinarith [sq_nonneg v, mul_nonneg hY (sq_nonneg v)]

lemma exp_part_le_tail {Y c v : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) (hv : c ≤ |v|) :
    Y * c / (c ^ 2 + v ^ 2) ≤ Y / (2 * c) := by
  have : c ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ hc.le hv 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [mul_nonneg hY hc.le]

lemma continuous_hfun_line {Y c : ℝ} (hc : 0 < c) : Continuous fun v : ℝ => hfun Y ((c : ℂ) + v * I) :=
  continuous_iff_continuousAt.mpr fun v =>
    (differentiableAt_hfun Y (by simpa using hc)).continuousAt.comp (by fun_prop : Continuous fun v : ℝ =>
      (c : ℂ) + v * I).continuousAt

lemma integrable_hfun_line {Y c : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) :
    Integrable fun v : ℝ => hfun Y ((c : ℂ) + v * I) := by
  set κ : ℝ := min c 1 with hκ
  have hκ0 : 0 < κ := lt_min hc one_pos
  have hbound : ∀ v : ℝ, ‖hfun Y ((c : ℂ) + v * I)‖ ≤
      (κ / 2) ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y / c) * (1 + ‖v‖) ^ (-(3 / 2 : ℝ)) := by
    intro v
    rw [norm_hfun_line hc]
    have hns : κ / 2 * (1 + ‖v‖) ≤ ‖(c : ℂ) + v * I‖ := by
      have h1 := norm_line_ge (c := c) (v := v)
      have h2 := norm_line_ge_c (v := v) hc
      have : κ ≤ c := min_le_left _ _
      have : κ ≤ 1 := min_le_right _ _
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg v]
    have hp : ‖(c : ℂ) + v * I‖ ^ (-(3 / 2 : ℝ)) ≤ (κ / 2 * (1 + ‖v‖)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hns (by norm_num)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hp
    have he : Real.exp (c + Y * c / (c ^ 2 + v ^ 2)) ≤ Real.exp (c + Y / c) :=
      Real.exp_le_exp.mpr (by linarith [exp_part_le (v := v) hY hc])
    calc ‖(c : ℂ) + v * I‖ ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y * c / (c ^ 2 + v ^ 2))
        ≤ ((κ / 2) ^ (-(3 / 2 : ℝ)) * (1 + ‖v‖) ^ (-(3 / 2 : ℝ))) * Real.exp (c + Y / c) := by gcongr
      _ = _ := by ring
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by simp; norm_num)).const_mul
    ((κ / 2) ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y / c))) (continuous_hfun_line hc).aestronglyMeasurable
    (Eventually.of_forall hbound)

/-- the tail bound on `[c, ∞)`. -/
lemma tail_Ioi {Y c : ℝ} (hc : 0 < c) (g : ℝ → ℂ)
    (hg : ∀ v : ℝ, c < v → ‖g v‖ ≤ v ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y / (2 * c))) :
    ‖∫ v in Ioi c, g v‖ ≤ 2 * Real.exp (c + Y / (2 * c)) / √c := by
  have hI := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) hc
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi c)) (hI.mul_const (Real.exp (c + Y / (2 * c))))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => hg v hv))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_mul_const, integral_Ioi_rpow_of_lt (by norm_num) hc]
  rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow]
  field_simp

lemma tail_pointwise {Y c v : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) (hv : c ≤ |v|) :
    ‖hfun Y ((c : ℂ) + v * I)‖ ≤ |v| ^ (-(3 / 2 : ℝ)) * Real.exp (c + Y / (2 * c)) := by
  rw [norm_hfun_line hc]
  have h1 : ‖(c : ℂ) + v * I‖ ^ (-(3 / 2 : ℝ)) ≤ |v| ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) norm_line_ge (by norm_num)
  have h2 : Real.exp (c + Y * c / (c ^ 2 + v ^ 2)) ≤ Real.exp (c + Y / (2 * c)) :=
    Real.exp_le_exp.mpr (by linarith [exp_part_le_tail hY hc hv])
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- **the tails of the line**: `‖∫_ℝ h − ∫_{−c}^{c} h‖ ≤ 4 e^{c + Y/(2c)}/√c`. -/
theorem tail_bound {Y c : ℝ} (hY : 0 ≤ Y) (hc : 0 < c) :
    ‖(∫ v : ℝ, hfun Y ((c : ℂ) + v * I)) - ∫ v in (-c)..c, hfun Y ((c : ℂ) + v * I)‖ ≤
      4 * Real.exp (c + Y / (2 * c)) / √c := by
  set g := fun v : ℝ => hfun Y ((c : ℂ) + v * I)
  have hint := integrable_hfun_line hY hc
  have e1 := intervalIntegral.integral_Iic_add_Ioi (f := g) (b := -c) hint.integrableOn hint.integrableOn
  have e2 := intervalIntegral.integral_interval_add_Ioi (f := g) (a := -c) (b := c) hint.integrableOn
    hint.integrableOn
  have e3 := integral_comp_neg_Ioi c g
  have hdiff : (∫ v : ℝ, g v) - ∫ v in (-c)..c, g v = (∫ v in Ioi c, g (-v)) + ∫ v in Ioi c, g v := by
    rw [e3, ← e1, ← e2]; ring
  change ‖(∫ v : ℝ, g v) - ∫ v in (-c)..c, g v‖ ≤ _
  rw [hdiff]
  have b1 := tail_Ioi hc (fun v => g (-v)) fun v hv => by
    have := tail_pointwise (v := -v) hY hc (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    rwa [abs_neg, abs_of_pos (by linarith)] at this
  have b2 := tail_Ioi hc g fun v hv => by
    have := tail_pointwise (v := v) hY hc (by rw [abs_of_pos (by linarith)]; linarith)
    rwa [abs_of_pos (by linarith)] at this
  calc _ ≤ ‖∫ v in Ioi c, g (-v)‖ + ‖∫ v in Ioi c, g v‖ := norm_add_le _ _
    _ ≤ _ := by
        simp only at b1
        have : 4 * Real.exp (c + Y / (2 * c)) / √c =
          2 * Real.exp (c + Y / (2 * c)) / √c + 2 * Real.exp (c + Y / (2 * c)) / √c := by ring
        linarith

/-! ### the exact main term -/

/-- **Andrews' `k = 1` term** (up to the sign `(−1)^{n+1}`):
`√24/√(24n−1) · sinh(π√(24n−1)/12) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/12)`. -/
def M1 (n : ℕ) : ℝ := √24 / √(24 * (n : ℝ) - 1) * Real.sinh (π * √(24 * (n : ℝ) - 1) / 12)

lemma sqrt_YY {n : ℕ} (hn : 1 ≤ n) : √(YY n) = π * √(24 * (n : ℝ) - 1) / 24 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ 24 * (n : ℝ) - 1 := by linarith
  rw [show YY n = (π * √(24 * (n : ℝ) - 1) / 24) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt h0]; unfold YY aa; ring]
  exact Real.sqrt_sq (by positivity)

lemma YY_pos {n : ℕ} (hn : 1 ≤ n) : 0 < YY n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold YY; have := aa_pos; have : (0 : ℝ) < n - 1 / 24 := by linarith
  positivity

lemma main_const {n : ℕ} (hn : 1 ≤ n) :
    √(π * aa) * (2 * Real.sinh (2 * √(YY n)) / (√π * (2 * √(YY n)))) = M1 n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 < 24 * (n : ℝ) - 1 := by linarith
  have hs : 0 < √(24 * (n : ℝ) - 1) := Real.sqrt_pos.mpr h0
  rw [sqrt_YY hn, Real.sqrt_mul Real.pi_pos.le, show √aa = π / √24 by
    rw [show aa = (π / √24) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; rfl]
    exact Real.sqrt_sq (by positivity)]
  unfold M1
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h24 : (0 : ℝ) < √24 := by positivity
  have h24s : √(24 : ℝ) ^ 2 = 24 := Real.sq_sqrt (by norm_num)
  rw [show 2 * (π * √(24 * (n : ℝ) - 1) / 24) = π * √(24 * (n : ℝ) - 1) / 12 by ring]
  field_simp
  rw [h24s]; ring

/-- **exact evaluation of the major arc**: `‖∫_{−t}^{t} M − 2π M₁(n)‖ ≤ √(πa)·4e^{3A/2}/√(A/2)`. -/
theorem major_eval {n : ℕ} (hn : 1 ≤ n) :
    ‖(∫ θ in (-Dragonette.tD n)..Dragonette.tD n, Dragonette.MD n (Dragonette.tD n) θ) - 2 * π * M1 n‖ ≤
      √(π * aa) * (4 * Real.exp (3 / 2 * Dragonette.AD n) / √(Dragonette.AD n / 2)) := by
  set t := Dragonette.tD n with htdef
  set A := Dragonette.AD n with hAdef
  have ht := Dragonette.tD_pos hn
  have hA := Dragonette.AD_pos hn
  have ha := aa_pos
  have hY := YY_pos hn
  have hc : aa / (2 * t) = A / 2 := by
    have := Dragonette.AD_eq hn; rw [← htdef, ← hAdef] at this
    rw [← this]; unfold aa; field_simp
  have hc0 : 0 < aa / (2 * t) := by positivity
  have hB := bessel_line hY.le hc0
  rw [← Complex.ofReal_tsum, tsum_bco hY] at hB
  have hT := tail_bound hY.le hc0
  have hch := major_chord n ht
  rw [hch]
  have e : ((√(π * aa) : ℝ) : ℂ) * (∫ v in (-(aa / (2 * t)))..(aa / (2 * t)),
        hfun (YY n) (((aa / (2 * t) : ℝ) : ℂ) + v * I)) - 2 * π * M1 n =
      -(((√(π * aa) : ℝ) : ℂ) * ((∫ v : ℝ, hfun (YY n) (((aa / (2 * t) : ℝ) : ℂ) + v * I)) -
        ∫ v in (-(aa / (2 * t)))..(aa / (2 * t)), hfun (YY n) (((aa / (2 * t) : ℝ) : ℂ) + v * I))) := by
    have hB' : (∫ v : ℝ, hfun (YY n) (((aa / (2 * t) : ℝ) : ℂ) + v * I)) =
        2 * π * ((2 * Real.sinh (2 * √(YY n)) / (√π * (2 * √(YY n))) : ℝ) : ℂ) := hB
    rw [hB', ← main_const hn]; push_cast; ring
  rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  refine hT.trans ?_
  rw [hc]
  gcongr
  -- `A/2 + Y/A ≤ 3A/2`
  have : YY n / (2 * (A / 2)) ≤ A := by
    rw [div_le_iff₀ (by positivity)]
    have hAt : A = n * t := rfl
    have hat : aa = A * t := by
      have := Dragonette.AD_eq hn; rw [← htdef, ← hAdef] at this
      rw [← this]; unfold aa; field_simp; rw [div_self ht.ne']
    unfold YY
    rw [hat, hAt]
    have : 0 ≤ (n : ℝ) * t := by positivity
    nlinarith [mul_pos ht ht]
  linarith

/-! ### assembly with Dragonette's decomposition -/

open Dragonette in
/-- **the explicit bound** (for all `n` with `t_n ≤ 1/32` and the cusp-error condition `hη`, i.e. all large `n`):
`|α(n) − (−1)^{n+1} M₁(n)| ≤ Err(1/t)/K_n + √(πa)·4e^{3A/2}/(2π√(A/2))`, where
`Err/K_n = Err(1/t)e^{π√(n/6)}/(2√n)` is exponentially smaller than the main term. -/
theorem andrews_k1_bound {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) :
    |(α n : ℝ) - (-1) ^ (n + 1) * M1 n| ≤
      Err (1 / tD n) / KD n + √(π * aa) * (4 * Real.exp (3 / 2 * AD n) / √(AD n / 2)) / (2 * π) := by
  have hD := decomp_D hn ht32 hη
  have hmain := major_main_D hn
  have hP := PD_eq hn
  set X := ∫ θ in (-tD n)..tD n, MD n (tD n) θ with hX
  set T := √(π * aa) * (4 * Real.exp (3 / 2 * AD n) / √(AD n / 2))
  have hT : ‖X - 2 * π * M1 n‖ ≤ T := major_eval hn
  set J := ∫ v in (-√(AD n))..√(AD n), hneg (v / √(AD n)) (tD n) v
  have hJ : ((1 / √π : ℝ) : ℂ) * J = ((KD n / (2 * π) : ℝ) : ℂ) * X := by
    rw [hmain, ← mul_assoc, ← Complex.ofReal_mul, hP]
  rw [hJ] at hD
  set s : ℝ := (-1) ^ (n + 1) * (α n : ℝ)
  have hK : 0 < KD n := by unfold KD; have := Real.sqrt_pos.mpr (show (0 : ℝ) < n by exact_mod_cast hn); positivity
  have hπ : 0 < 2 * π := by positivity
  have hdec : (((KD n * (s - M1 n)) : ℝ) : ℂ) = (((KD n * s : ℝ) : ℂ) - ((KD n / (2 * π) : ℝ) : ℂ) * X) +
      ((KD n / (2 * π) : ℝ) : ℂ) * (X - 2 * π * M1 n) := by
    push_cast; field_simp; ring
  have hb : KD n * |s - M1 n| ≤ Err (1 / tD n) + KD n / (2 * π) * T := by
    have h := congrArg norm hdec
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hK] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    gcongr
  have hs : (α n : ℝ) - (-1) ^ (n + 1) * M1 n = (-1) ^ (n + 1) * (s - M1 n) := by
    have h2 : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    simp only [s]; linear_combination (-(α n : ℝ)) * h2
  rw [hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [div_add_div _ _ hK.ne' hπ.ne', le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hb hπ.le
  have e : (Err (1 / tD n) + KD n / (2 * π) * T) * (2 * π) = Err (1 / tD n) * (2 * π) + KD n * T := by
    field_simp
  rw [e] at this
  linarith

/-! ### the power saving -/

/-- the constant in `Err(u) ≤ K u² e^{−u/2400}`. -/
def KE : ℝ := 8 + 62 * (4 * C0 + 4) * π + 8 * π + 12 * π

lemma KE_pos : 0 < KE := by unfold KE; have := C0_nonneg; positivity

lemma Err_le {u : ℝ} (hu : 1 ≤ u) : Dragonette.Err u ≤ KE * u ^ 2 * Real.exp (-(u / 2400)) := by
  unfold Dragonette.Err KE
  set E := Real.exp (-(u / 2400))
  have hE : 0 < E := Real.exp_pos _
  have h9 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(π ^ 2 * u / 2)) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right h9 (by linarith : (0 : ℝ) ≤ u)])
  have h3 : Real.exp (-(u / 160)) ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hC : 0 ≤ 4 * C0 + 4 := by linarith [C0_nonneg]
  have hπ := Real.pi_pos
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hE2 := (Real.exp_pos (-(π ^ 2 * u / 2))).le
  have hE3 := (Real.exp_pos (-(u / 160))).le
  have a1 : 31 * (4 * C0 + 4) * (π * u) * Real.exp (-(π ^ 2 * u / 2)) ≤ 31 * (4 * C0 + 4) * π * (u ^ 2 * E) := by
    have : u * Real.exp (-(π ^ 2 * u / 2)) ≤ u ^ 2 * E := mul_le_mul hu2 h2 hE2 (by positivity)
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 31 * (4 * C0 + 4) * π by positivity)
    nlinarith
  have a2 : 2 * Real.exp (-(u / 160)) * (1 + 2 * u) ≤ 6 * u * E := by
    have : (1 + 2 * u) ≤ 3 * u := by linarith
    nlinarith [mul_le_mul h3 this (by linarith) hE.le]
  have a3 : u * E ≤ u ^ 2 * E := mul_le_mul_of_nonneg_right hu2 hE.le
  have a4 : 2 * π * u * (2 * Real.exp (-(u / 160)) * (1 + 2 * u)) ≤ 12 * π * (u ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_left a2 (show 0 ≤ 2 * π * u by positivity)
    nlinarith
  nlinarith

lemma tD_inv_eq {n : ℕ} (hn : 1 ≤ n) : 1 / Dragonette.tD n = √(24 * (n : ℝ)) / π := by
  unfold Dragonette.tD; field_simp

lemma AD_eq_u {n : ℕ} (hn : 1 ≤ n) : Dragonette.AD n = π ^ 2 / 24 * (1 / Dragonette.tD n) := by
  rw [← Dragonette.AD_eq hn]; have := Dragonette.tD_pos hn; field_simp

/-- **Andrews 1966 with the first term and a power saving**:
`α(n) = (−1)^{n+1} √24/√(24n−1) · sinh(π√(24n−1)/12) + O(e^{π√(n/6) − √(24n)/(2450π)})`.
The saving `√(24n)/(2450π) = (12/(2450π²))·π√(n/6) ≈ π√(n/6)/2015` is a fixed power of the main term. -/
theorem andrews_k1_isBigO :
    (fun n : ℕ => (Dragonette.α n : ℝ) - (-1) ^ (n + 1) * M1 n) =O[atTop]
      (fun n : ℕ => Real.exp (π * √((n : ℝ) / 6) - √(24 * (n : ℝ)) / (2450 * π))) := by
  -- `u = 1/t → ∞`
  have hu : Tendsto (fun n : ℕ => 1 / Dragonette.tD n) atTop atTop := by
    have h : Tendsto (fun n : ℕ => √(24 * (n : ℝ)) / π) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))).atTop_div_const
        Real.pi_pos
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (tD_inv_eq hn).symm
  have hd : (0 : ℝ) < 1 / 2400 - 1 / 2450 := by norm_num
  have hpe := (Dragonette.tendsto_pow_exp hd 2).comp hu
  have hev1 := hpe.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev2 := hu.eventually (eventually_ge_atTop 48)
  refine Asymptotics.IsBigO.of_bound (KE + √(π * aa) * 4 / (2 * π)) ?_
  filter_upwards [Dragonette.eventually_small, hev1, hev2] with n hsm h1 h2
  obtain ⟨hn, ht32, hη⟩ := hsm
  simp only [Function.comp] at h1
  set u := 1 / Dragonette.tD n with hudef
  set A := Dragonette.AD n with hAdef
  have hAu : A = π ^ 2 / 24 * u := AD_eq_u hn
  have hsq : √(24 * (n : ℝ)) / (2450 * π) = u / 2450 := by rw [hudef, tD_inv_eq hn]; field_simp
  have h2A : π * √((n : ℝ) / 6) = 2 * A := (Dragonette.two_AD hn).symm
  rw [h2A, hsq, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hb := andrews_k1_bound hn ht32 hη
  rw [← hudef, ← hAdef] at hb
  set g := Real.exp (2 * A - u / 2450)
  have hg : 0 < g := Real.exp_pos _
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  -- term 1
  have hKD : Dragonette.KD n = 2 * √(n : ℝ) / Real.exp (2 * A) := rfl
  have hsn : 1 ≤ √(n : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hErr := Err_le (u := u) (by linarith)
  have t1 : Dragonette.Err u / Dragonette.KD n ≤ KE * g := by
    rw [hKD, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : u ^ 2 * Real.exp (-(u / 2400)) = (u ^ 2 * Real.exp (-((1 / 2400 - 1 / 2450) * u))) *
        Real.exp (-(u / 2450)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hgg : g = Real.exp (2 * A) * Real.exp (-(u / 2450)) := by
      simp only [g]; rw [← Real.exp_add]; ring_nf
    calc Dragonette.Err u * Real.exp (2 * A) ≤ KE * u ^ 2 * Real.exp (-(u / 2400)) * Real.exp (2 * A) := by
          gcongr
      _ = KE * (u ^ 2 * Real.exp (-((1 / 2400 - 1 / 2450) * u))) * (Real.exp (2 * A) * Real.exp (-(u / 2450))) := by
          rw [mul_assoc KE, e]; ring
      _ ≤ KE * 1 * g := by rw [← hgg]; gcongr; exact KE_pos.le
      _ ≤ KE * g * (2 * √(n : ℝ)) := by
          have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 2 * √(n : ℝ)) (mul_pos KE_pos hg).le
          linarith
  -- term 2
  have hA2 : 1 ≤ √(A / 2) := by
    rw [show (1 : ℝ) = √1 by simp]; refine Real.sqrt_le_sqrt ?_; rw [hAu]; nlinarith
  have t2 : √(π * aa) * (4 * Real.exp (3 / 2 * A) / √(A / 2)) / (2 * π) ≤ √(π * aa) * 4 / (2 * π) * g := by
    have h9 : 9 ≤ π ^ 2 := by nlinarith
    have he : Real.exp (3 / 2 * A) ≤ g := Real.exp_le_exp.mpr (by
      rw [hAu]; nlinarith [mul_le_mul_of_nonneg_right h9 (by linarith : (0 : ℝ) ≤ u)])
    have : 4 * Real.exp (3 / 2 * A) / √(A / 2) ≤ 4 * g := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [Real.exp_pos (3 / 2 * A)]
    have hs0 : 0 ≤ √(π * aa) := Real.sqrt_nonneg _
    calc √(π * aa) * (4 * Real.exp (3 / 2 * A) / √(A / 2)) / (2 * π) ≤ √(π * aa) * (4 * g) / (2 * π) := by
          gcongr
      _ = _ := by ring
  linarith

end

end Andrews66
