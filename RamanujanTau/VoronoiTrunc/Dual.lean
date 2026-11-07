/-
# The exact dual expansion of the Riesz means of `τ` with Schläfli kernels

For `r ≥ 5` and every real `x`,

    W_r(x) = Σ_{n≤x} τ(n)(x−n)^r = (r!/(2π)^r) Σ_n τ(n) k_r(n, x),
    k_j(n, x) = (1/2π) ∫_ℝ z^{−(13+j)} exp(2π(xz − n/z)) dt,   z = 1 + it   (`dual_W`).

Proof: inverse Laplace (`laplace_inv`) termwise, Fubini, the modular relation `Dq_modular`,
Fubini again.  Then `kB_eq`: `k_j(n,x) = (x/n)^{(12+j)/2} I_{12+j}(2π√(nx))` (scaling `z = √(n/x) v`
and the contour identification `lineInt_eq_Ik`).
-/
import RamanujanTau.VoronoiTrunc.Laplace
import RamanujanTau.VoronoiTrunc.Modular
import RamanujanTau.VoronoiTrunc.Contour
import RamanujanTau.HeckeConvex.Summable
import RamanujanTau.TauPartialSumsSharp.Core

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

/-! ### Bounds for `τ` -/

lemma norm_tauC (n : ℕ) : ‖tauC n‖ = |((tau n : ℤ) : ℝ)| := by
  unfold tauC
  rw [show ((τ n : ℤ) : ℂ) = (((τ n : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]

/-- `|τ(n)| ≤ A n⁷`. -/
lemma exists_tau_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ‖tauC n‖ ≤ A * (n : ℝ) ^ 7 := by
  obtain ⟨A, hA0, hA⟩ := RamanujanTau.HeckeConvex.exists_sum_abs_tau_le
  refine ⟨A, hA0, fun n => ?_⟩
  rw [norm_tauC]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tau_zero]
  · have h1 : |((tau n : ℤ) : ℝ)| ≤ ∑ m ∈ Finset.Icc 1 n, |((tau m : ℤ) : ℝ)| :=
      Finset.single_le_sum (f := fun m => |((tau m : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
    have h2 : (n : ℝ) ^ (13 / 2 : ℝ) ≤ (n : ℝ) ^ 7 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
    calc |((tau n : ℤ) : ℝ)| ≤ A * (n : ℝ) ^ (13 / 2 : ℝ) := h1.trans (hA n)
      _ ≤ A * (n : ℝ) ^ 7 := by gcongr

/-- `n⁷ e^{−na} ≤ 7! (2/a)⁷ e^{−na/2}`. -/
lemma pow_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (n : ℝ) ^ 7 * Real.exp (-(n * a)) ≤ (Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * (Real.exp (-(a / 2))) ^ n := by
  have h := Real.pow_div_factorial_le_exp (x := n * a / 2) (by positivity) 7
  have hf : (0 : ℝ) < Nat.factorial 7 := by positivity
  rw [div_le_iff₀ hf] at h
  have e1 : (n : ℝ) ^ 7 = (2 / a) ^ 7 * (n * a / 2) ^ 7 := by field_simp
  have e2 : (Real.exp (-(a / 2))) ^ n = Real.exp (-(n * a)) * Real.exp (n * a / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have : 0 ≤ (2 / a) ^ 7 * Real.exp (-(n * a)) := by positivity
  nlinarith [Real.exp_pos (-(n * a))]

/-- `Σ_n |τ(n)| e^{−na} ≤ K a^{−8}` for `0 < a ≤ 2π`, with `K = A·7!·2⁸(1+π)`. -/
lemma tau_exp_sum {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ n : ℕ, ‖tauC n‖ ≤ A * (n : ℝ) ^ 7)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ 2 * π) :
    Summable (fun n : ℕ => ‖tauC n‖ * Real.exp (-(n * a))) ∧
      ∑' n : ℕ, ‖tauC n‖ * Real.exp (-(n * a)) ≤
        A * (Nat.factorial 7 : ℝ) * 2 ^ 8 * (1 + π) * (a ^ 8)⁻¹ := by
  set q := Real.exp (-(a / 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg : Summable fun n : ℕ => A * ((Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * q ^ n) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left A
  have hb : ∀ n : ℕ, ‖tauC n‖ * Real.exp (-(n * a)) ≤ A * ((Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * q ^ n) := by
    intro n
    calc ‖tauC n‖ * Real.exp (-(n * a)) ≤ A * (n : ℝ) ^ 7 * Real.exp (-(n * a)) := by
          gcongr; exact hA n
      _ = A * ((n : ℝ) ^ 7 * Real.exp (-(n * a))) := by ring
      _ ≤ A * ((Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * q ^ n) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_le ha n) hA0
  have hs : Summable (fun n : ℕ => ‖tauC n‖ * Real.exp (-(n * a))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hb hg
  refine ⟨hs, (hs.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  -- 1/(1-q) ≤ (1+π)·2/a
  have h1 : a / 2 / (1 + a / 2) ≤ 1 - q := by
    have := Real.add_one_le_exp (a / 2)
    rw [hq, Real.exp_neg, div_le_iff₀ (by positivity)]
    have hpos := Real.exp_pos (a / 2)
    field_simp
    nlinarith
  have h2 : (1 - q)⁻¹ ≤ (1 + π) * (2 / a) := by
    have hpos : 0 < a / 2 / (1 + a / 2) := by positivity
    calc (1 - q)⁻¹ ≤ (a / 2 / (1 + a / 2))⁻¹ := inv_anti₀ hpos h1
      _ = (1 + a / 2) * (2 / a) := by field_simp
      _ ≤ (1 + π) * (2 / a) := by gcongr; linarith
  calc A * ((Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * (1 - q)⁻¹)
      ≤ A * ((Nat.factorial 7 : ℝ) * (2 / a) ^ 7 * ((1 + π) * (2 / a))) := by gcongr
    _ = A * (Nat.factorial 7 : ℝ) * 2 ^ 8 * (1 + π) * (a ^ 8)⁻¹ := by field_simp


/-! ### The line `z = 1 + it` -/

/-- `z(t) = 1 + it`. -/
noncomputable def zl (t : ℝ) : ℂ := 1 + t * I

lemma zl_re (t : ℝ) : (zl t).re = 1 := by simp [zl]
lemma zl_im (t : ℝ) : (zl t).im = t := by simp [zl]

lemma sq_norm_zl (t : ℝ) : ‖zl t‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, zl_re, zl_im]; ring

lemma one_le_norm_zl (t : ℝ) : 1 ≤ ‖zl t‖ := by
  have : (1 : ℝ) ^ 2 ≤ ‖zl t‖ ^ 2 := by rw [sq_norm_zl]; nlinarith [sq_nonneg t]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) (by norm_num)).1 this

lemma zl_ne_zero (t : ℝ) : zl t ≠ 0 := by
  intro h; have := congrArg Complex.re h; rw [zl_re] at this; simp at this

lemma continuous_zl : Continuous zl := by unfold zl; fun_prop

lemma re_inv_zl (t : ℝ) : ((zl t)⁻¹).re = 1 / (1 + t ^ 2) := by
  rw [inv_re, zl_re, ← Complex.sq_norm, sq_norm_zl]

lemma inv_norm_zl_pow_le {m : ℕ} (hm : 2 ≤ m) (t : ℝ) : (‖zl t‖ ^ m)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  rw [← sq_norm_zl]
  exact pow_le_pow_right₀ (one_le_norm_zl t) hm

/-- **The Schläfli kernel** `k_j(n,x) = (1/2π) ∫ z^{−(13+j)} e^{2π(xz − n/z)} dt`, `z = 1+it`. -/
noncomputable def kB (j n : ℕ) (x : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, ((zl t) ^ (13 + j))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹))

lemma norm_kB_integrand (j n : ℕ) (x t : ℝ) :
    ‖((zl t) ^ (13 + j))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹))‖ =
      (‖zl t‖ ^ (13 + j))⁻¹ * (Real.exp (2 * π * x) * Real.exp (-(n * (2 * π / (1 + t ^ 2))))) := by
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_exp, ← Real.exp_add]
  congr 2
  have : (2 * π * ((x : ℂ) * zl t - (n : ℂ) * (zl t)⁻¹)).re = 2 * π * (x - n * (1 / (1 + t ^ 2))) := by
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, zl_re, zl_im, natCast_re, natCast_im,
      re_inv_zl, zero_mul, sub_zero, mul_one]
    simp
  rw [this]; field_simp; ring

lemma continuous_kB_integrand (j n : ℕ) (x : ℝ) :
    Continuous fun t : ℝ => ((zl t) ^ (13 + j))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹)) := by
  have hz := continuous_zl
  refine ((hz.pow _).inv₀ fun t => pow_ne_zero _ (zl_ne_zero t)).mul ?_
  exact Complex.continuous_exp.comp (continuous_const.mul ((continuous_const.mul hz).sub
    (continuous_const.mul (hz.inv₀ zl_ne_zero))))

lemma norm_kB_integrand_le (j n : ℕ) (x t : ℝ) :
    ‖((zl t) ^ (13 + j))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹))‖ ≤
      Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹ := by
  rw [norm_kB_integrand]
  have h1 := inv_norm_zl_pow_le (m := 13 + j) (by omega) t
  have h2 : Real.exp (-(n * (2 * π / (1 + t ^ 2)))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have : 0 ≤ (n : ℝ) * (2 * π / (1 + t ^ 2)) := by positivity
                              linarith)
  have h0 : 0 ≤ (‖zl t‖ ^ (13 + j))⁻¹ := by positivity
  calc (‖zl t‖ ^ (13 + j))⁻¹ * (Real.exp (2 * π * x) * Real.exp (-(n * (2 * π / (1 + t ^ 2)))))
      ≤ (1 + t ^ 2)⁻¹ * (Real.exp (2 * π * x) * 1) := by gcongr
    _ = _ := by ring

lemma integrable_kB_integrand (j n : ℕ) (x : ℝ) :
    Integrable fun t : ℝ => ((zl t) ^ (13 + j))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹)) :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul _)
    (continuous_kB_integrand j n x).aestronglyMeasurable
    (Eventually.of_forall (norm_kB_integrand_le j n x))

/-! ### The dual expansion -/

lemma WC_eq_tsum {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    TauPartialSumsSharp.WC tauC r x = ∑' n : ℕ, tauC n * (((max (x - n) 0) ^ r : ℝ) : ℂ) := by
  unfold TauPartialSumsSharp.WC
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hx : 0 ≤ x := by
      by_contra h; rw [Nat.floor_of_nonpos (not_le.1 h).le] at h2; omega
    have : (n : ℝ) ≤ x := (Nat.cast_le.2 h2).trans (Nat.floor_le hx)
    rw [max_eq_left (by linarith)]; push_cast; rfl
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [tauC, tau_zero]
    · have : ⌊x⌋₊ < n := by
        by_contra h; exact hn (Finset.mem_Icc.2 ⟨hpos, not_lt.1 h⟩)
      have hxn : x < n := by
        rcases le_or_gt 0 x with hx | hx
        · exact (Nat.floor_lt hx).1 this
        · linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [max_eq_right (by linarith), zero_pow (by omega)]; simp


/-- Step 1: each Riesz term is an inverse Laplace transform. -/
lemma riesz_term {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) :
    ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) : ℂ) * (((max (x - n) 0) ^ r : ℝ) : ℂ) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, cexp (((2 * π * (x - n) : ℝ) : ℂ) * zl t) * ((zl t) ^ (r + 1))⁻¹ := by
  have h := laplace_inv hr (2 * π * (x - n))
  simp only [zl]
  rw [h]
  have hm : max (2 * π * (x - n)) 0 = 2 * π * max (x - n) 0 := by
    rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
  rw [hm, mul_pow]
  push_cast
  have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  field_simp
  rw [mul_pow, mul_pow]

/-- The integrand of the first interchange. -/
noncomputable def F1 (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  tauC n * (cexp (((2 * π * (x - n) : ℝ) : ℂ) * zl t) * ((zl t) ^ (r + 1))⁻¹)

/-- The integrand of the second interchange. -/
noncomputable def G1 (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  tauC n * (((zl t) ^ (13 + r))⁻¹ * cexp (2 * π * (x * zl t - n * (zl t)⁻¹)))

lemma norm_F1_le {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖F1 r x n t‖ ≤ ‖tauC n‖ * Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹ := by
  unfold F1
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_inv, norm_pow]
  have hre : (((2 * π * (x - n) : ℝ) : ℂ) * zl t).re = 2 * π * (x - n) := by
    simp [mul_re, zl_re, zl_im]
  rw [hre]
  have h1 := inv_norm_zl_pow_le (m := r + 1) (by omega) t
  have e : Real.exp (2 * π * (x - n)) = Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have : 0 ≤ ‖tauC n‖ * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x)) := by positivity
  calc ‖tauC n‖ * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (‖zl t‖ ^ (r + 1))⁻¹)
      ≤ ‖tauC n‖ * (Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

lemma continuous_F1 (r : ℕ) (x : ℝ) (n : ℕ) : Continuous (F1 r x n) := by
  unfold F1
  have hz := continuous_zl
  exact continuous_const.mul ((Complex.continuous_exp.comp (continuous_const.mul hz)).mul
    ((hz.pow _).inv₀ fun t => pow_ne_zero _ (zl_ne_zero t)))

lemma integrable_F1 {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (n : ℕ) : Integrable (F1 r x n) :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul _) (continuous_F1 r x n).aestronglyMeasurable
    (Eventually.of_forall (norm_F1_le hr x n))

lemma summable_F1 {r : ℕ} (hr : 1 ≤ r) (x : ℝ) : Summable fun n => ∫ t, ‖F1 r x n t‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_tau_le
  obtain ⟨hs, -⟩ := tau_exp_sum hA0 hA (a := 2 * π) (by positivity) le_rfl
  have hb : ∀ n : ℕ, ∫ t, ‖F1 r x n t‖ ≤ (‖tauC n‖ * Real.exp (-(n * (2 * π)))) * (Real.exp (2 * π * x) * π) := by
    intro n
    calc ∫ t, ‖F1 r x n t‖ ≤ ∫ t, ‖tauC n‖ * Real.exp (-(n * (2 * π))) * Real.exp (2 * π * x) * (1 + t ^ 2)⁻¹ :=
          integral_mono (integrable_F1 hr x n).norm (integrable_inv_one_add_sq.const_mul _)
            (norm_F1_le hr x n)
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hb (hs.mul_right _)

lemma tsum_F1 (r : ℕ) (x t : ℝ) :
    ∑' n, F1 r x n t = cexp (2 * π * x * zl t) * ((zl t) ^ (r + 1))⁻¹ * Dq (zl t) := by
  unfold Dq F1
  rw [← tsum_mul_left]
  congr 1; funext n
  have : cexp (((2 * π * (x - n) : ℝ) : ℂ) * zl t) = cexp (2 * π * x * zl t) * cexp (-2 * π * n * zl t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

lemma modular_step (r : ℕ) (x t : ℝ) :
    cexp (2 * π * x * zl t) * ((zl t) ^ (r + 1))⁻¹ * Dq (zl t) = ∑' n, G1 r x n t := by
  have hre : 0 < (zl t).re := by rw [zl_re]; norm_num
  rw [Dq_modular hre]
  unfold Dq G1
  rw [← mul_assoc, ← tsum_mul_left]
  congr 1; funext n
  have hz := zl_ne_zero t
  have e : cexp (2 * π * x * zl t) * cexp (-2 * π * n * (zl t)⁻¹) =
      cexp (2 * π * (x * zl t - n * (zl t)⁻¹)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← e]
  field_simp
  ring

lemma norm_G1 (r : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖G1 r x n t‖ = (‖zl t‖ ^ (13 + r))⁻¹ * Real.exp (2 * π * x) *
      (‖tauC n‖ * Real.exp (-(n * (2 * π / (1 + t ^ 2))))) := by
  unfold G1; rw [norm_mul, norm_kB_integrand]; ring

lemma integrable_G1 (r : ℕ) (x : ℝ) (n : ℕ) : Integrable (G1 r x n) := by
  unfold G1; exact (integrable_kB_integrand r n x).const_mul _

lemma summable_G1 {r : ℕ} (hr : 5 ≤ r) (x : ℝ) : Summable fun n => ∫ t, ‖G1 r x n t‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_tau_le
  set K := A * (Nat.factorial 7 : ℝ) * 2 ^ 8 * (1 + π) with hK
  have hK0 : 0 ≤ K := by positivity
  -- pointwise bound on the full sum over n
  have hpt : ∀ t : ℝ, Summable (fun n : ℕ => ‖G1 r x n t‖) ∧
      ∑' n, ‖G1 r x n t‖ ≤ Real.exp (2 * π * x) * K * ((2 * π) ^ 8)⁻¹ * (1 + t ^ 2)⁻¹ := by
    intro t
    have ha : 0 < 2 * π / (1 + t ^ 2) := by positivity
    have ha' : 2 * π / (1 + t ^ 2) ≤ 2 * π := div_le_self (by positivity) (by nlinarith [sq_nonneg t])
    obtain ⟨hs, hle⟩ := tau_exp_sum hA0 hA ha ha'
    simp_rw [norm_G1]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    have hz : (‖zl t‖ ^ (13 + r))⁻¹ ≤ ((1 + t ^ 2) ^ 9)⁻¹ := by
      apply inv_anti₀ (by positivity)
      rw [← sq_norm_zl, ← pow_mul]
      exact pow_le_pow_right₀ (one_le_norm_zl t) (by omega)
    have ha8 : ((2 * π / (1 + t ^ 2)) ^ 8)⁻¹ = (1 + t ^ 2) ^ 8 * ((2 * π) ^ 8)⁻¹ := by
      rw [div_pow, inv_div]; field_simp
    calc (‖zl t‖ ^ (13 + r))⁻¹ * Real.exp (2 * π * x) *
          ∑' n, ‖tauC n‖ * Real.exp (-(n * (2 * π / (1 + t ^ 2))))
        ≤ ((1 + t ^ 2) ^ 9)⁻¹ * Real.exp (2 * π * x) *
          (K * ((2 * π / (1 + t ^ 2)) ^ 8)⁻¹) := by gcongr
      _ = Real.exp (2 * π * x) * K * ((2 * π) ^ 8)⁻¹ * (1 + t ^ 2)⁻¹ := by
          rw [ha8]; field_simp
  set C := Real.exp (2 * π * x) * K * ((2 * π) ^ 8)⁻¹
  have hC : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ t, ‖G1 r x n t‖ ≤ C * π := by
    intro N
    rw [← integral_finsetSum _ (fun n _ => (integrable_G1 r x n).norm)]
    calc ∫ t, ∑ n ∈ Finset.range N, ‖G1 r x n t‖ ≤ ∫ t, C * (1 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_finsetSum _ (fun n _ => (integrable_G1 r x n).norm))
            (integrable_inv_one_add_sq.const_mul _) (fun t => ?_)
          exact ((hpt t).1.sum_le_tsum _ (fun n _ => norm_nonneg _)).trans (hpt t).2
      _ = C * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  exact summable_of_sum_range_le (fun n => integral_nonneg fun t => norm_nonneg _) hC

/-- **The dual expansion** of the Riesz mean `W_r` (`r ≥ 5`). -/
theorem dual_W {r : ℕ} (hr : 5 ≤ r) (x : ℝ) :
    HasSum (fun n => tauC n * kB r n x)
      ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) * TauPartialSumsSharp.WC tauC r x) := by
  have hr1 : 1 ≤ r := by omega
  -- second interchange
  have h2 := hasSum_integral_of_summable_integral_norm (integrable_G1 r x) (summable_G1 hr x)
  have h2' := h2.mul_left (((1 / (2 * π) : ℝ) : ℂ))
  have hterm : ∀ n, ((1 / (2 * π) : ℝ) : ℂ) * ∫ t, G1 r x n t = tauC n * kB r n x := by
    intro n; unfold G1 kB; rw [integral_const_mul]; ring
  simp_rw [hterm] at h2'
  convert h2' using 1
  -- the value
  have hF : ∑' n, ∫ t, F1 r x n t = ∫ t, ∑' n, F1 r x n t :=
    integral_tsum_of_summable_integral_norm (integrable_F1 hr1 x) (summable_F1 hr1 x)
  have hval : ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) : ℂ) * TauPartialSumsSharp.WC tauC r x =
      ((1 / (2 * π) : ℝ) : ℂ) * ∑' n, ∫ t, F1 r x n t := by
    rw [WC_eq_tsum hr1, ← tsum_mul_left, ← tsum_mul_left]
    congr 1; funext n
    unfold F1
    rw [integral_const_mul, mul_left_comm, riesz_term hr1 x n]
    ring
  rw [hval, hF]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [tsum_F1, modular_step]


/-! ### The kernel family: derivatives, continuity, scaling -/

/-- The integrand with a general exponent `m`. -/
noncomputable def gE (m n : ℕ) (y t : ℝ) : ℂ :=
  ((zl t) ^ m)⁻¹ * cexp (2 * π * (y * zl t - n * (zl t)⁻¹))

/-- `(1/2π) ∫ gE m n y`. -/
noncomputable def kE (m n : ℕ) (y : ℝ) : ℂ := ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, gE m n y t

lemma kB_eq_kE (j n : ℕ) (x : ℝ) : kB j n x = kE (13 + j) n x := rfl

lemma norm_gE_le {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (y t : ℝ) :
    ‖gE m n y t‖ ≤ Real.exp (2 * π * y) * (1 + t ^ 2)⁻¹ := by
  unfold gE
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_exp]
  have hre : (2 * π * ((y : ℂ) * zl t - (n : ℂ) * (zl t)⁻¹)).re = 2 * π * (y - n * (1 / (1 + t ^ 2))) := by
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, zl_re, zl_im, natCast_re, natCast_im,
      re_inv_zl, zero_mul, sub_zero, mul_one]
    simp
  rw [hre]
  have h1 := inv_norm_zl_pow_le hm t
  have h2 : Real.exp (2 * π * (y - n * (1 / (1 + t ^ 2)))) ≤ Real.exp (2 * π * y) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ (n : ℝ) * (1 / (1 + t ^ 2)) := by positivity
    nlinarith [Real.pi_pos]
  calc (‖zl t‖ ^ m)⁻¹ * Real.exp (2 * π * (y - n * (1 / (1 + t ^ 2))))
      ≤ (1 + t ^ 2)⁻¹ * Real.exp (2 * π * y) := by gcongr
    _ = _ := by ring

lemma continuous_gE (m n : ℕ) (y : ℝ) : Continuous (gE m n y) := by
  have := continuous_kB_integrand 0 n y
  unfold gE
  have hz := continuous_zl
  refine ((hz.pow _).inv₀ fun t => pow_ne_zero _ (zl_ne_zero t)).mul ?_
  exact Complex.continuous_exp.comp (continuous_const.mul ((continuous_const.mul hz).sub
    (continuous_const.mul (hz.inv₀ zl_ne_zero))))

lemma integrable_gE {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (y : ℝ) : Integrable (gE m n y) :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul _) (continuous_gE m n y).aestronglyMeasurable
    (Eventually.of_forall (norm_gE_le hm n y))

lemma hasDerivAt_gE (m n : ℕ) (t y : ℝ) :
    HasDerivAt (fun y : ℝ => gE (m + 1) n y t) (2 * π * gE m n y t) y := by
  unfold gE
  have hz := zl_ne_zero t
  have h1 : HasDerivAt (fun y : ℝ => 2 * π * ((y : ℂ) * zl t - n * (zl t)⁻¹)) (2 * π * zl t) y := by
    have := ((hasDerivAt_id y).ofReal_comp.mul_const (zl t)).sub_const ((n : ℂ) * (zl t)⁻¹)
    have := this.const_mul (2 * π : ℂ)
    simpa using this
  have h2 := (h1.cexp).const_mul (((zl t) ^ (m + 1))⁻¹)
  convert h2 using 1
  rw [pow_succ]
  field_simp

/-- `d/dy k_{m+1}(n,y) = 2π k_m(n,y)` (`m ≥ 2`). -/
theorem hasDerivAt_kE {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (y0 : ℝ) :
    HasDerivAt (kE (m + 1) n) (2 * π * kE m n y0) y0 := by
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), ∀ y ∈ Metric.ball y0 1,
      ‖2 * π * gE m n y t‖ ≤ 2 * π * Real.exp (2 * π * (y0 + 1)) * (1 + t ^ 2)⁻¹ := by
    refine Eventually.of_forall fun t y hy => ?_
    rw [norm_mul, show ‖(2 * π : ℂ)‖ = 2 * π by simp [abs_of_pos Real.pi_pos], mul_assoc (2 * π)]
    refine mul_le_mul_of_nonneg_left ((norm_gE_le hm n y t).trans ?_) (by positivity)
    gcongr
    have := (Real.dist_eq y y0 ▸ Metric.mem_ball.1 hy)
    have := (abs_lt.1 this).2
    linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y t => gE (m + 1) n y t) (F' := fun y t => 2 * π * gE m n y t) (x₀ := y0)
    (Metric.ball_mem_nhds y0 one_pos)
    (Eventually.of_forall fun y => (continuous_gE (m + 1) n y).aestronglyMeasurable)
    (integrable_gE (by omega) n y0) ((continuous_gE m n y0).aestronglyMeasurable.const_mul _) hb
    (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall fun t y _ => hasDerivAt_gE m n t y)
  unfold kE
  have := h.2.const_mul (((1 / (2 * π) : ℝ) : ℂ))
  convert this using 1
  rw [integral_const_mul]; ring

lemma continuous_kE {m : ℕ} (hm : 2 ≤ m) (n : ℕ) : Continuous (kE (m + 1) n) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_kE hm n y).continuousAt

lemma continuous_kB (j n : ℕ) : Continuous (kB j n) := by
  have e : 13 + j = (12 + j) + 1 := by omega
  have : kB j n = kE ((12 + j) + 1) n := by funext x; rw [kB_eq_kE, e]
  rw [this]; exact continuous_kE (by omega) n

/-- `k_{j+1}(n, y+h) − k_{j+1}(n, y) = 2π ∫₀^h k_j(n, y+s) ds`. -/
theorem kB_rel (j n : ℕ) (y h : ℝ) :
    kB (j + 1) n (y + h) - kB (j + 1) n y = 2 * π * ∫ s in (0 : ℝ)..h, kB j n (y + s) := by
  have hd : ∀ x ∈ Set.uIcc y (y + h), HasDerivAt (kB (j + 1) n) (2 * π * kB j n x) x := by
    intro x _
    have : kB (j + 1) n = kE ((13 + j) + 1) n := by funext x; rw [kB_eq_kE]; rfl
    rw [this]
    exact hasDerivAt_kE (by omega) n x
  have hc : Continuous fun x => 2 * π * kB j n x := continuous_const.mul (continuous_kB j n)
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_comp_add_left (fun x => kB j n x) y]
  simp


lemma sqrt_mul_sqrt_div {n x : ℝ} (hn : 0 < n) (hx : 0 < x) : √(n * x) * √(x / n) = x := by
  rw [← Real.sqrt_mul (by positivity)]
  have : n * x * (x / n) = x ^ 2 := by field_simp
  rw [this, Real.sqrt_sq hx.le]

lemma sqrt_mul_eq {n x : ℝ} (hn : 0 < n) (hx : 0 < x) : √(n * x) = n * √(x / n) := by
  rw [show n * x = n ^ 2 * (x / n) by field_simp, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]

/-- **Scaling**: `k_j(n,x) = (x/n)^{(12+j)/2} I_{12+j}(2π√(nx))`. -/
theorem kB_eq_Ik (j : ℕ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    kB j n x = (((√(x / n)) ^ (12 + j) * Ik (12 + j) (2 * π * √(n * x)) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set c := √(x / n) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  set L := 2 * π * √(n * x) with hL
  have hLc : L * c = 2 * π * x := by rw [hL, mul_assoc, sqrt_mul_sqrt_div hn0 hx]
  have hLn : L = 2 * π * n * c := by rw [hL, sqrt_mul_eq hn0 hx]; ring
  have hline := lineInt_eq_Ik (ν := 12 + j) (by omega) (L := L) (by positivity) hc0
  unfold LineInt at hline
  set g : ℝ → ℂ := fun u => fk (12 + j) L ((c : ℂ) + u * I) with hg
  have hsub := Measure.integral_comp_mul_left g c
  have hgc : ∀ t : ℝ, g (c * t) = ((c ^ (13 + j) : ℝ) : ℂ)⁻¹ * gE (13 + j) n x t := by
    intro t
    simp only [hg, fk, gE, zl]
    have hz : (1 : ℂ) + t * I ≠ 0 := zl_ne_zero t
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have e1 : (c : ℂ) + ((c * t : ℝ) : ℂ) * I = (c : ℂ) * (1 + t * I) := by push_cast; ring
    rw [e1]
    have e2 : (L : ℂ) * ((c : ℂ) * (1 + t * I) - ((c : ℂ) * (1 + t * I))⁻¹) =
        2 * π * ((x : ℂ) * (1 + t * I) - (n : ℂ) * (1 + t * I)⁻¹) := by
      have h1 : (L : ℂ) * c = 2 * π * x := by exact_mod_cast hLc
      have h2 : (L : ℂ) = 2 * π * n * c := by exact_mod_cast hLn
      have h3 : (L : ℂ) * (c : ℂ)⁻¹ = 2 * π * n := by rw [h2]; field_simp
      calc (L : ℂ) * ((c : ℂ) * (1 + t * I) - ((c : ℂ) * (1 + t * I))⁻¹)
          = ((L : ℂ) * c) * (1 + t * I) - ((L : ℂ) * (c : ℂ)⁻¹) * (1 + t * I)⁻¹ := by
            rw [mul_inv]; ring
        _ = _ := by rw [h1, h3]; ring
    rw [e2, mul_pow]
    push_cast
    rw [mul_inv]; ring
  have hint : ∫ t, g (c * t) = ((c ^ (13 + j) : ℝ) : ℂ)⁻¹ * ∫ t, gE (13 + j) n x t := by
    simp_rw [hgc]; rw [integral_const_mul]
  rw [hint, abs_inv, abs_of_pos hc0, Complex.real_smul] at hsub
  rw [kB_eq_kE]
  unfold kE
  have hci : ((c ^ (13 + j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hc0 _).ne'
  have hint2 : ∫ t, gE (13 + j) n x t = ((c ^ (13 + j) : ℝ) : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ∫ u, g u) := by
    rw [← hsub]; field_simp
  have hl : ((1 / (2 * π) : ℝ) : ℂ) * ∫ u, g u = (Ik (12 + j) L : ℂ) := hline
  rw [hint2]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ((1 / (2 * π) : ℝ) : ℂ) * (((c ^ (13 + j) : ℝ) : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ∫ u, g u))
      = ((c ^ (13 + j) : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) * (((1 / (2 * π) : ℝ) : ℂ) * ∫ u, g u) := by ring
    _ = _ := by
        rw [hl]; push_cast
        rw [show 13 + j = (12 + j) + 1 by omega, pow_succ]
        field_simp

/-! ### Iterated averages and the smoothed partial sum -/

/-- `It h 0 g = g`, `It h (j+1) g x = ∫₀^h (It h j g)(x+s) ds`. -/
noncomputable def It (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | j + 1, g => fun x => ∫ s in (0 : ℝ)..h, It h j g (x + s)

lemma continuous_It (h : ℝ) : ∀ (j : ℕ) (g : ℝ → ℂ), Continuous g → Continuous (It h j g) := by
  intro j
  induction j with
  | zero => intro g hg; exact hg
  | succ j ih =>
    intro g hg
    show Continuous fun x => ∫ s in (0 : ℝ)..h, It h j g (x + s)
    have hc := ih g hg
    have : Continuous (Function.uncurry fun x s : ℝ => It h j g (x + s)) :=
      hc.comp (continuous_fst.add continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 h

/-- `Δ_h^r k_r(n,·)(x) = (2π)^r It_h^r k_0(n,·)(x)`. -/
theorem DkC_kB {h : ℝ} (hh : 0 ≤ h) (n : ℕ) : ∀ (r : ℕ) (x : ℝ), 0 < x →
    TauPartialSumsSharp.DkC h r (kB r n) x = (2 * π : ℂ) ^ r * It h r (kB 0 n) x := by
  intro r
  induction r with
  | zero => intro x _; simp [TauPartialSumsSharp.DkC, It]
  | succ r ih =>
    intro x hx
    simp only [TauPartialSumsSharp.DkC]
    have e : (fun y => kB (r + 1) n (y + h) - kB (r + 1) n y) =
        fun y => (2 * π : ℂ) * ∫ s in (0 : ℝ)..h, kB r n (y + s) := by
      funext y; exact kB_rel r n y h
    rw [e, TauPartialSumsSharp.DkC_const_mul,
      TauPartialSumsSharp.DkC_integral_on h hh r _ (continuous_kB r n).continuousOn x hx]
    have e2 : ∫ s in (0 : ℝ)..h, TauPartialSumsSharp.DkC h r (kB r n) (x + s) =
        ∫ s in (0 : ℝ)..h, (2 * π : ℂ) ^ r * It h r (kB 0 n) (x + s) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hh] at hs
      exact ih (x + s) (by linarith [hs.1])
    rw [e2, intervalIntegral.integral_const_mul]
    show _ = (2 * π : ℂ) ^ (r + 1) * ∫ s in (0 : ℝ)..h, It h r (kB 0 n) (x + s)
    ring

lemma DkC_summable (h : ℝ) (hh : 0 ≤ h) (r : ℕ) : ∀ (f : ℕ → ℝ → ℂ) (x : ℝ),
    (∀ y ∈ Icc x (x + r * h), Summable fun n => f n y) →
    Summable fun n => TauPartialSumsSharp.DkC h r (f n) x := by
  induction r with
  | zero => intro f x hs; exact hs x ⟨le_rfl, by simp⟩
  | succ r ih =>
    intro f x hs
    simp only [TauPartialSumsSharp.DkC]
    refine ih (fun n y => f n (y + h) - f n y) x (fun y hy => ?_)
    have h1 := hs (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
    have h2 := hs y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
    exact h1.sub h2

/-- **The smoothed partial sum**: `Δ_h^r W_r(x) = r! Σ_n τ(n) It_h^r k_0(n,·)(x)`. -/
theorem DkC_WC_eq {r : ℕ} (hr : 5 ≤ r) {h : ℝ} (hh : 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => tauC n * It h r (kB 0 n) x)
      (((Nat.factorial r : ℝ) : ℂ)⁻¹ * TauPartialSumsSharp.DkC h r (TauPartialSumsSharp.WC tauC r) x) := by
  set c : ℂ := ((((2 * π) ^ r / (Nat.factorial r : ℝ)) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact Complex.ofReal_ne_zero.2 (div_pos (pow_pos (by positivity) r)
      (by exact_mod_cast Nat.factorial_pos r)).ne'
  have hW : TauPartialSumsSharp.WC tauC r = fun y => c⁻¹ * ∑' n, tauC n * kB r n y := by
    funext y
    rw [(dual_W hr y).tsum_eq, ← hc]; field_simp
  have hs : ∀ y, Summable fun n => tauC n * kB r n y := fun y => (dual_W hr y).summable
  rw [hW, TauPartialSumsSharp.DkC_const_mul,
    TauPartialSumsSharp.DkC_tsum_on h hh r _ x (fun y _ => hs y)]
  have hsum : Summable fun n => TauPartialSumsSharp.DkC h r (fun y => tauC n * kB r n y) x :=
    DkC_summable h hh r _ x (fun y _ => hs y)
  have e : ∀ n, TauPartialSumsSharp.DkC h r (fun y => tauC n * kB r n y) x =
      (2 * π : ℂ) ^ r * (tauC n * It h r (kB 0 n) x) := by
    intro n
    rw [TauPartialSumsSharp.DkC_const_mul, DkC_kB hh n r x hx]; ring
  simp_rw [e] at hsum ⊢
  have hpi : (2 * π : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0))
  have hsum' : Summable fun n => tauC n * It h r (kB 0 n) x := by
    have := hsum.mul_left ((2 * π : ℂ) ^ r)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hpi] using this
  rw [tsum_mul_left]
  have hf : ((Nat.factorial r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have e3 : ((Nat.factorial r : ℝ) : ℂ)⁻¹ * (c⁻¹ * ((2 * π : ℂ) ^ r * ∑' n, tauC n * It h r (kB 0 n) x)) =
      ∑' n, tauC n * It h r (kB 0 n) x := by
    have hf' : ((Nat.factorial r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
    rw [hc]; push_cast; field_simp
  rw [e3]; exact hsum'.hasSum

end RamanujanTau.VoronoiTrunc
