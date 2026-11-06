/-
# Hardy's Z-function of Δ and the mollifier

* `ZH t = (2π)⁶ Λ(6+it)/|Γ(6+it)|`: real (because `Λ(6+it)` is real), continuous, and
  `|ZH t| = |L(Δ,6+it)|` (`norm_tauL_line`); zeros of `ZH` are critical zeros of `L(Δ,s)`.
* `Mc b y s = Σ_{1≤n≤y} b(n) n^{11/2−s}`: on the line, `Mc b y (6+it) = Σ b(n) n^{−1/2−it}`,
  the mollifier in the normalisation `λ(n) = τ(n) n^{−11/2}`.  `wM b y t = |M(6+it)|²`.
* `norm_tauL_sub_one_le_all`: `|L(7+k+iv) − 1| ≤ 2^{−k} S` for all `k`, `v`.
-/
import RamanujanTau.HafnerProportion.Reduce
import RamanujanTau.HardyCount.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HardyZeros RamanujanTau.HardyCount
open scoped Real

lemma six_add_ne_neg_nat (t : ℝ) (m : ℕ) : (6 + t * I : ℂ) ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma Gamma_line_ne_zero (t : ℝ) : Gamma (6 + t * I) ≠ 0 :=
  Complex.Gamma_ne_zero (six_add_ne_neg_nat t)

lemma continuous_Gamma_line : Continuous fun t : ℝ => Gamma (6 + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h1 : ContinuousAt Gamma (6 + t * I) :=
    (Complex.differentiableAt_Gamma _ (six_add_ne_neg_nat t)).continuousAt
  have h2 : Continuous fun t : ℝ => (6 + t * I : ℂ) := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => (6 + t * I : ℂ)) (g := Gamma) h1 h2.continuousAt

/-- Hardy's `Z`-function of `Δ`, normalised so that `|ZH t| = |L(Δ, 6+it)|`. -/
noncomputable def ZH (t : ℝ) : ℝ := (2 * π) ^ (6 : ℕ) * Zr t / ‖Gamma (6 + t * I)‖

lemma continuous_ZH : Continuous ZH :=
  (continuous_const.mul continuous_Zr).div (continuous_norm.comp continuous_Gamma_line)
    fun t => norm_ne_zero_iff.mpr (Gamma_line_ne_zero t)

lemma norm_tauL_line (t : ℝ) : ‖tauL (6 + t * I)‖ = |ZH t| := by
  have hZ : heckeLambda (6 + t * I) = (Zr t : ℂ) := Zc_eq_Zr t
  have hpow : ‖(2 * π : ℂ) ^ (6 + t * I)‖ = (2 * π) ^ (6 : ℕ) := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have : ((6 : ℂ) + t * I).re = ((6 : ℕ) : ℝ) := by simp
    rw [this, Real.rpow_natCast]
  have hG := norm_pos_iff.mpr (Gamma_line_ne_zero t)
  rw [tauL, hZ, norm_mul, norm_mul, hpow, norm_inv, Complex.norm_real, Real.norm_eq_abs, ZH,
    abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (6 : ℕ)),
    abs_of_pos hG]
  field_simp

lemma tauL_zero_of_ZH_zero {t : ℝ} (h0 : ZH t = 0) : tauL (6 + t * I) = 0 := by
  have := norm_tauL_line t
  rw [h0, abs_zero] at this
  exact norm_eq_zero.mp this

/-- The mollifier `M(s) = Σ_{1≤n≤y} b(n) n^{11/2−s}`. -/
noncomputable def Mc (b : ℕ → ℂ) (y : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, b n * (n : ℂ) ^ ((11 / 2 : ℂ) - s)

/-- The Selberg weight `|M(6+it)|²`. -/
noncomputable def wM (b : ℕ → ℂ) (y : ℕ) (t : ℝ) : ℝ := ‖Mc b y (6 + t * I)‖ ^ 2

lemma differentiable_Mc (b : ℕ → ℂ) (y : ℕ) : Differentiable ℂ (Mc b y) := by
  unfold Mc
  refine Differentiable.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (show n ≠ 0 by omega)
  exact (differentiable_const _).mul
    (((differentiable_const _).sub differentiable_id).const_cpow (Or.inl hn0))

lemma continuous_wM (b : ℕ → ℂ) (y : ℕ) : Continuous (wM b y) := by
  have h2 : Continuous fun t : ℝ => (6 + t * I : ℂ) := by fun_prop
  exact (continuous_norm.comp ((differentiable_Mc b y).continuous.comp h2)).pow 2

lemma wM_nonneg (b : ℕ → ℂ) (y : ℕ) (t : ℝ) : 0 ≤ wM b y t := by unfold wM; positivity

lemma norm_LM2_line (b : ℕ → ℂ) (y : ℕ) (t : ℝ) :
    ‖tauL (6 + t * I) * Mc b y (6 + t * I) ^ 2‖ = |ZH t| * wM b y t := by
  rw [norm_mul, norm_pow, norm_tauL_line, wM]

/-- `|L(Δ, 7+k+iv) − 1| ≤ 2^{−k} S` with one `S` for all `k`. -/
theorem norm_tauL_sub_one_le_all :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k : ℕ, ∀ y : ℝ,
      ‖tauL (((7 + k : ℝ) : ℂ) + y * I) - 1‖ ≤ (1 / 2) ^ k * S := by
  have hsum7 : LSeriesSummable tauC (7 : ℂ) := LSeriesSummable_tau_of_gt_13_2 (by norm_num)
  set S : ℝ := ∑' n, ‖LSeries.term tauC 7 n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨S, hS0, fun k y => ?_⟩
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

end RamanujanTau.HafnerProportion
