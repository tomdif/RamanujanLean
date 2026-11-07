/-
# Sub-Hecke bound for τ: definitions and the majorant of the unfolded Poincaré integral

Notation (Iwaniec, *Topics in classical automorphic forms*, §3.2; Kloosterman 1927):

* `ee z = exp(2πiz)`;
* `kloosterman m n c = S(m,n;c) = ∑_{d mod c, (d,c)=1} e((m d + n d̄)/c)`;
* `kInt n c y = ∫_ℝ w^{-12} e(-1/(c² w)) e(-n w) dx`, `w = x + iy` — the `c`-th term of the unfolded
  Fourier coefficient of the weight-12 Poincaré series `P₁` (numerically
  `c^{-12} kInt n c (1/n) = 2π n^{11/2} J₁₁(4π√n/c)/c`, see `scripts/taubound/check_kint.py`).

Main result of this file: the elementary majorant
`‖kInt n c y‖ ≤ M_r e^{2πny} (2πy/c²)^{-r} (y²)^{r-6} y J_r` for every `0 ≤ r < 11/2`,
obtained from `e^{-t} ≤ M_r t^{-r}` and `∫ (x²+y²)^{r-6} dx = (y²)^{r-6} y ∫ (1+s²)^{r-6} ds`.
No oscillation of the integrand is used.
-/
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory
open scoped Real

/-- `e(z) = exp(2πiz)`. -/
noncomputable def ee (z : ℂ) : ℂ := Complex.exp (2 * π * I * z)

lemma norm_ee (z : ℂ) : ‖ee z‖ = Real.exp (-2 * π * z.im) := by
  rw [ee, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The Kloosterman sum `S(m,n;c) = ∑_{0 ≤ d < c, (d,c)=1} e((m d + n d̄)/c)`, `d̄ = d⁻¹ mod c`. -/
noncomputable def kloosterman (m n : ℤ) (c : ℕ) : ℂ :=
  ∑ d ∈ (Finset.range c).filter (fun d => Nat.Coprime d c),
    ee (((m : ℂ) * d + (n : ℂ) * (((d : ZMod c)⁻¹).val : ℂ)) / c)

/-- Trivial bound `|S(m,n;c)| ≤ c`. -/
lemma norm_kloosterman_le (m n : ℤ) (c : ℕ) : ‖kloosterman m n c‖ ≤ c := by
  unfold kloosterman
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ d ∈ (Finset.range c).filter (fun d => Nat.Coprime d c),
      ‖ee (((m : ℂ) * d + (n : ℂ) * (((d : ZMod c)⁻¹).val : ℂ)) / c)‖ = 1 := by
    intro d _
    rw [norm_ee]
    have : ((((m : ℂ) * d + (n : ℂ) * (((d : ZMod c)⁻¹).val : ℂ)) / c)).im = 0 := by
      rw [Complex.div_im]; simp
    simp [this]
  rw [Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- The unfolded Poincaré integral `K(n,c;y) = ∫_ℝ w^{-12} e(-1/(c²w)) e(-nw) dx`, `w = x+iy`. -/
noncomputable def kInt (n c : ℕ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) + y * I) ^ (-12 : ℤ) * ee (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + y * I))) *
    ee (-(n : ℂ) * ((x : ℂ) + y * I))

/-! ### `e^{-t} ≤ M_r t^{-r}` -/

/-- The constant `M_r = ⌈r⌉₊! + 1`. -/
noncomputable def expConst (r : ℝ) : ℝ := (Nat.factorial ⌈r⌉₊ : ℝ) + 1

lemma expConst_pos (r : ℝ) : 0 < expConst r := by unfold expConst; positivity

lemma rpow_mul_exp_neg_le {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    t ^ r * Real.exp (-t) ≤ expConst r := by
  unfold expConst
  rcases le_or_gt t 1 with h1 | h1
  · have : t ^ r ≤ 1 := Real.rpow_le_one ht.le h1 hr
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : t ^ r * Real.exp (-t) ≤ 1 := by
      calc t ^ r * Real.exp (-t) ≤ 1 * 1 :=
            mul_le_mul this h2 (Real.exp_pos _).le zero_le_one
        _ = 1 := by ring
    have : (0 : ℝ) ≤ (Nat.factorial ⌈r⌉₊ : ℝ) := by positivity
    linarith
  · set m := ⌈r⌉₊
    have hrm : r ≤ (m : ℝ) := Nat.le_ceil r
    have h3 : t ^ r ≤ t ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hrm
    have h4 : t ^ m / (Nat.factorial m) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le m
    rw [Real.rpow_natCast] at h3
    have hf : (0 : ℝ) < Nat.factorial m := by positivity
    have h5 : t ^ m ≤ Nat.factorial m * Real.exp t := by
      rw [div_le_iff₀ hf] at h4; linarith
    have h6 : t ^ r * Real.exp (-t) ≤ Nat.factorial m := by
      calc t ^ r * Real.exp (-t) ≤ (Nat.factorial m * Real.exp t) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right (h3.trans h5) (Real.exp_pos _).le
        _ = Nat.factorial m := by rw [mul_assoc, ← Real.exp_add]; simp
    linarith

lemma exp_neg_le_rpow {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    Real.exp (-t) ≤ expConst r * t ^ (-r) := by
  have h := rpow_mul_exp_neg_le hr ht
  have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  rw [Real.rpow_neg ht.le, ← div_eq_mul_inv, le_div_iff₀ htr]
  linarith [mul_comm (t ^ r) (Real.exp (-t))]

/-! ### The Japanese-bracket integral -/

/-- `J_r = ∫_ℝ (1+s²)^{r-6} ds`. -/
noncomputable def jConst (r : ℝ) : ℝ := ∫ s : ℝ, (1 + s ^ 2) ^ (r - 6)

lemma integrable_japanese {r : ℝ} (hr : r < 11 / 2) :
    Integrable (fun s : ℝ => (1 + s ^ 2) ^ (r - 6)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 12 - 2 * r)
    (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1; ring

lemma jConst_nonneg (r : ℝ) : 0 ≤ jConst r :=
  integral_nonneg fun s => Real.rpow_nonneg (by positivity) _

lemma bracket_eq {r y : ℝ} (hy : 0 < y) (x : ℝ) :
    (x ^ 2 + y ^ 2) ^ (r - 6) = (y ^ 2) ^ (r - 6) * (1 + (x / y) ^ 2) ^ (r - 6) := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

lemma integrable_bracket {r y : ℝ} (hr : r < 11 / 2) (hy : 0 < y) :
    Integrable (fun x : ℝ => (x ^ 2 + y ^ 2) ^ (r - 6)) := by
  have h := ((integrable_japanese hr).comp_div hy.ne').const_mul ((y ^ 2) ^ (r - 6))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [bracket_eq hy x]

lemma integral_bracket {r y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ, (x ^ 2 + y ^ 2) ^ (r - 6) = (y ^ 2) ^ (r - 6) * y * jConst r := by
  simp_rw [bracket_eq hy]
  rw [integral_const_mul]
  have := Measure.integral_comp_div (fun s : ℝ => (1 + s ^ 2) ^ (r - 6)) y
  simp only at this
  rw [this, abs_of_pos hy, jConst, smul_eq_mul]
  ring

/-! ### The pointwise majorant -/

lemma norm_w_zpow {x y : ℝ} (hy : 0 < y) :
    ‖((x : ℂ) + y * I) ^ (-12 : ℤ)‖ = (x ^ 2 + y ^ 2) ^ (-6 : ℝ) := by
  rw [norm_zpow]
  have hn : ‖(x : ℂ) + y * I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def]; congr 1; simp [Complex.normSq_apply]; ring
  rw [hn, show (-12 : ℤ) = 2 * (-6 : ℤ) by norm_num, zpow_mul, zpow_two]
  rw [Real.mul_self_sqrt (by positivity)]
  rw [← Real.rpow_intCast]; norm_num

lemma im_neg_inv {x y : ℝ} (c : ℝ) (hc : c ≠ 0) (hy : 0 < y) :
    (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + y * I))).im = y / (c ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hu : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  rw [Complex.div_im]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  field_simp

lemma norm_integrand_le {r : ℝ} (hr : 0 ≤ r) (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y)
    (x : ℝ) :
    ‖((x : ℂ) + y * I) ^ (-12 : ℤ) * ee (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + y * I))) *
        ee (-(n : ℂ) * ((x : ℂ) + y * I))‖ ≤
      expConst r * Real.exp (2 * π * n * y) * (2 * π * y / (c : ℝ) ^ 2) ^ (-r) *
        (x ^ 2 + y ^ 2) ^ (r - 6) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hu : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [norm_mul, norm_mul, norm_w_zpow hy, norm_ee, norm_ee]
  have hc2 : ((c : ℂ)) = ((c : ℝ) : ℂ) := by simp
  rw [hc2, im_neg_inv (c : ℝ) hc' hy]
  have him : (-(n : ℂ) * ((x : ℂ) + y * I)).im = -(n * y) := by simp
  rw [him]
  set t := 2 * π * y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) with ht
  have htpos : 0 < t := by positivity
  have hexp : Real.exp (-2 * π * (y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)))) = Real.exp (-t) := by
    rw [ht]; congr 1; ring
  rw [hexp]
  have hb := exp_neg_le_rpow hr htpos
  have ht2 : t ^ (-r) = (2 * π * y / (c : ℝ) ^ 2) ^ (-r) * (x ^ 2 + y ^ 2) ^ r := by
    rw [ht, show 2 * π * y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) =
      (2 * π * y / (c : ℝ) ^ 2) * (x ^ 2 + y ^ 2)⁻¹ by field_simp]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hu.le,
      ← Real.rpow_neg hu.le, neg_neg]
  have hsplit : (x ^ 2 + y ^ 2) ^ (r - 6) = (x ^ 2 + y ^ 2) ^ (-6 : ℝ) * (x ^ 2 + y ^ 2) ^ r := by
    rw [← Real.rpow_add hu]; ring_nf
  rw [hsplit]
  have he2 : Real.exp (-2 * π * -(↑n * y)) = Real.exp (2 * π * n * y) := by ring_nf
  rw [he2]
  have hA : 0 ≤ (x ^ 2 + y ^ 2) ^ (-6 : ℝ) := Real.rpow_nonneg hu.le _
  have hE : 0 ≤ Real.exp (2 * π * n * y) := (Real.exp_pos _).le
  calc (x ^ 2 + y ^ 2) ^ (-6 : ℝ) * Real.exp (-t) * Real.exp (2 * π * n * y)
      ≤ (x ^ 2 + y ^ 2) ^ (-6 : ℝ) * (expConst r * t ^ (-r)) * Real.exp (2 * π * n * y) := by
        gcongr
    _ = _ := by rw [ht2]; ring

/-- **Majorant of the unfolded Poincaré integral** (no oscillation used). -/
theorem norm_kInt_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 11 / 2) (n c : ℕ) (hc : c ≠ 0) {y : ℝ}
    (hy : 0 < y) :
    ‖kInt n c y‖ ≤ expConst r * Real.exp (2 * π * n * y) * (2 * π * y / (c : ℝ) ^ 2) ^ (-r) *
      ((y ^ 2) ^ (r - 6) * y * jConst r) := by
  unfold kInt
  have hint := (integrable_bracket hr hy).const_mul
    (expConst r * Real.exp (2 * π * n * y) * (2 * π * y / (c : ℝ) ^ 2) ^ (-r))
  refine (norm_integral_le_of_norm_le hint
    (Filter.Eventually.of_forall fun x => norm_integrand_le hr0 n c hc hy x)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_bracket hy]

end RamanujanTau.TauBound
