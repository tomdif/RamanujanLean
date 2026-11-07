/-
# Two explicit line integrals (the residue bookkeeping, done by arctangent)

For real `α, β ≠ 0`,

    ∫_ℝ (1/(α+it) − 1/(β+it)) dt = π (sgn α − sgn β)          (`integral_inv_sub_line`).

So `u(s) = 1/(s−p) − 1/(s−q)` has line integral `0` to the right of `p, q` and `−2π` on a line
separating `q < Re s < p`: this replaces the residue theorem in the contour shift of `Dual`.
Proof: `t ↦ g(t)` satisfies `g(−t) = conj g(t)`, so the integral is real; its real part is
`∫ α/(α²+t²) − ∫ β/(β²+t²)` and `∫ α/(α²+t²) dt = π α/|α|` (`integral_univ_inv_one_add_sq`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory

lemma normSq_line (α t : ℝ) : Complex.normSq ((α : ℂ) + t * I) = α ^ 2 + t ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma ne_zero_line {α : ℝ} (hα : α ≠ 0) (t : ℝ) : (α : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; exact hα this

/-- `∫ α/(α²+t²) dt = π α/|α|`. -/
lemma integral_div_sq_add {α : ℝ} (hα : α ≠ 0) :
    ∫ t : ℝ, α / (α ^ 2 + t ^ 2) = π * (α / |α|) := by
  have ha : 0 < |α| := abs_pos.2 hα
  have e : ∀ t : ℝ, α / (α ^ 2 + t ^ 2) = (α / |α| ^ 2) * (1 + (|α|⁻¹ * t) ^ 2)⁻¹ := by
    intro t
    have : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [this]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => (1 + u ^ 2)⁻¹) |α|⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos ha, smul_eq_mul]
  field_simp

lemma integrable_div_sq_add {α : ℝ} (hα : α ≠ 0) :
    Integrable fun t : ℝ => α / (α ^ 2 + t ^ 2) := by
  have ha : 0 < |α| := abs_pos.2 hα
  have e : (fun t : ℝ => α / (α ^ 2 + t ^ 2)) =
      fun t => (α / |α| ^ 2) * (1 + (|α|⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    have : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [this]; field_simp
  rw [e]
  exact (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero ha.ne')).const_mul _

lemma inv_line_re (α t : ℝ) : (1 / ((α : ℂ) + t * I)).re = α / (α ^ 2 + t ^ 2) := by
  rw [Complex.div_re, normSq_line]; simp

lemma inv_line_im (α t : ℝ) : (1 / ((α : ℂ) + t * I)).im = -(t / (α ^ 2 + t ^ 2)) := by
  rw [Complex.div_im, normSq_line]; simp

lemma integrable_odd_part {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    Integrable fun t : ℝ => t / (α ^ 2 + t ^ 2) - t / (β ^ 2 + t ^ 2) := by
  have ha : 0 < α ^ 2 := by positivity
  have hb : 0 < β ^ 2 := by positivity
  set μ₀ : ℝ := min (min (α ^ 2) (β ^ 2)) 1 with hμ₀
  have hμ : 0 < μ₀ := lt_min (lt_min ha hb) one_pos
  have hμa : μ₀ ≤ α ^ 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hμb : μ₀ ≤ β ^ 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hμ1 : μ₀ ≤ 1 := min_le_right _ _
  set C : ℝ := |β ^ 2 - α ^ 2| / μ₀ ^ 2 with hC
  refine (integrable_inv_one_add_sq.const_mul C).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  have hA : 0 < α ^ 2 + t ^ 2 := by positivity
  have hB : 0 < β ^ 2 + t ^ 2 := by positivity
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have e : t / (α ^ 2 + t ^ 2) - t / (β ^ 2 + t ^ 2) =
      t * (β ^ 2 - α ^ 2) / ((α ^ 2 + t ^ 2) * (β ^ 2 + t ^ 2)) := by
    field_simp; ring
  have hAm : μ₀ * (1 + t ^ 2) ≤ α ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hBm : μ₀ * (1 + t ^ 2) ≤ β ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have htt : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hA hB), div_le_iff₀ (mul_pos hA hB), hC]
  have hprod : (μ₀ * (1 + t ^ 2)) * (μ₀ * (1 + t ^ 2)) ≤ (α ^ 2 + t ^ 2) * (β ^ 2 + t ^ 2) :=
    mul_le_mul hAm hBm (by positivity) hA.le
  calc |t| * |β ^ 2 - α ^ 2| ≤ (1 + t ^ 2) * |β ^ 2 - α ^ 2| := by gcongr
    _ = |β ^ 2 - α ^ 2| / μ₀ ^ 2 * (1 + t ^ 2)⁻¹ * ((μ₀ * (1 + t ^ 2)) * (μ₀ * (1 + t ^ 2))) := by
        field_simp
    _ ≤ |β ^ 2 - α ^ 2| / μ₀ ^ 2 * (1 + t ^ 2)⁻¹ * ((α ^ 2 + t ^ 2) * (β ^ 2 + t ^ 2)) := by
        gcongr

/-- **The line integral of `1/(α+it) − 1/(β+it)`.** -/
theorem integral_inv_sub_line {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∫ t : ℝ, (1 / ((α : ℂ) + t * I) - 1 / ((β : ℂ) + t * I)) = (π * (α / |α| - β / |β|) : ℝ) := by
  set R : ℝ → ℝ := fun t => α / (α ^ 2 + t ^ 2) - β / (β ^ 2 + t ^ 2) with hR
  set O : ℝ → ℝ := fun t => t / (α ^ 2 + t ^ 2) - t / (β ^ 2 + t ^ 2) with hO
  have hg : ∀ t : ℝ, (1 / ((α : ℂ) + t * I) - 1 / ((β : ℂ) + t * I)) =
      ((R t : ℝ) : ℂ) - ((O t : ℝ) : ℂ) * I := by
    intro t
    apply Complex.ext
    · simp only [sub_re, inv_line_re, hR, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
    · simp only [sub_im, inv_line_im, hO, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hIR : Integrable R := (integrable_div_sq_add hα).sub (integrable_div_sq_add hβ)
  have hIO : Integrable O := integrable_odd_part hα hβ
  have hO0 : ∫ t, O t = 0 := by
    have h1 : ∫ t, O (-t) = ∫ t, O t := integral_neg_eq_self O volume
    have h2 : ∀ t, O (-t) = -O t := by intro t; simp only [hO]; ring_nf
    simp_rw [h2, integral_neg] at h1
    linarith
  simp_rw [hg]
  have h1 : Integrable (fun t => ((R t : ℝ) : ℂ)) := hIR.ofReal
  have h2 : Integrable (fun t => ((O t : ℝ) : ℂ) * I) := hIO.ofReal.mul_const I
  rw [integral_sub h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    hO0]
  have hRi : ∫ t, R t = π * (α / |α|) - π * (β / |β|) := by
    simp only [hR]
    rw [integral_sub (integrable_div_sq_add hα) (integrable_div_sq_add hβ),
      integral_div_sq_add hα, integral_div_sq_add hβ]
  rw [hRi]; push_cast; ring

lemma integrable_inv_sub_line {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    Integrable fun t : ℝ => 1 / ((α : ℂ) + t * I) - 1 / ((β : ℂ) + t * I) := by
  set R : ℝ → ℝ := fun t => α / (α ^ 2 + t ^ 2) - β / (β ^ 2 + t ^ 2) with hR
  set O : ℝ → ℝ := fun t => t / (α ^ 2 + t ^ 2) - t / (β ^ 2 + t ^ 2) with hO
  have hg : ∀ t : ℝ, (1 / ((α : ℂ) + t * I) - 1 / ((β : ℂ) + t * I)) =
      ((R t : ℝ) : ℂ) - ((O t : ℝ) : ℂ) * I := by
    intro t
    apply Complex.ext
    · simp only [sub_re, inv_line_re, hR, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
    · simp only [sub_im, inv_line_im, hO, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have h1 : Integrable (fun t => ((R t : ℝ) : ℂ)) :=
    ((integrable_div_sq_add hα).sub (integrable_div_sq_add hβ)).ofReal
  have h2 : Integrable (fun t => ((O t : ℝ) : ℂ) * I) :=
    (integrable_odd_part hα hβ).ofReal.mul_const I
  exact (h1.sub h2).congr (Filter.Eventually.of_forall fun t => (hg t).symm)

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.integral_inv_sub_line
#print axioms RamanujanTau.RankinLandau.integrable_inv_sub_line
