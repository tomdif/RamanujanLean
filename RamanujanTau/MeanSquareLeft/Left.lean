/-
# Mean square of `L(Δ,s)` on every line `Re s = σ < 6`

    ∫₀ᵀ |L(Δ, σ+it)|² dt  ~  C(σ) T^{25−4σ},
    C(σ) = (2π)^{4σ−24} · RS(24−2σ) / (25−4σ),     RS(β) = Σ τ(n)² n^{−β}.

* `norm_tauL_fe`: the functional equation in norm form (any `σ < 12`, any `t`):
  `|L(σ+it)| = (2π)^{2σ−12} |Γ(12−σ+it)/Γ(σ+it)| |L(12−σ+it)|`.
* `tendsto_Qr` (GammaAsymp): `|Γ(12−σ+it)/Γ(σ+it)| / t^{12−2σ} → 1`, so
  `|χ(σ+it)|² / t^{24−4σ} → (2π)^{4σ−24}`.
* the mean square on `Re s = 12−σ > 6` (`MeanSquareFull.mean_square_tauL_full`), and the
  Abelian lemma `abel_mean` with `α = 24−4σ > 0`.
-/
import RamanujanTau.MeanSquareLeft.GammaAsymp
import RamanujanTau.MeanSquareLeft.Abel
import RamanujanTau.MeanSquareFull.Main
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.MeanSquareLeft

open Complex Real Filter Topology MeasureTheory
open RamanujanTau.HeckeL
open scoped ComplexConjugate

/-- `RS(β) = Σ_{n} τ(n)² n^{−β}` (the Rankin–Selberg Dirichlet series, convergent for `β > 12`). -/
noncomputable def RS (β : ℝ) : ℝ := ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)

/-- The left-of-centre mean-square constant `C(σ) = (2π)^{4σ−24} RS(24−2σ)/(25−4σ)`. -/
noncomputable def Cleft (σ : ℝ) : ℝ := (2 * π) ^ (4 * σ - 24) * RS (2 * (12 - σ)) / (25 - 4 * σ)

/-- **Functional equation, norm form.** For `σ < 12` and every real `t`. -/
theorem norm_tauL_fe {σ : ℝ} (hσ : σ < 12) (t : ℝ) :
    ‖tauL ((σ : ℂ) + t * I)‖ = (2 * π) ^ (2 * σ - 12) *
      (‖Complex.Gamma (((12 - σ : ℝ) : ℂ) + t * I)‖ / ‖Complex.Gamma ((σ : ℂ) + t * I)‖) *
        ‖tauL (((12 - σ : ℝ) : ℂ) + t * I)‖ := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hs : s.re = σ := by simp [hsdef]
  have hs0 : ∀ n : ℕ, 12 - s ≠ -n := by
    intro n h; have := congrArg re h; simp [hs] at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hT : tauL s = ((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))) *
      (Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹) * tauL (12 - s) := by
    conv_lhs => rw [tauL, ← heckeLambda_functional_equation s, heckeLambda_eq_tauL hs0]
    ring
  have e : 12 - s = conj (((12 - σ : ℝ) : ℂ) + t * I) := by
    apply Complex.ext <;> simp [hsdef]
  have hP : ‖(2 * π : ℂ) ^ s‖ * ‖(2 * π : ℂ) ^ (-(12 - s))‖ = (2 * π) ^ (2 * σ - 12) := by
    rw [RamanujanTau.HeckeConvex.norm_two_pi_cpow',
      RamanujanTau.HeckeConvex.norm_two_pi_cpow', ← Real.rpow_add (by positivity)]
    congr 1; simp [hs]; ring
  rw [hT, norm_mul, norm_mul, norm_mul, hP, norm_mul, norm_inv, e, RamanujanTau.RankinError.norm_Gamma_conj,
    RamanujanTau.HeckeZeros.tauL_conj, Complex.norm_conj]
  ring

lemma continuous_normsq_line (σ : ℝ) :
    Continuous fun t : ℝ => ‖tauL ((σ : ℂ) + t * I)‖ ^ 2 :=
  (tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2

lemma two_pi_sq (σ : ℝ) : ((2 * π) ^ (2 * σ - 12)) ^ 2 = (2 * π) ^ (4 * σ - 24) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

/-- `|χ(σ+it)|² / t^{24−4σ} → (2π)^{4σ−24}`. -/
lemma tendsto_chi_sq {σ : ℝ} (hσ : σ ≤ 6) :
    Tendsto (fun t : ℝ => ((2 * π) ^ (2 * σ - 12) *
      (‖Complex.Gamma (((12 - σ : ℝ) : ℂ) + t * I)‖ / ‖Complex.Gamma ((σ : ℂ) + t * I)‖)) ^ 2 /
        t ^ (24 - 4 * σ)) atTop (𝓝 ((2 * π) ^ (4 * σ - 24))) := by
  have hQ := tendsto_Qr (a := σ) (b := 12 - σ) (by linarith)
  have h := (hQ.pow 2).const_mul (((2 * π) ^ (2 * σ - 12)) ^ 2)
  rw [one_pow, mul_one, two_pi_sq] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold Qr
  have h1 := norm_Gamma_vert_pos σ ht.ne'
  have hP : 0 < t ^ (12 - σ - σ) := Real.rpow_pos_of_pos ht _
  have hα : t ^ (24 - 4 * σ) = (t ^ (12 - σ - σ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
  rw [hα]
  field_simp
  rw [← two_pi_sq]; ring

/-- **Mean square of `L(Δ,s)` left of the critical line.** For every `σ < 6`,
`∫₀ᵀ |L(Δ,σ+it)|² dt / T^{25−4σ} → (2π)^{4σ−24} RS(24−2σ)/(25−4σ)`. -/
theorem mean_square_tauL_left {σ : ℝ} (hσ : σ < 6) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) /
      T ^ (25 - 4 * σ)) atTop (𝓝 (Cleft σ)) := by
  have hA := RamanujanTau.MeanSquareFull.mean_square_tauL_full (σ := 12 - σ) (by linarith)
  have h := abel_mean (g := fun t : ℝ => ‖tauL (((12 - σ : ℝ) : ℂ) + t * I)‖ ^ 2)
    (F := fun t : ℝ => ‖tauL ((σ : ℂ) + t * I)‖ ^ 2)
    (h := fun t : ℝ => ((2 * π) ^ (2 * σ - 12) *
      (‖Complex.Gamma (((12 - σ : ℝ) : ℂ) + t * I)‖ / ‖Complex.Gamma ((σ : ℂ) + t * I)‖)) ^ 2)
    (continuous_normsq_line (12 - σ)) (fun t => by positivity) (continuous_normsq_line σ)
    (α := 24 - 4 * σ) (by linarith) hA
    (fun t _ => by simp only; rw [norm_tauL_fe (by linarith) t]; ring)
    (tendsto_chi_sq hσ.le)
  rw [show (24 - 4 * σ + 1 : ℝ) = 25 - 4 * σ by ring] at h
  convert h using 2
  unfold Cleft RS
  ring

/-- The left-line limit is a positive finite constant (`τ(1) = 1`). -/
theorem summable_RS {β : ℝ} (hβ : 12 < β) :
    Summable fun n : ℕ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) := by
  have := RamanujanTau.MeanSquareFull.summable_mean_square_limit_full (σ := β / 2) (by linarith)
  simpa [show 2 * (β / 2) = β by ring] using this

end RamanujanTau.MeanSquareLeft
