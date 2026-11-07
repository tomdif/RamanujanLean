/-
# From the Rankin–Selberg functional equation to a power-saving error term

Input (`RSData a κ`): an entire `Λ₀`, bounded on `−3/2 ≤ Re s ≤ 5/2`, with `Λ₀(1−s) = Λ₀(s)`, and

    γ(s) ζ(2s) D(s) = Λ₀(s) + κ (1/(s−1) − 1/s)       (Re s > 2),
    γ(s) = 2 π^{−s} Γ(s) Γ(s+11) (4π)^{−s−11},  D(s) = ∑ aₙ n^{−s}.

For `aₙ = τ(n)²/n¹¹` this is the Rankin–Selberg unfolding of `|Δ|²y¹² E*(z,s)` (`κ = ‖Δ‖²`).

Output (`power_saving_of_RSData`): `∑_{n≤N} aₙ = c₀N + O(N^{1−δ})`, `δ = 2^{−22}`,
`c₀ = 3 κ (4π)¹² / (π · 11!)`.

Route: Phragmén–Lindelöf (Mathlib `PhragmenLindelof.vertical_strip`) on the strip
`[−3/2, 5/2]` for `f(s) = (s(s−1)Λ₀(s) + κ)/(γ(s)(s+3)¹⁹)`, bounded on both edges by the
functional equation and an exact `Γ`-ratio computation; this gives `D(s) − c₀/(s−1)`
polynomially bounded on `3/4 ≤ Re s ≤ 5/2`; then `rieszAsymp_of_continuation` and
`riesz_descend`.
-/
import RamanujanTau.RankinError.PerronShift
import RamanujanTau.RankinError.GammaBound

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

/-- The gamma factor `γ(s) = 2 π^{−s} Γ(s) Γ(s+11) (4π)^{−s−11}`. -/
noncomputable def gam (s : ℂ) : ℂ :=
  2 * (π : ℂ) ^ (-s) * Complex.Gamma s * Complex.Gamma (s + 11) * ((4 * π : ℝ) : ℂ) ^ (-s - 11)

/-- Its reciprocal, an entire function. -/
noncomputable def invGam (s : ℂ) : ℂ :=
  (π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + 11) / 2 * (Complex.Gamma s)⁻¹ *
    (Complex.Gamma (s + 11))⁻¹

/-- The Rankin–Selberg data: continuation, functional equation, and the unfolding identity. -/
structure RSData (a : ℕ → ℝ) (κ : ℝ) where
  Λ₀ : ℂ → ℂ
  diff : Differentiable ℂ Λ₀
  L₀ : ℝ
  bdd : ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖Λ₀ s‖ ≤ L₀
  fe : ∀ s : ℂ, Λ₀ (1 - s) = Λ₀ s
  unfold : ∀ s : ℂ, 2 < s.re →
    gam s * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s = Λ₀ s + κ * (1 / (s - 1) - 1 / s)

lemma pi_ne_zero' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
lemma fourpi_ne_zero : ((4 * π : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)

lemma differentiable_invGam : Differentiable ℂ invGam := by
  intro s
  have h3 : DifferentiableAt ℂ (fun s => (Complex.Gamma s)⁻¹) s := by
    simpa using Complex.differentiable_one_div_Gamma s
  have h4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + 11))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + 11)).comp s
      (differentiableAt_id.add_const (11 : ℂ))
    simpa [Function.comp_def] using this
  unfold invGam
  exact ((((differentiableAt_id.const_cpow (Or.inl pi_ne_zero')).mul
    ((differentiableAt_id.add_const _).const_cpow (Or.inl fourpi_ne_zero))).div_const 2).mul
    h3).mul h4

lemma gam_mul_invGam {s : ℂ} (hs : 0 < s.re) : gam s * invGam s = 1 := by
  have hG1 := Complex.Gamma_ne_zero_of_re_pos hs
  have hG2 := Complex.Gamma_ne_zero_of_re_pos (s := s + 11) (by simp; linarith)
  unfold gam invGam
  have e1 : (π : ℂ) ^ (-s) * (π : ℂ) ^ s = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.2 (Or.inl pi_ne_zero'))]
  have e2 : ((4 * π : ℝ) : ℂ) ^ (-s - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11) = 1 := by
    rw [show -s - 11 = -(s + 11) by ring, cpow_neg,
      inv_mul_cancel₀ (cpow_ne_zero_iff.2 (Or.inl fourpi_ne_zero))]
  calc _ = ((π : ℂ) ^ (-s) * (π : ℂ) ^ s) *
        (((4 * π : ℝ) : ℂ) ^ (-s - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) *
        (Complex.Gamma (s + 11) * (Complex.Gamma (s + 11))⁻¹) := by ring
    _ = 1 := by rw [e1, e2, mul_inv_cancel₀ hG1, mul_inv_cancel₀ hG2]; ring

lemma norm_cpow_pos (b : ℝ) (hb : 0 < b) (s : ℂ) : ‖(b : ℂ) ^ s‖ = b ^ s.re :=
  norm_cpow_eq_rpow_re_of_pos hb s

/-- `‖LSeries f s‖ ≤ ∑ ‖term f σ n‖` for `Re s ≥ σ`. -/
lemma norm_LSeries_le {f : ℕ → ℂ} {σ : ℝ} (hσ : LSeriesSummable f σ) {s : ℂ} (h : σ ≤ s.re) :
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f σ n‖ := by
  have hs : LSeriesSummable f s := hσ.of_re_le_re (by simpa using h)
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  exact hs.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f (by simpa using h) n)
    hσ.norm

/-- `‖1/ζ(w)‖ ≤ Z` for `Re w ≥ 3/2`. -/
lemma exists_norm_inv_zeta_le : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ w : ℂ, 3 / 2 ≤ w.re → ‖(riemannZeta w)⁻¹‖ ≤ Z := by
  have hμ : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by simp; norm_num)
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun w hw => ?_⟩
  have hw1 : 1 < w.re := by linarith
  have := LSeries_one_mul_Lseries_moebius hw1
  rw [LSeries_one_eq_riemannZeta hw1] at this
  rw [inv_eq_of_mul_eq_one_right this]
  exact norm_LSeries_le hμ (by simpa using hw)

lemma exists_norm_zeta_le : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ w : ℂ, 5 ≤ w.re → ‖riemannZeta w‖ ≤ Z := by
  have h1 : LSeriesSummable 1 ((5 : ℝ) : ℂ) := LSeriesSummable_one_iff.2 (by simp)
  refine ⟨∑' n, ‖LSeries.term 1 ((5 : ℝ) : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _,
    fun w hw => ?_⟩
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  exact norm_LSeries_le h1 (by simpa using hw)

end RamanujanTau.RankinError
