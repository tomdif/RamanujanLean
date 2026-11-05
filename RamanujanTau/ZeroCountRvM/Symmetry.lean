/-
# The argument principle for `Λ(Δ,s)` reduced to the right half of the rectangle

`φ = Λ'/Λ` with `Λ = heckeLambda` (entire, `Λ(12−s) = Λ(s)`, `Λ(s̄) = \overline{Λ(s)}`), so
`φ(12−s) = −φ(s)` and `φ(s̄) = \overline{φ(s)}`.  On the rectangle `[12−σ₁, σ₁] × [0, T]`
(`σ₁ ≥ 7`, `Λ(x+iT) ≠ 0`; `Λ > 0` on the real axis):

  `π · Σ_{ρ inside} ord_ρ Λ = Re ∫₀ᵀ φ(σ₁+iy) dy − Im ∫₆^{σ₁} φ(x+iT) dx`   (`pi_count_eq`).
-/
import RamanujanTau.ZeroCountRvM.ArgPrinciple
import RamanujanTau.HeckeL.Positivity
import RamanujanTau.HeckeZeros.Main

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory
open RamanujanTau.HeckeL RamanujanTau.HeckeZeros
open scoped ComplexConjugate Real Interval

/-- `φ = Λ'/Λ`. -/
noncomputable def phi : ℂ → ℂ := logDeriv heckeLambda

lemma intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

lemma deriv_heckeLambda_twelve_sub (s : ℂ) :
    deriv heckeLambda (12 - s) = -deriv heckeLambda s := by
  have h1 : HasDerivAt (fun w => heckeLambda (12 - w)) (deriv heckeLambda (12 - s) * (-1)) s := by
    have := (heckeLambda_entire (12 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 12)
    simpa using this
  have h2 : (fun w => heckeLambda (12 - w)) = heckeLambda := funext heckeLambda_functional_equation
  rw [h2] at h1
  rw [h1.deriv]; ring

lemma deriv_heckeLambda_conj (s : ℂ) :
    deriv heckeLambda (conj s) = conj (deriv heckeLambda s) := by
  have h := (heckeLambda_entire s).hasDerivAt.conj_conj
  have h2 : (conj ∘ heckeLambda ∘ conj) = heckeLambda := by
    funext w; simp [Function.comp, heckeLambda_conj]
  rw [h2] at h; exact h.deriv

lemma phi_twelve_sub (s : ℂ) : phi (12 - s) = -phi s := by
  unfold phi
  rw [logDeriv_apply, logDeriv_apply, deriv_heckeLambda_twelve_sub,
    heckeLambda_functional_equation, neg_div]

lemma phi_conj (s : ℂ) : phi (conj s) = conj (phi s) := by
  unfold phi
  rw [logDeriv_apply, logDeriv_apply, deriv_heckeLambda_conj, heckeLambda_conj, map_div₀]

lemma continuous_deriv_heckeLambda : Continuous (deriv heckeLambda) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (heckeLambda_entire.analyticAt z).deriv.continuousAt

lemma continuousAt_phi {s : ℂ} (hs : heckeLambda s ≠ 0) : ContinuousAt phi s :=
  continuous_deriv_heckeLambda.continuousAt.div heckeLambda_entire.continuous.continuousAt hs

/-- **Symmetry reduction** of the rectangle integral. -/
theorem rectInt_phi_symm {σ₁ T : ℝ} (hσ : 6 ≤ σ₁)
    (hT : ∀ x : ℝ, heckeLambda (x + T * I) ≠ 0) :
    rectInt phi (12 - σ₁) σ₁ 0 T = 2 * I * ((((∫ y in (0 : ℝ)..T, phi (σ₁ + y * I)).re -
      (∫ x in (6 : ℝ)..σ₁, phi (x + T * I)).im : ℝ)) : ℂ) := by
  set V := ∫ y in (0 : ℝ)..T, phi (σ₁ + y * I)
  set H := ∫ x in (6 : ℝ)..σ₁, phi (x + T * I)
  have hcont : Continuous fun x : ℝ => phi (x + T * I) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ContinuousAt.comp (g := phi) (continuousAt_phi (hT x))
      (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x)
  -- bottom side vanishes
  have hbot : ∫ x in (12 - σ₁)..σ₁, phi (↑x + ↑(0 : ℝ) * I) = 0 := by
    simp only [ofReal_zero, zero_mul, add_zero]
    set J := ∫ x in (12 - σ₁)..σ₁, phi (x : ℂ)
    have h1 : ∫ x in (12 - σ₁)..σ₁, phi ((12 - x : ℝ) : ℂ) = J := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => phi (x : ℂ)) 12, sub_sub_cancel]
    have h2 : ∫ x in (12 - σ₁)..σ₁, phi ((12 - x : ℝ) : ℂ) = -J := by
      rw [← intervalIntegral.integral_neg]
      apply integral_congr; intro x _
      simp only []; push_cast; rw [phi_twelve_sub]
    have : J = -J := h1.symm.trans h2
    linear_combination this / 2
  -- left side
  have hleft : ∫ y in (0 : ℝ)..T, phi (↑(12 - σ₁) + ↑y * I) = -conj V := by
    rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply integral_congr; intro y _
    simp only []
    have : (↑(12 - σ₁) + ↑y * I : ℂ) = 12 - conj ((σ₁ : ℂ) + y * I) := by
      simp [map_add, conj_ofReal]; ring
    rw [this, phi_twelve_sub, phi_conj]
  -- top side
  have htop : ∫ x in (12 - σ₁)..σ₁, phi (↑x + ↑T * I) = H - conj H := by
    rw [← integral_add_adjacent_intervals (b := 6) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have h1 : ∫ x in (12 - σ₁)..6, phi (↑x + ↑T * I) =
        ∫ x in (12 - σ₁)..6, -conj (phi (((12 - x : ℝ) : ℂ) + T * I)) := by
      apply integral_congr; intro x _
      simp only []
      have : (↑x + ↑T * I : ℂ) = 12 - conj (((12 - x : ℝ) : ℂ) + T * I) := by
        simp [map_add, conj_ofReal, map_ofNat]; ring
      rw [this, phi_twelve_sub, phi_conj]
    have h2 : ∫ x in (12 - σ₁)..6, phi (((12 - x : ℝ) : ℂ) + T * I) = H := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => phi ((x : ℂ) + T * I)) 12]
      norm_num
      rfl
    rw [h1, intervalIntegral.integral_neg, intervalIntegral_conj, h2]
    ring
  unfold rectInt
  rw [hbot, hleft, htop]
  have hV : V + conj V = ((2 * V.re : ℝ) : ℂ) := add_conj V
  have hH : H - conj H = ((2 * H.im : ℝ) : ℂ) * I := sub_conj H
  simp only [smul_eq_mul]
  push_cast at hV hH ⊢
  linear_combination (-1 : ℂ) * hH + I * hV

/-- **Argument principle for `Λ`, right-half form.** -/
theorem pi_count_eq {σ₁ T : ℝ} (hσ : 7 ≤ σ₁) (hT0 : 0 < T)
    (hT : ∀ x : ℝ, heckeLambda (x + T * I) ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ u, u ∈ S ↔ (heckeLambda u = 0 ∧ 12 - σ₁ < u.re ∧ u.re < σ₁ ∧ 0 < u.im ∧ u.im < T)) ∧
      π * ((∑ u ∈ S, analyticOrderNatAt heckeLambda u : ℕ) : ℝ) =
        (∫ y in (0 : ℝ)..T, phi (σ₁ + y * I)).re - (∫ x in (6 : ℝ)..σ₁, phi (x + T * I)).im := by
  have hB : ∀ z ∈ rectBd (12 - σ₁) σ₁ 0 T, heckeLambda z ≠ 0 := by
    intro z hz
    rcases hz with ⟨_, h | h⟩ | ⟨_, h | h⟩
    · have hz : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
      rw [hz]; intro h0
      have := (heckeLambda_pos z.re).2
      rw [h0] at this; simp at this
    · have hz : z = (z.re : ℂ) + T * I := by apply Complex.ext <;> simp [h]
      rw [hz]; exact hT _
    · exact heckeLambda_ne_zero_of_lt (by rw [h]; linarith)
    · exact heckeLambda_ne_zero_of_gt (by rw [h]; linarith)
  obtain ⟨S, hS, hInt⟩ := arg_principle_rect heckeLambda_entire
    ⟨7, heckeLambda_ne_zero_of_gt (by norm_num)⟩ (by linarith : 12 - σ₁ < σ₁) hT0 hB
  refine ⟨S, hS, ?_⟩
  have hsym := rectInt_phi_symm (by linarith : (6 : ℝ) ≤ σ₁) hT
  have hphi : phi = logDeriv heckeLambda := rfl
  rw [← hphi, hsym] at hInt
  have hI : (2 * I : ℂ) ≠ 0 := by simp
  have h2 : ((((∫ y in (0 : ℝ)..T, phi (σ₁ + y * I)).re -
      (∫ x in (6 : ℝ)..σ₁, phi (x + T * I)).im : ℝ)) : ℂ) =
      ((π * ((∑ u ∈ S, analyticOrderNatAt heckeLambda u : ℕ) : ℝ) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hI
    rw [hInt]; push_cast; ring
  exact (Complex.ofReal_injective h2).symm

end RamanujanTau.ZeroCountRvM
