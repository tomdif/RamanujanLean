/-
# The shifted product AFE: `Z(u) Z(u')` with no root-number cross terms

Selberg's key lemma needs the *lag correlation* `Z(u) Z(u+v)` of Hardy's function.  The
residue machinery of `HeckeAFE3.Square` applies verbatim to `P(z) = Λ(a+z) Λ(b+z)` for any
`a, b`: Hecke's equation gives `P(−z) = Λ(12−a+z) Λ(12−b+z)`, so for every `c > 0`

    Λ(a) Λ(b) = I(a, b) + I(12−a, 12−b),    I(a,b) = (1/2πi) ∫_{(c)} Λ(a+z)Λ(b+z) e^{z²} dz/z
                                                                          (`heckeLambda_mul_afe`)

and `I(a,b) = Σ_{m,n} τ(m)τ(n)(2πm)^{−a}(2πn)^{−b} W(a,b; 4π²mn)` (`ISh_eq_tsum`).  On the line,
with `a = 6+iu`, `b = 6−iu'` (so `12−a = ā`, `12−b = b̄`, and `Λ(6−iu') = Λ(6+iu')`):

    Z(u) Z(u') = 2 Re[ U(u,u') Σ_{m,n} τ(m)τ(n) m^{−(6+iu)} n^{−(6−iu')} W̃_{u,u'}(4π²mn) ]
                                                                           (`ZH_mul_ZH_afe`)

with the unimodular phase `U(u,u') = (2π)^{i(u'−u)} Γ(6+iu)Γ(6−iu')/(|Γ(6+iu)||Γ(6+iu')|)`
`= e^{i(ϑ(u)−ϑ(u'))}` and `W̃ = W(a,b;·)/(Γ(a)Γ(b))`.  For `u = u'` this is `tauL_normSq_afe`.
Level 1 (axiom-clean, no hypotheses).
-/
import RamanujanTau.HeckeAFE3.Square
import RamanujanTau.HafnerProportion.Hardy

set_option autoImplicit false

namespace RamanujanTau.SelbergKey

open Complex MeasureTheory Set Filter Topology LSeries RamanujanTau.HeckeAFE RamanujanTau.HeckeL
open scoped Real ComplexConjugate

/-- `I(a,b) = (1/2π) ∫_ℝ Λ(a+z) Λ(b+z) e^{z²}/z dy`, `z = c+iy`. -/
noncomputable def ISh (a b : ℂ) (c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun z => heckeLambda (a + z) * heckeLambda (b + z) * cexp (z ^ 2) / z) c

/-- `W(a,b;ξ) = (1/2π) ∫_ℝ Γ(a+z)Γ(b+z) ξ^{−z} e^{z²}/z dy`. -/
noncomputable def W2sh (a b : ℂ) (ξ c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun z => Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z) *
    cexp (z ^ 2) / z) c

/-- **Shifted product AFE for `Λ`** (exact, every `a, b ∈ ℂ`, every `c > 0`). -/
theorem heckeLambda_mul_afe (a b : ℂ) {c : ℝ} (hc : 0 < c) :
    heckeLambda a * heckeLambda b = ISh a b c + ISh (12 - a) (12 - b) c := by
  set F : ℂ → ℂ := fun z => heckeLambda (a + z) * heckeLambda (b + z) with hFdef
  set G : ℂ → ℂ := fun z => heckeLambda (12 - a + z) * heckeLambda (12 - b + z) with hGdef
  have hFd : DifferentiableOn ℂ F (strip (-c) c) :=
    ((heckeLambda_entire.comp ((differentiable_const _).add differentiable_id)).mul
      (heckeLambda_entire.comp ((differentiable_const _).add differentiable_id))).differentiableOn
  have hFb : ∃ M, ∀ z ∈ strip (-c) c, ‖F z‖ ≤ M := by
    obtain ⟨L1, hL1⟩ := heckeLambda_bdd_strip (a.re - c) (a.re + c)
    obtain ⟨L2, hL2⟩ := heckeLambda_bdd_strip (b.re - c) (b.re + c)
    refine ⟨L1 * L2, fun z hz => ?_⟩
    simp only [hFdef]; rw [norm_mul]
    have h1 := hL1 (a + z) (by simp; linarith [hz.1]) (by simp; linarith [hz.2])
    have h2 := hL2 (b + z) (by simp; linarith [hz.1]) (by simp; linarith [hz.2])
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  have hres := vline_residue (by linarith : -c < 0) hc hFd hFb
  have hrefl : ∀ u, (fun z => F z * cexp (z ^ 2) / z) (-u) = -(fun z => G z * cexp (z ^ 2) / z) u := by
    intro u
    simp only [hFdef, hGdef]
    have h1 : heckeLambda (a + -u) = heckeLambda (12 - a + u) := by
      rw [← heckeLambda_functional_equation (a + -u)]; congr 1; ring
    have h2 : heckeLambda (b + -u) = heckeLambda (12 - b + u) := by
      rw [← heckeLambda_functional_equation (b + -u)]; congr 1; ring
    rw [h1, h2, neg_sq, div_neg]
  have hneg := vline_neg_eq (g := fun z => F z * cexp (z ^ 2) / z)
    (h := fun z => G z * cexp (z ^ 2) / z) hrefl c
  have hF0 : F 0 = heckeLambda a * heckeLambda b := by simp only [hFdef, add_zero]
  rw [hneg, sub_neg_eq_add, hF0] at hres
  unfold ISh
  have h2pi : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have e1 : (fun z => heckeLambda (a + z) * heckeLambda (b + z) * cexp (z ^ 2) / z) =
      (fun z => F z * cexp (z ^ 2) / z) := rfl
  have e2 : (fun z => heckeLambda (12 - a + z) * heckeLambda (12 - b + z) * cexp (z ^ 2) / z) =
      (fun z => G z * cexp (z ^ 2) / z) := rfl
  rw [e1, e2, ← mul_add, hres]
  field_simp

/-- `I(ā, b̄) = conj I(a, b)`. -/
theorem ISh_conj (a b : ℂ) (c : ℝ) : ISh (conj a) (conj b) c = conj (ISh a b c) := by
  unfold ISh vline
  rw [map_mul, ← integral_conj]
  have h2 : conj ((2 * π : ℂ)⁻¹) = (2 * π : ℂ)⁻¹ := by
    rw [map_inv₀, map_mul, Complex.conj_ofReal, map_ofNat]
  rw [h2]
  congr 1
  rw [← integral_neg_eq_self]
  congr 1; ext y
  have hz : conj ((c : ℂ) + y * I) = (c : ℂ) + ((-y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [map_div₀, map_mul, map_mul, ← Complex.exp_conj, map_pow,
    ← RamanujanTau.HeckeZeros.heckeLambda_conj, ← RamanujanTau.HeckeZeros.heckeLambda_conj,
    map_add (starRingEnd ℂ) a, map_add (starRingEnd ℂ) b, hz]

/-! ## The double Dirichlet expansion -/

lemma power_key_sh {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (a b z : ℂ) :
    (2 * π : ℂ) ^ (-(a + z)) * ((m : ℂ) ^ (a + z))⁻¹ *
        ((2 * π : ℂ) ^ (-(b + z)) * ((n : ℂ) ^ (b + z))⁻¹) =
      ((2 * π * m : ℝ) : ℂ) ^ (-a) * ((2 * π * n : ℝ) : ℂ) ^ (-b) *
        ((4 * π ^ 2 * m * n : ℝ) : ℂ) ^ (-z) := by
  have h2 : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hp : (0:ℝ) < 2 * π := by positivity
  rw [h2, cpow_ofReal_pos hp, cpow_ofReal_pos hm, cpow_ofReal_pos hp, cpow_ofReal_pos hn,
    cpow_ofReal_pos (by positivity), cpow_ofReal_pos (by positivity),
    cpow_ofReal_pos (by positivity), ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  have hl : Real.log ((2 * π) * (2 * π) * m * n) =
      Real.log (2 * π) + Real.log (2 * π) + Real.log m + Real.log n := by
    rw [Real.log_mul (x := (2 * π) * (2 * π) * m) (by positivity) hn.ne',
      Real.log_mul (x := (2 * π) * (2 * π)) (by positivity) hm.ne', Real.log_mul hp.ne' hp.ne']
  rw [show (4 * π ^ 2 * m * n : ℝ) = (2 * π) * (2 * π) * m * n by ring, hl,
    Real.log_mul hp.ne' hm.ne', Real.log_mul hp.ne' hn.ne']
  push_cast; ring

lemma norm_W2sh_integrand_le {a b : ℂ} {c ξ : ℝ} (hc : 0 < c) (h1 : 0 < a.re + c)
    (h2 : 0 < b.re + c) (hξ : 0 < ξ) (y : ℝ) :
    ‖Gamma (a + ((c : ℂ) + y * I)) * Gamma (b + ((c : ℂ) + y * I)) *
        (ξ : ℂ) ^ (-((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)‖ ≤
      Real.Gamma (a.re + c) * Real.Gamma (b.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) *
        Real.exp (-1 * y ^ 2) := by
  have hw1 : 0 < (a + ((c : ℂ) + y * I)).re := by simpa using h1
  have hw2 : 0 < (b + ((c : ℂ) + y * I)).re := by simpa using h2
  have hG1 := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw1
  have hG2 := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw2
  have hre1 : (a + ((c : ℂ) + y * I)).re = a.re + c := by simp
  have hre2 : (b + ((c : ℂ) + y * I)).re = b.re + c := by simp
  rw [hre1] at hG1; rw [hre2] at hG2
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
  have hr : (-((c : ℂ) + y * I)).re = -c := by simp
  rw [hr]
  have he : Real.exp (c ^ 2 - y ^ 2) = Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hi := norm_inv_line_le hc y
  have hG10 : 0 ≤ Real.Gamma (a.re + c) := (Real.Gamma_pos_of_pos h1).le
  calc ‖Gamma (a + (↑c + ↑y * I))‖ * ‖Gamma (b + (↑c + ↑y * I))‖ * ξ ^ (-c) *
        (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((c : ℂ) + y * I)⁻¹‖
      ≤ Real.Gamma (a.re + c) * Real.Gamma (b.re + c) * ξ ^ (-c) *
        (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) * c⁻¹ := by gcongr
    _ = _ := by ring

lemma integrable_W2sh_integrand {a b : ℂ} {c ξ : ℝ} (hc : 0 < c) (h1 : 0 < a.re + c)
    (h2 : 0 < b.re + c) (hξ : 0 < ξ) :
    Integrable (fun y : ℝ => Gamma (a + ((c : ℂ) + y * I)) * Gamma (b + ((c : ℂ) + y * I)) *
        (ξ : ℂ) ^ (-((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have hcont : Continuous (fun y : ℝ => Gamma (a + ((c : ℂ) + y * I)) *
      Gamma (b + ((c : ℂ) + y * I)) * (ξ : ℂ) ^ (-((c : ℂ) + y * I)) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
    refine Continuous.div ?_ (continuous_line c) (line_ne_zero hc.ne')
    refine (((continuous_Gamma_line h1).mul (continuous_Gamma_line h2)).mul ?_).mul (by fun_prop)
    exact continuous_iff_continuousAt.2 fun y =>
      ((continuousAt_const_cpow hξ0).comp (by fun_prop : Continuous fun y : ℝ =>
        -((c : ℂ) + y * I)).continuousAt)
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
    (Real.Gamma (a.re + c) * Real.Gamma (b.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  exact norm_W2sh_integrand_le hc h1 h2 hξ y

lemma norm_fsh_le {a b : ℂ} {c : ℝ} (hc : 0 < c) (h1 : 0 < a.re + c) (h2 : 0 < b.re + c)
    {m n : ℕ} (hm : (0:ℝ) < m) (hn : (0:ℝ) < n) (y : ℝ) :
    ‖tauC m * tauC n * ((2 * π * m : ℝ) : ℂ) ^ (-a) * ((2 * π * n : ℝ) : ℂ) ^ (-b) *
      (Gamma (a + ((c : ℂ) + y * I)) * Gamma (b + ((c : ℂ) + y * I)) *
        ((4 * π ^ 2 * m * n : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) *
        cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I))‖ ≤
      |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-a.re) * (2 * π * n) ^ (-b.re) *
        (Real.Gamma (a.re + c) * Real.Gamma (b.re + c) * (4 * π ^ 2 * m * n) ^ (-c) *
          (Real.exp (c ^ 2) * c⁻¹) * Real.exp (-1 * y ^ 2)) := by
  have hτm : ‖tauC m‖ = |(tau m : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have hτn : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have e1 : ‖((2 * π * m : ℝ) : ℂ) ^ (-a)‖ = (2 * π * m) ^ (-a.re) := by
    rw [norm_ofReal_cpow (by positivity)]; simp
  have e2 : ‖((2 * π * n : ℝ) : ℂ) ^ (-b)‖ = (2 * π * n) ^ (-b.re) := by
    rw [norm_ofReal_cpow (by positivity)]; simp
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hτm, hτn, e1, e2]
  have hW := norm_W2sh_integrand_le hc h1 h2 (ξ := 4 * π ^ 2 * m * n) (by positivity) y
  have h0 : 0 ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-a.re) * (2 * π * n) ^ (-b.re) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul_of_nonneg_left hW h0

set_option maxHeartbeats 1000000 in
/-- **Double Dirichlet expansion of `I(a,b)`** (`Re a + c > 7`, `Re b + c > 7`). -/
theorem ISh_eq_tsum {a b : ℂ} {c : ℝ} (hc : 0 < c) (hs1 : 7 < a.re + c) (hs2 : 7 < b.re + c) :
    ISh a b c = ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 * ((2 * π * p.1 : ℝ) : ℂ) ^ (-a) *
      ((2 * π * p.2 : ℝ) : ℂ) ^ (-b) * W2sh a b (4 * π ^ 2 * p.1 * p.2) c := by
  set f : ℕ × ℕ → ℝ → ℂ := fun p y => tauC p.1 * tauC p.2 * ((2 * π * p.1 : ℝ) : ℂ) ^ (-a) *
    ((2 * π * p.2 : ℝ) : ℂ) ^ (-b) *
    (Gamma (a + ((c : ℂ) + y * I)) * Gamma (b + ((c : ℂ) + y * I)) *
      ((4 * π ^ 2 * p.1 * p.2 : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) with hfdef
  have h1 : 0 < a.re + c := by linarith
  have h2 : 0 < b.re + c := by linarith
  have hpt : ∀ y : ℝ, heckeLambda (a + ((c : ℂ) + y * I)) *
      heckeLambda (b + ((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) /
        ((c : ℂ) + y * I) = ∑' p, f p y := by
    intro y
    set z : ℂ := (c : ℂ) + y * I
    have hw1 : 7 < (a + z).re := by simpa [z] using hs1
    have hw2 : 7 < (b + z).re := by simpa [z] using hs2
    rw [heckeLambda_eq hw1, heckeLambda_eq hw2, LSeries, LSeries]
    rw [show (2 * π : ℂ) ^ (-(a + z)) * Gamma (a + z) * (∑' n, term tauC (a + z) n) *
        ((2 * π : ℂ) ^ (-(b + z)) * Gamma (b + z) * (∑' n, term tauC (b + z) n)) *
        cexp (z ^ 2) / z = ((∑' n, term tauC (a + z) n) * (∑' n, term tauC (b + z) n)) *
        ((2 * π : ℂ) ^ (-(a + z)) * Gamma (a + z) * ((2 * π : ℂ) ^ (-(b + z)) *
          Gamma (b + z)) * cexp (z ^ 2) / z) by ring]
    rw [tsum_mul_tsum_of_summable_norm (HeckeAFE3.summable_norm_term_tau hw1)
      (HeckeAFE3.summable_norm_term_tau hw2), ← tsum_mul_right]
    congr 1; ext p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hfdef, term, tauC_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, term, tauC_zero]
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hk := power_key_sh hmpos hnpos a b z
    simp only [hfdef, term, if_neg hm, if_neg hn]
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      div_eq_mul_inv (tauC m), div_eq_mul_inv (tauC n)]
    linear_combination (tauC m * tauC n * Gamma (a + z) * Gamma (b + z) * cexp (z ^ 2) / z) * hk
  have hint : ∀ p, Integrable (f p) := by
    intro p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [hfdef, tauC_zero, zero_mul]; exact integrable_zero _ _ _
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [hfdef, tauC_zero, zero_mul, mul_zero]; exact integrable_zero _ _ _
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact (integrable_W2sh_integrand hc h1 h2 (by positivity)).const_mul _
  set K : ℝ := Real.Gamma (a.re + c) * Real.Gamma (b.re + c) * (Real.exp (c ^ 2) * c⁻¹) *
    ∫ y : ℝ, Real.exp (-1 * y ^ 2)
  have hK0 : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos h1
    have := Real.Gamma_pos_of_pos h2
    have : 0 ≤ ∫ y : ℝ, Real.exp (-1 * y ^ 2) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set g1 : ℕ → ℝ := fun m => |(tau m : ℝ)| / (m : ℝ) ^ (a.re + c)
  set g2 : ℕ → ℝ := fun n => |(tau n : ℝ)| / (n : ℝ) ^ (b.re + c)
  have hbd : ∀ p : ℕ × ℕ, ∫ y, ‖f p y‖ ≤ ((2 * π) ^ (-a.re - b.re - 2 * c) * K) *
      (g1 p.1 * g2 p.2) := by
    intro p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hfdef, tauC_zero, g1, tau_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, tauC_zero, g2, tau_zero]
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hle : ∀ y, ‖f (m, n) y‖ ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-a.re) *
        (2 * π * n) ^ (-b.re) * (Real.Gamma (a.re + c) * Real.Gamma (b.re + c) *
          (4 * π ^ 2 * m * n) ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) * Real.exp (-1 * y ^ 2)) := by
      intro y
      exact norm_fsh_le hc h1 h2 hmpos hnpos y
    refine (integral_mono (hint _).norm ?_ hle).trans (le_of_eq ?_)
    · exact ((integrable_exp_neg_mul_sq one_pos).const_mul _).const_mul _
    · simp_rw [← mul_assoc]
      rw [integral_const_mul]
      have := HeckeAFE3.real_power_key2 (σ := a.re) (σ' := b.re) (c := c) hmpos hnpos
      calc _ = |(tau m : ℝ)| * |(tau n : ℝ)| * ((2 * π * m) ^ (-a.re) *
            (2 * π * n) ^ (-b.re) * (4 * π ^ 2 * m * n) ^ (-c)) * K := by
            simp only [K]; ring
        _ = _ := by rw [this]; simp only [g1, g2]; ring
  have hsum : Summable fun p => ∫ y, ‖f p y‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) hbd ?_
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg
      (RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by linarith))
      (RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by linarith))
      (fun m => by simp only [g1]; positivity) (fun n => by simp only [g2]; positivity)
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  unfold ISh vline
  simp_rw [hpt]
  rw [← hswap, ← tsum_mul_left]
  congr 1; ext p
  unfold W2sh vline
  simp only [hfdef]
  rw [integral_const_mul]
  ring

/-! ## The critical line: `Z(u) Z(u')` -/

/-- The unimodular phase `U(u,u') = (2π)^{i(u'−u)} Γ(6+iu)Γ(6−iu')/(|Γ(6+iu)||Γ(6+iu')|)`,
i.e. `e^{i(ϑ(u) − ϑ(u'))}` with `ϑ(u) = arg Γ(6+iu) − u log 2π`. -/
noncomputable def Ush (u u' : ℝ) : ℂ :=
  (2 * π : ℂ) ^ (((u' - u : ℝ) : ℂ) * I) * (Gamma (6 + u * I) * Gamma (6 - u' * I)) /
    ((‖Gamma (6 + u * I)‖ * ‖Gamma (6 + u' * I)‖ : ℝ) : ℂ)

/-- The normalized lag weight `W̃_{u,u'}(ξ) = W(6+iu, 6−iu'; ξ)/(Γ(6+iu)Γ(6−iu'))` (line `Re z = 2`). -/
noncomputable def Wsh (u u' ξ : ℝ) : ℂ :=
  W2sh (6 + u * I) (6 - u' * I) ξ 2 / (Gamma (6 + u * I) * Gamma (6 - u' * I))

lemma Gamma_six_sub_ne (u' : ℝ) : Gamma (6 - u' * I) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp)

lemma norm_Gamma_six_sub (u' : ℝ) : ‖Gamma (6 - u' * I)‖ = ‖Gamma (6 + u' * I)‖ := by
  have : (6 - u' * I : ℂ) = conj (6 + u' * I) := by apply Complex.ext <;> simp
  rw [this, Gamma_conj, Complex.norm_conj]

/-- `|U(u,u')| = 1`. -/
theorem norm_Ush (u u' : ℝ) : ‖Ush u u'‖ = 1 := by
  unfold Ush
  have hp : (0:ℝ) < 2 * π := by positivity
  have h2r : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hG1 : 0 < ‖Gamma (6 + u * I)‖ := norm_pos_iff.mpr (HafnerProportion.Gamma_line_ne_zero u)
  have hG2 : 0 < ‖Gamma (6 + u' * I)‖ := norm_pos_iff.mpr (HafnerProportion.Gamma_line_ne_zero u')
  rw [norm_div, norm_mul, norm_mul, h2r, norm_ofReal_cpow hp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), norm_Gamma_six_sub]
  have : ((((u' - u : ℝ) : ℂ) * I)).re = 0 := by simp
  rw [this, Real.rpow_zero, one_mul]
  exact div_self (mul_pos hG1 hG2).ne'

/-- **Lag AFE for Hardy's `Z`** (exact, no root-number cross terms):
`Z(u)Z(u') = 2 Re[U(u,u') Σ_{m,n} τ(m)τ(n) m^{−(6+iu)} n^{−(6−iu')} W̃_{u,u'}(4π²mn)]`. -/
theorem ZH_mul_ZH_afe (u u' : ℝ) :
    HafnerProportion.ZH u * HafnerProportion.ZH u' = 2 * (Ush u u' * ∑' p : ℕ × ℕ,
      tauC p.1 * tauC p.2 * (p.1 : ℂ) ^ (-(6 + u * I)) * (p.2 : ℂ) ^ (-(6 - u' * I)) *
        Wsh u u' (4 * π ^ 2 * p.1 * p.2)).re := by
  set a : ℂ := 6 + u * I with ha
  set b : ℂ := 6 - u' * I with hb
  have hare : a.re = 6 := by simp [ha]
  have hbre : b.re = 6 := by simp [hb]
  have hGa : Gamma a ≠ 0 := HafnerProportion.Gamma_line_ne_zero u
  have hGb : Gamma b ≠ 0 := Gamma_six_sub_ne u'
  have hp : (0:ℝ) < 2 * π := by positivity
  have h2 : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have h2r : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  -- `Λ(6+iu') = Λ(6−iu')`, and both `Λ` values on the line are real
  have hLb : heckeLambda b = (RamanujanTau.HardyZeros.Zr u' : ℂ) := by
    rw [← RamanujanTau.HardyZeros.Zc_eq_Zr, RamanujanTau.HardyZeros.Zc,
      ← heckeLambda_functional_equation b]
    congr 1; rw [hb]; ring
  have hLa : heckeLambda a = (RamanujanTau.HardyZeros.Zr u : ℂ) := by
    rw [← RamanujanTau.HardyZeros.Zc_eq_Zr, RamanujanTau.HardyZeros.Zc]
  have hca : 12 - a = conj a := by apply Complex.ext <;> simp [ha]; norm_num
  have hcb : 12 - b = conj b := by apply Complex.ext <;> simp [hb]; norm_num
  -- the series
  set S : ℂ := ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 * (p.1 : ℂ) ^ (-a) * (p.2 : ℂ) ^ (-b) *
    Wsh u u' (4 * π ^ 2 * p.1 * p.2) with hS
  have hISh : ISh a b 2 = (2 * π : ℂ) ^ (-(a + b)) * (Gamma a * Gamma b) * S := by
    rw [ISh_eq_tsum (by norm_num) (by rw [hare]; norm_num) (by rw [hbre]; norm_num), hS,
      ← tsum_mul_left]
    congr 1; ext p
    obtain ⟨m, n⟩ := p
    have e : ((2 * π * m : ℝ) : ℂ) ^ (-a) * ((2 * π * n : ℝ) : ℂ) ^ (-b) =
        (2 * π : ℂ) ^ (-(a + b)) * ((m : ℂ) ^ (-a) * (n : ℂ) ^ (-b)) := by
      rw [show ((2 * π * m : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) * ((m : ℝ) : ℂ) by push_cast; ring,
        show ((2 * π * n : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) * ((n : ℝ) : ℂ) by push_cast; ring,
        mul_cpow_ofReal_nonneg hp.le (Nat.cast_nonneg _),
        mul_cpow_ofReal_nonneg hp.le (Nat.cast_nonneg _), ← h2r,
        show (-(a + b)) = -a + -b by ring, cpow_add _ _ h2]
      push_cast; ring
    unfold Wsh
    rw [← ha, ← hb]
    dsimp only
    rw [mul_assoc (tauC m * tauC n), e]
    field_simp
  have hprod : heckeLambda a * heckeLambda b = ISh a b 2 + conj (ISh a b 2) := by
    rw [heckeLambda_mul_afe a b (by norm_num : (0:ℝ) < 2), hca, hcb, ISh_conj]
  have hZZ : ((HafnerProportion.ZH u * HafnerProportion.ZH u' : ℝ) : ℂ) =
      ((2 * π) ^ (12 : ℕ) / (‖Gamma a‖ * ‖Gamma (6 + u' * I)‖) : ℝ) *
        (ISh a b 2 + conj (ISh a b 2)) := by
    rw [← hprod, hLa, hLb]
    unfold HafnerProportion.ZH
    push_cast
    ring
  have hUS : ((2 * π) ^ (12 : ℕ) / (‖Gamma a‖ * ‖Gamma (6 + u' * I)‖) : ℝ) * ISh a b 2 =
      Ush u u' * S := by
    rw [hISh]
    unfold Ush
    rw [← ha, ← hb]
    have hG1 : (‖Gamma a‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr hGa).ne'
    have hG2 : (‖Gamma (6 + u' * I)‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr (HafnerProportion.Gamma_line_ne_zero u')).ne'
    have hpow : (2 * π : ℂ) ^ (((u' - u : ℝ) : ℂ) * I) =
        ((2 * π : ℝ) : ℂ) ^ (12 : ℕ) * (2 * π : ℂ) ^ (-(a + b)) := by
      rw [← h2r, ← cpow_natCast, ← cpow_add _ _ h2]
      congr 1; rw [ha, hb]; push_cast; ring
    rw [hpow]
    push_cast
    field_simp
  have hre : ((HafnerProportion.ZH u * HafnerProportion.ZH u' : ℝ) : ℂ) =
      ((2 * (Ush u u' * S).re : ℝ) : ℂ) := by
    rw [hZZ, mul_add]
    have hc : ((2 * π) ^ (12 : ℕ) / (‖Gamma a‖ * ‖Gamma (6 + u' * I)‖) : ℝ) * conj (ISh a b 2) =
        conj (((2 * π) ^ (12 : ℕ) / (‖Gamma a‖ * ‖Gamma (6 + u' * I)‖) : ℝ) * ISh a b 2) := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hc, hUS, Complex.add_conj]
  exact_mod_cast hre

end RamanujanTau.SelbergKey
