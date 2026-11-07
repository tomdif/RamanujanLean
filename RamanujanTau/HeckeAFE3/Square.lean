/-
# The approximate functional equation for `|L(Δ, 6+it)|²` (no root-number cross terms)

Apply the residue machinery to the *even* function `P(z) = Λ(s+z) Λ(12−s+z)`
(`P(−z) = P(z)` by Hecke's equation twice).  Then for every `s ∈ ℂ` and `c > 0`

    Λ(s)² = 2 · (1/2πi) ∫_{(c)} Λ(s+z) Λ(12−s+z) e^{z²} dz/z          (`heckeLambda_sq_afe`)

and, expanding both Dirichlet series (`Re s + c > 7`, `12 − Re s + c > 7`),

    Λ(s)² = 2 Σ_{m,n} τ(m)τ(n) (2πm)^{−s} (2πn)^{−(12−s)} W²_s(4π²mn)     (`heckeLambda_sq_eq_tsum`)

with `W²_s(ξ) = (1/2πi)∫_{(c)} Γ(s+z)Γ(12−s+z) ξ^{−z} e^{z²} dz/z`.  On the critical line
(`tauL_normSq_afe`):

    |L(Δ,6+it)|² = 2 Σ_{m,n} τ(m)τ(n) m^{−6−it} n^{−6+it} W_t(4π²mn),
    W_t = W²_{6+it} / (Γ(6+it)Γ(6−it)),

i.e. `|L|² = 2 Σ λ(m)λ(n)(mn)^{−1/2}(n/m)^{it} W_t(4π²mn)` — the mean value reduces to a diagonal
plus shifted sums `m ≠ n`, with **no** `ε(t)` cross terms.
-/
import RamanujanTau.HeckeAFE3.DerivJ
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE3

open Complex MeasureTheory Set Filter Topology LSeries RamanujanTau.HeckeAFE RamanujanTau.HeckeL
open scoped Real ComplexConjugate

/-- `I²(s) = (1/2π) ∫_ℝ Λ(s+z) Λ(12−s+z) e^{z²}/z dy`, `z = c+iy`. -/
noncomputable def ISq (s : ℂ) (c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun z => heckeLambda (s + z) * heckeLambda (12 - s + z) * cexp (z ^ 2) / z) c

/-- `W²_s(ξ) = (1/2π) ∫_ℝ Γ(s+z)Γ(12−s+z) ξ^{−z} e^{z²}/z dy`. -/
noncomputable def W2 (s : ℂ) (ξ c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun z => Gamma (s + z) * Gamma (12 - s + z) * (ξ : ℂ) ^ (-z) *
    cexp (z ^ 2) / z) c

/-- **AFE for `Λ(s)²`** (exact, every `s`, every `c > 0`). -/
theorem heckeLambda_sq_afe (s : ℂ) {c : ℝ} (hc : 0 < c) : heckeLambda s ^ 2 = 2 * ISq s c := by
  set F : ℂ → ℂ := fun z => heckeLambda (s + z) * heckeLambda (12 - s + z) with hFdef
  have hFd : DifferentiableOn ℂ F (strip (-c) c) :=
    ((heckeLambda_entire.comp ((differentiable_const _).add differentiable_id)).mul
      (heckeLambda_entire.comp ((differentiable_const _).add differentiable_id))).differentiableOn
  have hFb : ∃ M, ∀ z ∈ strip (-c) c, ‖F z‖ ≤ M := by
    obtain ⟨L1, hL1⟩ := heckeLambda_bdd_strip (s.re - c) (s.re + c)
    obtain ⟨L2, hL2⟩ := heckeLambda_bdd_strip (12 - s.re - c) (12 - s.re + c)
    refine ⟨L1 * L2, fun z hz => ?_⟩
    simp only [hFdef]; rw [norm_mul]
    have h1 := hL1 (s + z) (by simp; linarith [hz.1]) (by simp; linarith [hz.2])
    have h2 := hL2 (12 - s + z) (by simp; linarith [hz.1]) (by simp; linarith [hz.2])
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  have hres := vline_residue (by linarith : -c < 0) hc hFd hFb
  have hodd : ∀ z, (fun z => F z * cexp (z ^ 2) / z) (-z) = -(fun z => F z * cexp (z ^ 2) / z) z := by
    intro z
    simp only [hFdef]
    have h1 : heckeLambda (s + -z) = heckeLambda (12 - s + z) := by
      rw [← heckeLambda_functional_equation (s + -z)]; congr 1; ring
    have h2 : heckeLambda (12 - s + -z) = heckeLambda (s + z) := by
      rw [← heckeLambda_functional_equation (12 - s + -z)]; congr 1; ring
    rw [h1, h2, neg_sq, div_neg]; ring
  have hneg := vline_neg_of_odd (g := fun z => F z * cexp (z ^ 2) / z) hodd c
  have hF0 : F 0 = heckeLambda s ^ 2 := by
    simp only [hFdef, add_zero]
    rw [heckeLambda_functional_equation, sq]
  rw [hneg, sub_neg_eq_add, hF0] at hres
  unfold ISq
  have h2pi : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have e : (fun z => heckeLambda (s + z) * heckeLambda (12 - s + z) * cexp (z ^ 2) / z) =
      (fun z => F z * cexp (z ^ 2) / z) := rfl
  rw [e]
  have hv : vline (fun z => F z * cexp (z ^ 2) / z) c = π * heckeLambda s ^ 2 := by
    linear_combination hres / 2
  rw [hv]
  field_simp

/-! ## The double Dirichlet expansion -/

lemma power_key2 {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (s z : ℂ) :
    (2 * π : ℂ) ^ (-(s + z)) * ((m : ℂ) ^ (s + z))⁻¹ *
        ((2 * π : ℂ) ^ (-(12 - s + z)) * ((n : ℂ) ^ (12 - s + z))⁻¹) =
      ((2 * π * m : ℝ) : ℂ) ^ (-s) * ((2 * π * n : ℝ) : ℂ) ^ (-(12 - s)) *
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

lemma real_power_key2 {m n σ σ' c : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (2 * π * m) ^ (-σ) * (2 * π * n) ^ (-σ') * (4 * π ^ 2 * m * n) ^ (-c) =
      (2 * π) ^ (-σ - σ' - 2 * c) * (1 / m ^ (σ + c)) * (1 / n ^ (σ' + c)) := by
  have hp : (0:ℝ) < 2 * π := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos hn, one_div, one_div, ← Real.exp_neg, ← Real.exp_neg,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hl : Real.log ((2 * π) * (2 * π) * m * n) =
      Real.log (2 * π) + Real.log (2 * π) + Real.log m + Real.log n := by
    rw [Real.log_mul (x := (2 * π) * (2 * π) * m) (by positivity) hn.ne',
      Real.log_mul (x := (2 * π) * (2 * π)) (by positivity) hm.ne', Real.log_mul hp.ne' hp.ne']
  rw [show (4 * π ^ 2 * m * n : ℝ) = (2 * π) * (2 * π) * m * n by ring, hl,
    Real.log_mul hp.ne' hm.ne', Real.log_mul hp.ne' hn.ne']
  ring

lemma norm_W2_integrand_le {s : ℂ} {c ξ : ℝ} (hc : 0 < c) (h1 : 0 < s.re + c)
    (h2 : 0 < 12 - s.re + c) (hξ : 0 < ξ) (y : ℝ) :
    ‖Gamma (s + ((c : ℂ) + y * I)) * Gamma (12 - s + ((c : ℂ) + y * I)) *
        (ξ : ℂ) ^ (-((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)‖ ≤
      Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) *
        Real.exp (-1 * y ^ 2) := by
  have hw1 : 0 < (s + ((c : ℂ) + y * I)).re := by simpa using h1
  have hw2 : 0 < (12 - s + ((c : ℂ) + y * I)).re := by simp; linarith
  have hG1 := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw1
  have hG2 := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw2
  have hre1 : (s + ((c : ℂ) + y * I)).re = s.re + c := by simp
  have hre2 : (12 - s + ((c : ℂ) + y * I)).re = 12 - s.re + c := by simp
  rw [hre1] at hG1; rw [hre2] at hG2
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
  have hr : (-((c : ℂ) + y * I)).re = -c := by simp
  rw [hr]
  have he : Real.exp (c ^ 2 - y ^ 2) = Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hi := norm_inv_line_le hc y
  have hG10 : 0 ≤ Real.Gamma (s.re + c) := (Real.Gamma_pos_of_pos h1).le
  calc ‖Gamma (s + (↑c + ↑y * I))‖ * ‖Gamma (12 - s + (↑c + ↑y * I))‖ * ξ ^ (-c) *
        (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((c : ℂ) + y * I)⁻¹‖
      ≤ Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) * ξ ^ (-c) *
        (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) * c⁻¹ := by gcongr
    _ = _ := by ring

lemma integrable_W2_integrand {s : ℂ} {c ξ : ℝ} (hc : 0 < c) (h1 : 0 < s.re + c)
    (h2 : 0 < 12 - s.re + c) (hξ : 0 < ξ) :
    Integrable (fun y : ℝ => Gamma (s + ((c : ℂ) + y * I)) * Gamma (12 - s + ((c : ℂ) + y * I)) *
        (ξ : ℂ) ^ (-((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have hcont : Continuous (fun y : ℝ => Gamma (s + ((c : ℂ) + y * I)) *
      Gamma (12 - s + ((c : ℂ) + y * I)) * (ξ : ℂ) ^ (-((c : ℂ) + y * I)) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
    refine Continuous.div ?_ (continuous_line c) (line_ne_zero hc.ne')
    refine (((continuous_Gamma_line h1).mul (continuous_Gamma_line (s := 12 - s)
      (by simp; linarith))).mul ?_).mul (by fun_prop)
    exact continuous_iff_continuousAt.2 fun y =>
      ((continuousAt_const_cpow hξ0).comp (by fun_prop : Continuous fun y : ℝ =>
        -((c : ℂ) + y * I)).continuousAt)
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
    (Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  exact norm_W2_integrand_le hc h1 h2 hξ y

lemma summable_norm_term_tau {w : ℂ} (hw : 7 < w.re) : Summable fun n => ‖term tauC w n‖ :=
  summable_norm_iff.mpr (LSeriesSummable_tau hw)

lemma norm_f_le {s : ℂ} {c : ℝ} (hc : 0 < c) (h1 : 0 < s.re + c) (h2 : 0 < 12 - s.re + c)
    {m n : ℕ} (hm : (0:ℝ) < m) (hn : (0:ℝ) < n) (y : ℝ) :
    ‖tauC m * tauC n * ((2 * π * m : ℝ) : ℂ) ^ (-s) * ((2 * π * n : ℝ) : ℂ) ^ (-(12 - s)) *
      (Gamma (s + ((c : ℂ) + y * I)) * Gamma (12 - s + ((c : ℂ) + y * I)) *
        ((4 * π ^ 2 * m * n : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) *
        cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I))‖ ≤
      |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-s.re) * (2 * π * n) ^ (-(12 - s.re)) *
        (Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) * (4 * π ^ 2 * m * n) ^ (-c) *
          (Real.exp (c ^ 2) * c⁻¹) * Real.exp (-1 * y ^ 2)) := by
  have hτm : ‖tauC m‖ = |(tau m : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have hτn : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have e1 : ‖((2 * π * m : ℝ) : ℂ) ^ (-s)‖ = (2 * π * m) ^ (-s.re) := by
    rw [norm_ofReal_cpow (by positivity)]; simp
  have e2 : ‖((2 * π * n : ℝ) : ℂ) ^ (-(12 - s))‖ = (2 * π * n) ^ (-(12 - s.re)) := by
    rw [norm_ofReal_cpow (by positivity)]; simp
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hτm, hτn, e1, e2]
  have hW := norm_W2_integrand_le hc h1 h2 (ξ := 4 * π ^ 2 * m * n) (by positivity) y
  have h0 : 0 ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-s.re) * (2 * π * n) ^ (-(12 - s.re)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul_of_nonneg_left hW h0

set_option maxHeartbeats 1000000 in
/-- **Double Dirichlet expansion of `I²`**. -/
theorem ISq_eq_tsum {s : ℂ} {c : ℝ} (hc : 0 < c) (hs1 : 7 < s.re + c) (hs2 : 7 < 12 - s.re + c) :
    ISq s c = ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 * ((2 * π * p.1 : ℝ) : ℂ) ^ (-s) *
      ((2 * π * p.2 : ℝ) : ℂ) ^ (-(12 - s)) * W2 s (4 * π ^ 2 * p.1 * p.2) c := by
  set f : ℕ × ℕ → ℝ → ℂ := fun p y => tauC p.1 * tauC p.2 * ((2 * π * p.1 : ℝ) : ℂ) ^ (-s) *
    ((2 * π * p.2 : ℝ) : ℂ) ^ (-(12 - s)) *
    (Gamma (s + ((c : ℂ) + y * I)) * Gamma (12 - s + ((c : ℂ) + y * I)) *
      ((4 * π ^ 2 * p.1 * p.2 : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) with hfdef
  have h1 : 0 < s.re + c := by linarith
  have h2 : 0 < 12 - s.re + c := by linarith
  have hpt : ∀ y : ℝ, heckeLambda (s + ((c : ℂ) + y * I)) *
      heckeLambda (12 - s + ((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) /
        ((c : ℂ) + y * I) = ∑' p, f p y := by
    intro y
    set z : ℂ := (c : ℂ) + y * I
    have hw1 : 7 < (s + z).re := by simpa [z] using hs1
    have hw2 : 7 < (12 - s + z).re := by simp [z]; linarith
    rw [heckeLambda_eq hw1, heckeLambda_eq hw2, LSeries, LSeries]
    rw [show (2 * π : ℂ) ^ (-(s + z)) * Gamma (s + z) * (∑' n, term tauC (s + z) n) *
        ((2 * π : ℂ) ^ (-(12 - s + z)) * Gamma (12 - s + z) * (∑' n, term tauC (12 - s + z) n)) *
        cexp (z ^ 2) / z = ((∑' n, term tauC (s + z) n) * (∑' n, term tauC (12 - s + z) n)) *
        ((2 * π : ℂ) ^ (-(s + z)) * Gamma (s + z) * ((2 * π : ℂ) ^ (-(12 - s + z)) *
          Gamma (12 - s + z)) * cexp (z ^ 2) / z) by ring]
    rw [tsum_mul_tsum_of_summable_norm (summable_norm_term_tau hw1) (summable_norm_term_tau hw2),
      ← tsum_mul_right]
    congr 1; ext p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hfdef, term, tauC_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, term, tauC_zero]
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hk := power_key2 hmpos hnpos s z
    simp only [hfdef, term, if_neg hm, if_neg hn]
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      div_eq_mul_inv (tauC m), div_eq_mul_inv (tauC n)]
    linear_combination (tauC m * tauC n * Gamma (s + z) * Gamma (12 - s + z) * cexp (z ^ 2) / z) * hk
  have hint : ∀ p, Integrable (f p) := by
    intro p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [hfdef, tauC_zero, zero_mul]; exact integrable_zero _ _ _
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [hfdef, tauC_zero, zero_mul, mul_zero]; exact integrable_zero _ _ _
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact (integrable_W2_integrand hc h1 h2 (by positivity)).const_mul _
  set K : ℝ := Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) * (Real.exp (c ^ 2) * c⁻¹) *
    ∫ y : ℝ, Real.exp (-1 * y ^ 2)
  have hK0 : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos h1
    have := Real.Gamma_pos_of_pos h2
    have : 0 ≤ ∫ y : ℝ, Real.exp (-1 * y ^ 2) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set g1 : ℕ → ℝ := fun m => |(tau m : ℝ)| / (m : ℝ) ^ (s.re + c)
  set g2 : ℕ → ℝ := fun n => |(tau n : ℝ)| / (n : ℝ) ^ (12 - s.re + c)
  have hbd : ∀ p : ℕ × ℕ, ∫ y, ‖f p y‖ ≤ ((2 * π) ^ (-s.re - (12 - s.re) - 2 * c) * K) *
      (g1 p.1 * g2 p.2) := by
    intro p
    obtain ⟨m, n⟩ := p
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hfdef, tauC_zero, g1, tau_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, tauC_zero, g2, tau_zero]
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hξ : (0:ℝ) < 4 * π ^ 2 * m * n := by positivity
    have hle : ∀ y, ‖f (m, n) y‖ ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (2 * π * m) ^ (-s.re) *
        (2 * π * n) ^ (-(12 - s.re)) * (Real.Gamma (s.re + c) * Real.Gamma (12 - s.re + c) *
          (4 * π ^ 2 * m * n) ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) * Real.exp (-1 * y ^ 2)) := by
      intro y
      exact norm_f_le hc h1 h2 hmpos hnpos y
    refine (integral_mono (hint _).norm ?_ hle).trans (le_of_eq ?_)
    · exact ((integrable_exp_neg_mul_sq one_pos).const_mul _).const_mul _
    · simp_rw [← mul_assoc]
      rw [integral_const_mul]
      have := real_power_key2 (σ := s.re) (σ' := 12 - s.re) (c := c) hmpos hnpos
      calc _ = |(tau m : ℝ)| * |(tau n : ℝ)| * ((2 * π * m) ^ (-s.re) *
            (2 * π * n) ^ (-(12 - s.re)) * (4 * π ^ 2 * m * n) ^ (-c)) * K := by
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
  unfold ISq vline
  simp_rw [hpt]
  rw [← hswap, ← tsum_mul_left]
  congr 1; ext p
  unfold W2 vline
  simp only [hfdef]
  rw [integral_const_mul]
  ring

/-! ## The critical line -/

lemma tauL_conj (s : ℂ) : tauL (conj s) = conj (tauL s) := by
  unfold tauL
  rw [map_mul, map_mul, ← RamanujanTau.HeckeZeros.heckeLambda_conj, map_inv₀, ← Gamma_conj]
  congr 2
  have h2 : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [h2, cpow_conj _ _ (by rw [arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm),
    conj_ofReal]

/-- the normalized `|L|²` weight `W_t(ξ) = W²_{6+it}(ξ)/(Γ(6+it)Γ(6−it))` (line `Re z = 2`). -/
noncomputable def Wsq (t ξ : ℝ) : ℂ :=
  W2 (6 + t * I) ξ 2 / (Gamma (6 + t * I) * Gamma (12 - (6 + t * I)))

/-- **AFE for `|L(Δ, 6+it)|²`** (exact, no root-number cross terms):
`|L(6+it)|² = 2 Σ_{m,n} τ(m)τ(n) m^{−(6+it)} n^{−(6−it)} W_t(4π²mn)`. -/
theorem tauL_normSq_afe (t : ℝ) :
    ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) = 2 * ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 *
      (p.1 : ℂ) ^ (-(6 + t * I)) * (p.2 : ℂ) ^ (-(12 - (6 + t * I))) *
        Wsq t (4 * π ^ 2 * p.1 * p.2) := by
  set s : ℂ := 6 + t * I with hs
  have hsre : s.re = 6 := by simp [hs]
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hG' : Gamma (12 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hc : 12 - s = conj s := by apply Complex.ext <;> simp [hs]; norm_num
  have hnorm : ((‖tauL s‖ ^ 2 : ℝ) : ℂ) = tauL s * tauL (12 - s) := by
    rw [hc, tauL_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have hp : (0:ℝ) < 2 * π := by positivity
  have h2r : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hprod : tauL s * tauL (12 - s) =
      (2 * π : ℂ) ^ (12 : ℂ) * heckeLambda s ^ 2 / (Gamma s * Gamma (12 - s)) := by
    unfold tauL
    rw [heckeLambda_functional_equation, sq]
    have : (2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (12 - s) = (2 * π : ℂ) ^ (12 : ℂ) := by
      rw [← cpow_add _ _ h2]; ring_nf
    field_simp
    linear_combination (heckeLambda s * heckeLambda s) * this
  rw [hnorm, hprod, heckeLambda_sq_afe s (by norm_num : (0:ℝ) < 2),
    ISq_eq_tsum (by norm_num) (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)]
  rw [mul_div_assoc, mul_div_assoc, ← tsum_div_const, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; ext p
  obtain ⟨m, n⟩ := p
  rcases eq_or_ne m 0 with rfl | hm
  · simp [tauC_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tauC_zero]
  have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold Wsq
  rw [← hs]
  have e : (2 * π : ℂ) ^ (12 : ℂ) * (((2 * π * m : ℝ) : ℂ) ^ (-s) *
      ((2 * π * n : ℝ) : ℂ) ^ (-(12 - s))) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-(12 - s)) := by
    rw [h2r, cpow_ofReal_pos hp, cpow_ofReal_pos (by positivity), cpow_ofReal_pos (by positivity),
      show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      cpow_ofReal_pos hmpos, cpow_ofReal_pos hnpos, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [Real.log_mul hp.ne' hmpos.ne', Real.log_mul hp.ne' hnpos.ne']; push_cast; ring
  linear_combination (2 * tauC m * tauC n *
    (W2 s (4 * π ^ 2 * m * n) 2 / (Gamma s * Gamma (12 - s)))) * e

end RamanujanTau.HeckeAFE3
