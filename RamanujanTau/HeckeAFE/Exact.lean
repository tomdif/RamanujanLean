/-
# The exact smoothed approximate functional equation for `L(Δ, s)`

With `G(u) = e^{u²}` and the line integral `(1/2πi)∫_{(c)} … du = (1/2π) ∫_ℝ … dy` (`u = c+iy`):

    I_Λ(s; X) = (1/2πi) ∫_{(c)} Λ(s+u) X^u e^{u²} du/u,

* `heckeLambda_afe`: for every `s ∈ ℂ`, `X > 0`, `c > 0`:
  `Λ(s) = I_Λ(s; X) + I_Λ(12−s; 1/X)` (residue at `u = 0` + Hecke's `Λ(12−s) = Λ(s)`);
* `ILam_eq_tsum`: if `Re s + c > 7`, `I_Λ(s; X) = Σ_n τ(n) (2πn)^{−s} W_s(2πn/X)` with
  `W_s(ξ) = (1/2πi) ∫_{(c)} Γ(s+u) ξ^{−u} e^{u²} du/u`;
* `tauL_afe`: for `5 < Re s < 7` and `X > 0`,
  `L(Δ,s) = Σ τ(n) n^{−s} V_s(2πn/X) + ε(s) Σ τ(n) n^{s−12} V_{12−s}(2πnX)`,
  `V_s = W_s/Γ(s)`, `ε(s) = (2π)^{2s−12} Γ(12−s)/Γ(s)`;
* `tauL_afe_line`: the case `s = 6+it`, with `‖ε(6+it)‖ = 1` (`norm_eps_line`).
-/
import RamanujanTau.HeckeAFE.Contour
import RamanujanTau.HeckeL.Main
import RamanujanTau.HeckeConvex.Summable
import RamanujanTau.RankinError.GammaBound

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE

open Complex MeasureTheory Set Filter Topology LSeries RamanujanTau.HeckeL
open scoped Real

/-- `I_Λ(s; X) = (1/2π) ∫_ℝ Λ(s+u) X^u e^{u²}/u dy`, `u = c + iy`. -/
noncomputable def ILam (s : ℂ) (X c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun u => heckeLambda (s + u) * (X : ℂ) ^ u * cexp (u ^ 2) / u) c

/-- `W_s(ξ) = (1/2π) ∫_ℝ Γ(s+u) ξ^{−u} e^{u²}/u dy`, `u = c + iy`. -/
noncomputable def WGam (s : ℂ) (ξ c : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * vline (fun u => Gamma (s + u) * (ξ : ℂ) ^ (-u) * cexp (u ^ 2) / u) c

lemma cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = cexp ((Real.log x : ℂ) * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ofReal_log hx.le]

lemma norm_ofReal_cpow {X : ℝ} (hX : 0 < X) (u : ℂ) : ‖(X : ℂ) ^ u‖ = X ^ u.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hX u

lemma rpow_le_add_of_mem {X a b x : ℝ} (hX : 0 < X) (hax : a ≤ x) (hxb : x ≤ b) :
    X ^ x ≤ X ^ a + X ^ b := by
  rcases le_total 1 X with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hxb; linarith [Real.rpow_pos_of_pos hX a]
  · have := Real.rpow_le_rpow_of_exponent_ge hX h hax; linarith [Real.rpow_pos_of_pos hX b]

/-! ## The exact identity for `Λ` -/

/-- **Smoothed approximate functional equation for `Λ`** (exact, every `s`). -/
theorem heckeLambda_afe (s : ℂ) {X : ℝ} (hX : 0 < X) {c : ℝ} (hc : 0 < c) :
    heckeLambda s = ILam s X c + ILam (12 - s) X⁻¹ c := by
  set F : ℂ → ℂ := fun u => heckeLambda (s + u) * (X : ℂ) ^ u with hFdef
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hFd : DifferentiableOn ℂ F (strip (-c) c) := by
    refine DifferentiableOn.mul ?_ ?_
    · exact (heckeLambda_entire.comp ((differentiable_const _).add differentiable_id)).differentiableOn
    · exact (differentiable_id.const_cpow (Or.inl hX0)).differentiableOn
  have hFb : ∃ M, ∀ u ∈ strip (-c) c, ‖F u‖ ≤ M := by
    obtain ⟨L, hL⟩ := heckeLambda_bdd_strip (s.re - c) (s.re + c)
    refine ⟨L * (X ^ (-c) + X ^ c), fun u hu => ?_⟩
    simp only [hFdef]
    rw [norm_mul, norm_ofReal_cpow hX]
    have h1 := hL (s + u) (by simp; linarith [hu.1]) (by simp; linarith [hu.2])
    have h2 := rpow_le_add_of_mem hX hu.1 hu.2
    exact mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)
  have hres := vline_residue (by linarith : -c < 0) hc hFd hFb
  have hF0 : F 0 = heckeLambda s := by simp [hFdef]
  have hrefl : vline (fun u => F u * cexp (u ^ 2) / u) (-c) =
      -vline (fun u => heckeLambda (12 - s + u) * ((X⁻¹ : ℝ) : ℂ) ^ u * cexp (u ^ 2) / u) c := by
    refine vline_neg_eq (fun u => ?_) c
    simp only [hFdef]
    have hfe : heckeLambda (s + -u) = heckeLambda (12 - s + u) := by
      rw [← heckeLambda_functional_equation (s + -u)]; congr 1; ring
    have hinv : (X : ℂ) ^ (-u) = ((X⁻¹ : ℝ) : ℂ) ^ u := by
      rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hX.le]; exact Real.pi_ne_zero.symm),
        cpow_neg]
    rw [hfe, hinv, neg_sq, div_neg]
  rw [hrefl, sub_neg_eq_add, hF0] at hres
  unfold ILam
  have h2pi : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  rw [← mul_add]
  have : heckeLambda s = (2 * π : ℂ)⁻¹ * (2 * π * heckeLambda s) := by field_simp
  rw [this, ← hres]

/-! ## Dirichlet-series expansion of `I_Λ` -/

lemma ne_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -m := by
  intro h; rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma continuous_Gamma_line {s : ℂ} {c : ℝ} (h : 0 < s.re + c) :
    Continuous (fun y : ℝ => Gamma (s + ((c : ℂ) + y * I))) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hw : 0 < (s + ((c : ℂ) + y * I)).re := by simpa using h
  exact ContinuousAt.comp (g := Gamma) (f := fun y : ℝ => s + ((c : ℂ) + y * I))
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hw)).continuousAt
    (Continuous.continuousAt (by fun_prop))

lemma norm_inv_line_le {c : ℝ} (hc : 0 < c) (y : ℝ) : ‖((c : ℂ) + y * I)⁻¹‖ ≤ c⁻¹ := by
  rw [norm_inv]
  have := norm_line_ge (c := c) y
  rw [abs_of_pos hc] at this
  exact inv_anti₀ hc this

/-- Pointwise bound for the `W`-integrand on a line `Re u = c > 0`. -/
lemma norm_W_integrand_le {s : ℂ} {c ξ : ℝ} (hc : 0 < c) (hsc : 0 < s.re + c) (hξ : 0 < ξ)
    (y : ℝ) :
    ‖Gamma (s + ((c : ℂ) + y * I)) * (ξ : ℂ) ^ (-((c : ℂ) + y * I)) *
        cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)‖ ≤
      Real.Gamma (s.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) * Real.exp (-1 * y ^ 2) := by
  have hw : 0 < (s + ((c : ℂ) + y * I)).re := by simpa using hsc
  have hG := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re hw
  have hre : (s + ((c : ℂ) + y * I)).re = s.re + c := by simp
  rw [hre] at hG
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
  have hr : (-((c : ℂ) + y * I)).re = -c := by simp
  rw [hr]
  have he : Real.exp (c ^ 2 - y ^ 2) = Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hi := norm_inv_line_le hc y
  have hG0 : 0 ≤ Real.Gamma (s.re + c) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc ‖Gamma (s + (↑c + ↑y * I))‖ * ξ ^ (-c) * (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) *
        ‖((c : ℂ) + y * I)⁻¹‖
      ≤ Real.Gamma (s.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * Real.exp (-1 * y ^ 2)) * c⁻¹ := by
        gcongr
    _ = _ := by ring

lemma integrable_W_integrand {s : ℂ} {c ξ : ℝ} (hc : 0 < c) (hsc : 0 < s.re + c) (hξ : 0 < ξ) :
    Integrable (fun y : ℝ => Gamma (s + ((c : ℂ) + y * I)) * (ξ : ℂ) ^ (-((c : ℂ) + y * I)) *
        cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have hcont : Continuous (fun y : ℝ => Gamma (s + ((c : ℂ) + y * I)) *
      (ξ : ℂ) ^ (-((c : ℂ) + y * I)) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
    refine Continuous.div ?_ (continuous_line c) (line_ne_zero hc.ne')
    refine ((continuous_Gamma_line hsc).mul ?_).mul (by fun_prop)
    exact continuous_iff_continuousAt.2 fun y =>
      ((continuousAt_const_cpow hξ0).comp (by fun_prop : Continuous fun y : ℝ =>
        -((c : ℂ) + y * I)).continuousAt)
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
    (Real.Gamma (s.re + c) * ξ ^ (-c) * (Real.exp (c ^ 2) * c⁻¹)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  exact norm_W_integrand_le hc hsc hξ y

/-- the key power identity `(2π)^{−(s+u)} n^{−(s+u)} X^u = (2πn)^{−s} (2πn/X)^{−u}` -/
lemma power_key {n X : ℝ} (hn : 0 < n) (hX : 0 < X) (s u : ℂ) :
    (2 * π : ℂ) ^ (-(s + u)) * ((n : ℂ) ^ (s + u))⁻¹ * (X : ℂ) ^ u =
      ((2 * π * n : ℝ) : ℂ) ^ (-s) * ((2 * π * n / X : ℝ) : ℂ) ^ (-u) := by
  have h2 : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hp : (0:ℝ) < 2 * π := by positivity
  rw [h2, cpow_ofReal_pos hp, cpow_ofReal_pos hn, cpow_ofReal_pos hX,
    cpow_ofReal_pos (by positivity), cpow_ofReal_pos (by positivity), ← Complex.exp_neg,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.log_div (by positivity) hX.ne', Real.log_mul (by positivity) hn.ne']
  push_cast; ring

lemma real_power_key {n X σ c : ℝ} (hn : 0 < n) (hX : 0 < X) :
    (2 * π * n) ^ (-σ) * (2 * π * n / X) ^ (-c) =
      (2 * π) ^ (-σ - c) * X ^ c * (1 / n ^ (σ + c)) := by
  have hp : (0:ℝ) < 2 * π := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hn, one_div,
    ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) hX.ne', Real.log_mul (by positivity) hn.ne']
  ring

/-- **Dirichlet expansion**: for `Re s + c > 7`,
`I_Λ(s; X) = Σ_n τ(n) (2πn)^{−s} W_s(2πn/X)`. -/
theorem ILam_eq_tsum {s : ℂ} {X c : ℝ} (hX : 0 < X) (hc : 0 < c) (hs : 7 < s.re + c) :
    ILam s X c = ∑' n : ℕ, tauC n * ((2 * π * n : ℝ) : ℂ) ^ (-s) * WGam s (2 * π * n / X) c := by
  set f : ℕ → ℝ → ℂ := fun n y => tauC n * ((2 * π * n : ℝ) : ℂ) ^ (-s) *
    (Gamma (s + ((c : ℂ) + y * I)) * ((2 * π * n / X : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) with hfdef
  have hsc : 0 < s.re + c := by linarith
  -- pointwise expansion
  have hpt : ∀ y : ℝ, heckeLambda (s + ((c : ℂ) + y * I)) * (X : ℂ) ^ ((c : ℂ) + y * I) *
      cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) = ∑' n, f n y := by
    intro y
    set u : ℂ := (c : ℂ) + y * I
    have hw : 7 < (s + u).re := by simpa [u] using hs
    rw [heckeLambda_eq hw, LSeries]
    rw [show (2 * π : ℂ) ^ (-(s + u)) * Gamma (s + u) * (∑' n, term tauC (s + u) n) *
        (X : ℂ) ^ u * cexp (u ^ 2) / u =
        (∑' n, term tauC (s + u) n) * ((2 * π : ℂ) ^ (-(s + u)) * Gamma (s + u) *
          (X : ℂ) ^ u * cexp (u ^ 2) / u) by ring]
    rw [← tsum_mul_right]
    congr 1; ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, term, tauC_zero]
    · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hk := power_key hnpos hX s u
      simp only [hfdef, term, if_neg hn]
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, div_eq_mul_inv (tauC n)]
      linear_combination (tauC n * Gamma (s + u) * cexp (u ^ 2) / u) * hk
  -- summability of the norms
  have hint : ∀ n, Integrable (f n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [hfdef, tauC_zero, zero_mul]; exact integrable_zero _ _ _
    · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact (integrable_W_integrand hc hsc (by positivity)).const_mul _
  set K : ℝ := Real.Gamma (s.re + c) * (Real.exp (c ^ 2) * c⁻¹) * ∫ y : ℝ, Real.exp (-1 * y ^ 2)
  have hK0 : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos hsc
    have : 0 ≤ ∫ y : ℝ, Real.exp (-1 * y ^ 2) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  have hbd : ∀ n, ∫ y, ‖f n y‖ ≤
      |(tau n : ℝ)| / (n : ℝ) ^ (s.re + c) * ((2 * π) ^ (-s.re - c) * X ^ c * K) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef, tauC_zero, tau_zero]
    · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hξ : (0:ℝ) < 2 * π * n / X := by positivity
      have hle : ∀ y, ‖f n y‖ ≤ |(tau n : ℝ)| * (2 * π * n) ^ (-s.re) *
          (Real.Gamma (s.re + c) * (2 * π * n / X) ^ (-c) * (Real.exp (c ^ 2) * c⁻¹) *
            Real.exp (-1 * y ^ 2)) := by
        intro y
        simp only [hfdef]
        rw [norm_mul, norm_mul, norm_ofReal_cpow (by positivity), neg_re]
        have hτ : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
        rw [hτ]
        gcongr
        exact norm_W_integrand_le hc hsc hξ y
      refine (integral_mono (hint n).norm ?_ hle).trans (le_of_eq ?_)
      · exact ((integrable_exp_neg_mul_sq one_pos).const_mul _).const_mul _
      · simp_rw [← mul_assoc]
        rw [integral_const_mul]
        have := real_power_key (σ := s.re) (c := c) hnpos hX
        calc _ = |(tau n : ℝ)| * ((2 * π * n) ^ (-s.re) * (2 * π * n / X) ^ (-c)) * K := by
              simp only [K]; ring
          _ = _ := by rw [this]; ring
  have hsum : Summable fun n => ∫ y, ‖f n y‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbd ?_
    exact (RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by linarith)).mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  unfold ILam vline
  simp_rw [hpt]
  rw [← hswap, ← tsum_mul_left]
  congr 1; ext n
  unfold WGam vline
  simp only [hfdef]
  rw [integral_const_mul]
  ring

/-! ## The normalized AFE for `L(Δ, s)` -/

/-- the normalized weight `V_s(ξ) = W_s(ξ)/Γ(s)` (contour `Re u = 2`). -/
noncomputable def V (s : ℂ) (ξ : ℝ) : ℂ := WGam s ξ 2 / Gamma s

/-- the root factor `ε(s) = (2π)^{2s−12} Γ(12−s)/Γ(s)`. -/
noncomputable def eps (s : ℂ) : ℂ := (2 * π : ℂ) ^ (2 * s - 12) * Gamma (12 - s) / Gamma s

/-- **Smoothed approximate functional equation for `L(Δ,s)`**, `5 < Re s < 7`, any `X > 0`:
`L(Δ,s) = Σ τ(n) n^{−s} V_s(2πn/X) + ε(s) Σ τ(n) n^{s−12} V_{12−s}(2πnX)`. -/
theorem tauL_afe {s : ℂ} (h5 : 5 < s.re) (h7 : s.re < 7) {X : ℝ} (hX : 0 < X) :
    tauL s = ∑' n : ℕ, tauC n * (n : ℂ) ^ (-s) * V s (2 * π * n / X) +
      eps s * ∑' n : ℕ, tauC n * (n : ℂ) ^ (s - 12) * V (12 - s) (2 * π * n * X) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hG' : Gamma (12 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  have hp : (0:ℝ) < 2 * π := by positivity
  have h2r : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [tauL, heckeLambda_afe s hX (by norm_num : (0:ℝ) < 2),
    ILam_eq_tsum hX (by norm_num) (by linarith),
    ILam_eq_tsum (inv_pos.2 hX) (by norm_num) (by simp; linarith), mul_add]
  congr 1
  · rw [← tsum_mul_left]
    congr 1; ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [tauC_zero]
    · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      unfold V
      have e : (2 * π : ℂ) ^ s * ((2 * π * n : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := by
        rw [h2r, cpow_ofReal_pos hp, cpow_ofReal_pos (by positivity),
          show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_ofReal_pos hnpos,
          ← Complex.exp_add]
        congr 1; rw [Real.log_mul hp.ne' hnpos.ne']; push_cast; ring
      rw [← e]; field_simp
  · rw [← tsum_mul_left, ← tsum_mul_left]
    congr 1; ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [tauC_zero]
    · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      unfold V eps
      have hX' : 2 * π * n / X⁻¹ = 2 * π * n * X := by rw [div_inv_eq_mul]
      rw [hX']
      have e : (2 * π : ℂ) ^ s * ((2 * π * n : ℝ) : ℂ) ^ (-(12 - s)) =
          (2 * π : ℂ) ^ (2 * s - 12) * (n : ℂ) ^ (s - 12) := by
        rw [h2r, cpow_ofReal_pos hp, cpow_ofReal_pos (by positivity), cpow_ofReal_pos hp,
          show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_ofReal_pos hnpos,
          ← Complex.exp_add, ← Complex.exp_add]
        congr 1; rw [Real.log_mul hp.ne' hnpos.ne']; push_cast; ring
      have e2 : (2 * π : ℂ) ^ s * (Gamma s)⁻¹ *
          (tauC n * ((2 * π * n : ℝ) : ℂ) ^ (-(12 - s)) * WGam (12 - s) (2 * π * n * X) 2) =
          (2 * π : ℂ) ^ (2 * s - 12) * (n : ℂ) ^ (s - 12) * (Gamma s)⁻¹ * tauC n *
            WGam (12 - s) (2 * π * n * X) 2 := by
        rw [← e]; ring
      rw [e2]; field_simp

lemma line_twelve_sub (t : ℝ) : 12 - ((6 : ℂ) + t * I) = 6 + ((-t : ℝ) : ℂ) * I := by
  push_cast; ring

/-- **The AFE on the critical line** `s = 6 + it`, any `X > 0`. -/
theorem tauL_afe_line (t : ℝ) {X : ℝ} (hX : 0 < X) :
    tauL (6 + t * I) =
      ∑' n : ℕ, tauC n * (n : ℂ) ^ (-(6 + t * I)) * V (6 + t * I) (2 * π * n / X) +
      eps (6 + t * I) * ∑' n : ℕ, tauC n * (n : ℂ) ^ (-(6 + ((-t : ℝ) : ℂ) * I)) *
        V (6 + ((-t : ℝ) : ℂ) * I) (2 * π * n * X) := by
  have h := tauL_afe (s := 6 + t * I) (by simp; norm_num) (by simp; norm_num) hX
  rw [line_twelve_sub] at h
  rw [h]
  have e : ((6 : ℂ) + t * I - 12) = -(6 + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
  rw [e]

/-- `|ε(6+it)| = 1`. -/
theorem norm_eps_line (t : ℝ) : ‖eps (6 + t * I)‖ = 1 := by
  unfold eps
  have hG : Gamma (6 + t * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hc : 12 - ((6 : ℂ) + t * I) = starRingEnd ℂ (6 + t * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [hc, Gamma_conj, norm_div, norm_mul, Complex.norm_conj]
  have h1 : ‖(2 * π : ℂ) ^ (2 * ((6 : ℂ) + t * I) - 12)‖ = 1 := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      norm_ofReal_cpow (by positivity)]
    simp; norm_num
  rw [h1, one_mul, div_self (norm_ne_zero_iff.2 hG)]

end RamanujanTau.HeckeAFE
