/-
# Approximate functional equation for `|ζ(1/2+it)|²` and Ingham's mean-square theorem

Headlines (namespace `RamanujanTau.ZetaAFE`), all axiom-clean:

* `afe_exact` — exact AFE: `π|ζ(1/2+it)|² = Σ_{m,n} ∫_ℝ R_t(z) e^{z²}/z · m^{−1/2−z−it} n^{−1/2−z+it} dy`
  on `z = c + iy`, `1/2 < c ≤ 1` (conditional on two properties of `R_t` which `GammaBound` proves).
* `zeta_afe` — smoothed AFE with explicit main term:
  `|ζ(1/2+it)|² = Σ_{m,n≥1} (mn)^{−1/2} (n/m)^{it} V(log(mn/(t/2π))) + O_c(t^{c−1})`,
  `V(L) = ∫_{u>L} e^{−u²/4}/√π du = erfc(L/2)`.
* `zeta_mean_square_ingham` — `∫₀ᵀ |ζ(1/2+it)|² dt = T log(T/2π) + (2γ−1)T + O_ε(T^{1/2+ε})`.
* `zeta_mean_square_ingham_littleo` — the same with `o(T)`.
-/
import RamanujanTau.ZetaAFE.Ingham

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

/-- **Smoothed approximate functional equation** for `|ζ(1/2+it)|²`. For `1/2 < c ≤ 1` there is `C`
with, for `t ≥ 8`,
`| |ζ(1/2+it)|² − Σ_{m,n≥1} (mn)^{−1/2} (n/m)^{it} V(log(mn) − log(t/2π)) | ≤ C t^{c−1}`
(`bterm t ℓ (m−1,n−1) = (mn)^{−1/2} e^{it log(n/m)} V(log(mn) − ℓ)`). -/
theorem zeta_afe {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 8 ≤ t →
      ‖((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) -
        ∑' p : ℕ × ℕ, bterm t (Real.log (t / (2 * Real.pi))) p‖ ≤ C * t ^ (c - 1) := by
  obtain ⟨C, hC0, hC⟩ := pointwise_err hc hc1
  refine ⟨C, hC0, fun t ht => ?_⟩
  have := hC t ht
  have e := tsum_bterm_split t
  unfold ellT at e
  unfold zsq at this
  rw [e, ← sub_sub]
  exact this

/-- `bterm` unfolded: `(mn)^{−1/2} (n/m)^{it} V(log(mn) − ℓ)` with `m = p.1+1`, `n = p.2+1`. -/
theorem bterm_eq (t ℓ : ℝ) (p : ℕ × ℕ) :
    bterm t ℓ p = ((((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) : ℝ) *
      cexp (t * I * ((Real.log ((p.2 : ℝ) + 1) - Real.log ((p.1 : ℝ) + 1) : ℝ) : ℂ)) *
      (V (Real.log (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) - ℓ) : ℂ) := by
  unfold bterm lg
  have h1 : cexp (-(((Real.log ((p.1 : ℝ) + 1) + Real.log ((p.2 : ℝ) + 1) : ℝ) : ℂ) / 2)) =
      ((((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) : ℝ) := by
    rw [show -(((Real.log ((p.1 : ℝ) + 1) + Real.log ((p.2 : ℝ) + 1) : ℝ) : ℂ) / 2) =
      ((-(Real.log ((p.1 : ℝ) + 1) + Real.log ((p.2 : ℝ) + 1)) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    congr 1
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (by positivity)]
    congr 1; ring
  rw [h1, Real.log_mul (by positivity) (by positivity)]

/-- **Ingham's theorem** (1926): for every `ε > 0`,
`∫₀ᵀ |ζ(1/2+it)|² dt = T log(T/2π) + (2γ − 1)T + O_ε(T^{1/2+ε})`. -/
theorem zeta_mean_square_ingham {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 8 ≤ T →
      |(∫ t in (0:ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) -
        (T * Real.log (T / (2 * Real.pi)) + (2 * Real.eulerMascheroniConstant - 1) * T)| ≤
        C * T ^ (1 / 2 + ε) := by
  set c : ℝ := min (1 / 2 + ε) 1 with hcdef
  have hc : 1 / 2 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c ≤ 1 := min_le_right _ _
  obtain ⟨C, hC⟩ := ingham_rpow hc hc1
  refine ⟨max C 0, fun T hT => ?_⟩
  have h := hC T hT
  unfold zsq ellT at h
  refine h.trans ?_
  have hTc : T ^ c ≤ T ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_left _ _)
  have : 0 ≤ T ^ c := by positivity
  calc C * T ^ c ≤ max C 0 * T ^ c := mul_le_mul_of_nonneg_right (le_max_left _ _) this
    _ ≤ max C 0 * T ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_left hTc (le_max_right _ _)

/-- **Ingham's theorem, `o(T)` form.** -/
theorem zeta_mean_square_ingham_littleo :
    Tendsto (fun T : ℝ => ((∫ t in (0:ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) -
      (T * Real.log (T / (2 * Real.pi)) + (2 * Real.eulerMascheroniConstant - 1) * T)) / T)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := zeta_mean_square_ingham (ε := 1 / 4) (by norm_num)
  have hlim : Tendsto (fun T : ℝ => |C| * T ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 4)).const_mul |C|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (8 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT0, div_le_iff₀ hT0]
  refine (hC T hT).trans ?_
  have e : T ^ (1 / 2 + 1 / 4 : ℝ) = T ^ (-(1 / 4 : ℝ)) * T := by
    rw [← Real.rpow_add_one hT0.ne']; norm_num
  rw [e]
  have : 0 ≤ T ^ (-(1 / 4 : ℝ)) * T := by positivity
  calc C * (T ^ (-(1 / 4 : ℝ)) * T) ≤ |C| * (T ^ (-(1 / 4 : ℝ)) * T) := by
        gcongr; exact le_abs_self C
    _ = _ := by ring

end RamanujanTau.ZetaAFE

#print axioms RamanujanTau.ZetaAFE.line_gauss
#print axioms RamanujanTau.ZetaAFE.afe_line
#print axioms RamanujanTau.ZetaAFE.afe_exact
#print axioms RamanujanTau.ZetaAFE.zeta_sq_approx
#print axioms RamanujanTau.ZetaAFE.gamma_ratio_line
#print axioms RamanujanTau.ZetaAFE.norm_E_le
#print axioms RamanujanTau.ZetaAFE.abs_Dsum_sub_le
#print axioms RamanujanTau.ZetaAFE.norm_integral_bterm_off
#print axioms RamanujanTau.ZetaAFE.zeta_afe
#print axioms RamanujanTau.ZetaAFE.bterm_eq
#print axioms RamanujanTau.ZetaAFE.ingham_rpow
#print axioms RamanujanTau.ZetaAFE.zeta_mean_square_ingham
#print axioms RamanujanTau.ZetaAFE.zeta_mean_square_ingham_littleo
