/-
# Main term of the Δ-AFE

`ker_sub_V_gen` (generic form of `ZetaAFE.KerI_sub_V`): if `‖G(y) e^{−(c+iy)ℓ} − 1‖ ≤ B e^{y²/2}` then
`∫ G(y) e^{z²−zΛ}/z dy = π V(Λ−ℓ) + O(B e^{−c(Λ−ℓ)})`. Applied with `G = R_t`, `ℓ = 2 log(t/2π)`,
`B = K/t²` it gives

    |L(Δ,6+it)|² = Σ_{m,n} τ(m)τ(n)(mn)^{−6} (n/m)^{it} V(log(mn) − 2 log(t/2π)) + O_c(t^{2c−2}).
-/
import RamanujanTau.GoodSecondTerm.GammaRatioD

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL

/-- `K_t(Λ) − π V(Λ−ℓ)` is `O(B e^{−c(Λ−ℓ)})`. -/
theorem ker_sub_V_gen {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hRc : Continuous G)
    {KR : ℝ} (hR : ∀ y : ℝ, ‖G y‖ ≤ KR * Real.exp (y ^ 2 / 2)) {ℓ B : ℝ}
    (hB : ∀ y : ℝ, ‖G y * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1‖ ≤ B * Real.exp (y ^ 2 / 2))
    (Λ : ℝ) :
    ‖(∫ y : ℝ, G y * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) / ((c : ℂ) + y * I)) -
      (Real.pi : ℂ) * (V (Λ - ℓ) : ℂ)‖ ≤
      B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) * Real.exp (-(c * (Λ - ℓ))) := by
  rw [← line_gauss hc (Λ - ℓ)]
  have hint1 : Integrable fun y : ℝ => G y *
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) / ((c : ℂ) + y * I) := by
    have := integrable_line_gauss hc (G := fun y : ℝ => G y * cexp (-(((c : ℂ) + y * I) * Λ)))
      (hRc.mul (by fun_prop)) (K := KR * Real.exp (-(c * Λ))) (fun y => by
        rw [norm_mul, norm_cexp_neg_line]
        calc ‖G y‖ * Real.exp (-(c * Λ)) ≤ KR * Real.exp (y ^ 2 / 2) * Real.exp (-(c * Λ)) := by
              gcongr; exact hR y
          _ = _ := by ring)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [exp_sq_sub]; ring
  have hint2 : Integrable fun y : ℝ =>
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)) / ((c : ℂ) + y * I) := by
    have := integrable_line_gauss hc (G := fun y : ℝ => cexp (-(((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ))))
      (by fun_prop) (K := Real.exp (-(c * (Λ - ℓ)))) (fun y => by
        rw [norm_cexp_neg_line]
        have : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
        have := Real.exp_pos (-(c * (Λ - ℓ)))
        nlinarith)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [exp_sq_sub]
  rw [← integral_sub hint1 hint2]
  have hgauss : Integrable fun y : ℝ => B * Real.exp (c ^ 2) / c * Real.exp (-(c * (Λ - ℓ))) *
      Real.exp (-(1 / 2) * y ^ 2) := (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  refine (norm_integral_le_of_norm_le hgauss (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · have hz0 := line_ne_zero hc.ne' y
    have hzc : c ≤ ‖(c : ℂ) + y * I‖ := by
      have := (norm_line_ge c y).1; rwa [abs_of_pos hc] at this
    have heq : G y * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) /
        ((c : ℂ) + y * I) - cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)) /
        ((c : ℂ) + y * I) =
        (G y * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1) *
        (cexp (((c : ℂ) + y * I) ^ 2) * cexp (-(((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)))) /
          ((c : ℂ) + y * I) := by
      have e1 : cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) =
          cexp (-(((c : ℂ) + y * I) * ℓ)) * (cexp (((c : ℂ) + y * I) ^ 2) *
            cexp (-(((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)))) := by
        simp only [← Complex.exp_add]; congr 1; push_cast; ring
      have e2 : cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)) =
          cexp (((c : ℂ) + y * I) ^ 2) * cexp (-(((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ))) := by
        rw [sub_eq_add_neg, Complex.exp_add]
      rw [e1, e2]; field_simp
    rw [heq, norm_div, norm_mul, norm_mul, norm_cexp_sq_line, norm_cexp_neg_line]
    rw [div_le_iff₀ (hc.trans_le hzc)]
    have hb := hB y
    have hB0 : 0 ≤ B := by
      have := (norm_nonneg _).trans (hB 0); simp at this; exact this
    calc ‖G y * cexp (-((↑c + ↑y * I) * ↑ℓ)) - 1‖ *
          (Real.exp (c ^ 2 - y ^ 2) * Real.exp (-(c * (Λ - ℓ))))
        ≤ B * Real.exp (y ^ 2 / 2) * (Real.exp (c ^ 2 - y ^ 2) * Real.exp (-(c * (Λ - ℓ)))) := by
          gcongr
      _ = B * Real.exp (c ^ 2) / c * Real.exp (-(c * (Λ - ℓ))) * Real.exp (-(1 / 2) * y ^ 2) * c := by
          have e : Real.exp (y ^ 2 / 2) * (Real.exp (c ^ 2 - y ^ 2) * Real.exp (-(c * (Λ - ℓ)))) =
              Real.exp (c ^ 2) * Real.exp (-(c * (Λ - ℓ))) * Real.exp (-(1 / 2) * y ^ 2) := by
            simp only [← Real.exp_add]; congr 1; ring
          rw [mul_assoc B, e]; field_simp
      _ ≤ _ := by gcongr
  · rw [integral_const_mul, integral_gaussian]
    rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring]
    ring


/-- `|τ(m)τ(n)| (mn)^{−6}`-type real coefficient: `τ(M)τ(N) e^{−6Λ}`, `Λ = log M + log N`. -/
noncomputable def coefD (p : ℕ × ℕ) : ℝ :=
  ((tau (p.1 + 1) : ℤ) : ℝ) * ((tau (p.2 + 1) : ℤ) : ℝ) * Real.exp (-(6 * (lg p.1 + lg p.2)))

/-- Main-term coefficient `τ(m)τ(n)(mn)^{−6}(n/m)^{it} V(log(mn) − ℓ)`. -/
noncomputable def bD (t ℓ : ℝ) (p : ℕ × ℕ) : ℂ :=
  (coefD p : ℂ) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * (V (lg p.1 + lg p.2 - ℓ) : ℂ)

lemma tC_div_eq (m : ℕ) (s : ℂ) :
    tC m / ((m : ℂ) + 1) ^ s = (((tau (m + 1) : ℤ) : ℝ) : ℂ) * cexp (-((lg m : ℂ) * s)) := by
  rw [div_eq_mul_one_div, one_div_cpow_eq]; unfold tC; push_cast; rfl

lemma afeTermD_eq (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) :
    afeTermD t c p y = (coefD p : ℂ) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      (RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) /
        ((c : ℂ) + y * I)) := by
  unfold afeTermD coefD
  rw [tC_div_eq, tC_div_eq]
  unfold dp dm
  have e : cexp (((c : ℂ) + y * I) ^ 2) * (cexp (-((lg p.1 : ℂ) * (6 + (c + y * I) + t * I))) *
      cexp (-((lg p.2 : ℂ) * (6 + (c + y * I) - t * I)))) =
      ((Real.exp (-(6 * (lg p.1 + lg p.2))) : ℝ) : ℂ) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp]; simp only [← Complex.exp_add]; congr 1; push_cast; ring
  push_cast at e ⊢
  linear_combination (RtD t (↑c + ↑y * I) / (↑c + ↑y * I) * ((tau (p.1 + 1) : ℂ) * (tau (p.2 + 1) : ℂ))) * e

lemma integral_afeTermD (t c : ℝ) (p : ℕ × ℕ) :
    ∫ y : ℝ, afeTermD t c p y = (coefD p : ℂ) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      ∫ y : ℝ, RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 -
        ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) / ((c : ℂ) + y * I) := by
  simp_rw [afeTermD_eq]; rw [integral_const_mul]

lemma abs_coefD (σ : ℝ) (p : ℕ × ℕ) :
    |coefD p| * Real.exp (-((σ - 6) * (lg p.1 + lg p.2))) =
      (|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-σ)) *
      (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-σ)) := by
  unfold coefD
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e : Real.exp (-(6 * (lg p.1 + lg p.2))) * Real.exp (-((σ - 6) * (lg p.1 + lg p.2))) =
      Real.exp (-(σ * (lg p.1 + lg p.2))) := by rw [← Real.exp_add]; congr 1; ring
  rw [mul_assoc (|((tau (p.1 + 1) : ℤ) : ℝ)| * |((tau (p.2 + 1) : ℤ) : ℝ)|), e, exp_neg_lg]
  ring

/-- `Zτ_σ = Σ_{n≥1} |τ(n)| n^{−σ}`. -/
noncomputable def Ztau (σ : ℝ) : ℝ := ∑' n : ℕ, |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ)

lemma summable_tt {σ : ℝ} (hσ : 13 / 2 < σ) :
    Summable fun p : ℕ × ℕ => (|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-σ)) *
      (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-σ)) :=
  summable_mul_of_summable_norm (f := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ))
    (g := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ))
    (by simpa [Real.norm_eq_abs] using (summable_abs_tau_shift hσ).abs)
    (by simpa [Real.norm_eq_abs] using (summable_abs_tau_shift hσ).abs)

lemma tsum_tt {σ : ℝ} (hσ : 13 / 2 < σ) :
    ∑' p : ℕ × ℕ, (|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-σ)) *
      (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-σ)) = Ztau σ ^ 2 := by
  rw [sq, Ztau]
  exact (tsum_mul_tsum_of_summable_norm (f := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ))
    (g := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ))
    (by simpa [Real.norm_eq_abs] using (summable_abs_tau_shift hσ).abs)
    (by simpa [Real.norm_eq_abs] using (summable_abs_tau_shift hσ).abs)).symm

lemma norm_bD_le (t ℓ : ℝ) (p : ℕ × ℕ) :
    ‖bD t ℓ p‖ ≤ 2 * Real.exp ℓ * ((|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-(7 : ℝ))) *
      (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-(7 : ℝ)))) := by
  unfold bD
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_exp_osc, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (V_nonneg _), ← abs_coefD 7]
  have hV := V_le_exp (lg p.1 + lg p.2 - ℓ)
  have h0 := abs_nonneg (coefD p)
  calc |coefD p| * 1 * V (lg p.1 + lg p.2 - ℓ) ≤ |coefD p| * 1 * (2 * Real.exp (-(lg p.1 + lg p.2 - ℓ))) := by
        gcongr
    _ = _ := by
        rw [show -(lg p.1 + lg p.2 - ℓ) = ℓ + -((7 - 6) * (lg p.1 + lg p.2)) by ring, Real.exp_add]; ring

lemma summable_bD (t ℓ : ℝ) : Summable (bD t ℓ) :=
  Summable.of_norm_bounded ((summable_tt (by norm_num)).mul_left _) (norm_bD_le t ℓ)

/-- **The Δ-AFE with explicit main term.** -/
theorem delta_sq_approx {t c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1)
    (hRc : Continuous fun y : ℝ => RtD t (c + y * I)) {KR : ℝ}
    (hR : ∀ y : ℝ, ‖RtD t (c + y * I)‖ ≤ KR * Real.exp (y ^ 2 / 2)) {ℓ B : ℝ}
    (hB : ∀ y : ℝ, ‖RtD t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1‖ ≤ B * Real.exp (y ^ 2 / 2)) :
    ‖((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) - ∑' p : ℕ × ℕ, bD t ℓ p‖ ≤
      B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) / Real.pi * Real.exp (c * ℓ) *
        Ztau (6 + c) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hafe := afe_exact_delta hc hc1 hRc hR
  set C₁ : ℝ := B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) with hC₁
  set d : ℕ × ℕ → ℂ := fun p => (∫ y : ℝ, afeTermD t c p y) / Real.pi - bD t ℓ p with hd
  have hσ : 13 / 2 < 6 + c := by linarith
  have hdb : ∀ p, ‖d p‖ ≤ C₁ / Real.pi * Real.exp (c * ℓ) *
      ((|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-(6 + c))) *
        (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-(6 + c)))) := by
    intro p
    have hk := ker_sub_V_gen hc0 hRc hR hB (lg p.1 + lg p.2)
    have heq : d p = (coefD p : ℂ) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
        ((∫ y : ℝ, RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 -
          ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) / ((c : ℂ) + y * I)) -
          (Real.pi : ℂ) * (V (lg p.1 + lg p.2 - ℓ) : ℂ)) / Real.pi := by
      simp only [hd, integral_afeTermD, bD]; field_simp
    rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_real, norm_exp_osc, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, ← abs_coefD (6 + c)]
    have hC0 : 0 ≤ C₁ := by
      rw [hC₁]
      have hB0 : 0 ≤ B := by
        have := (norm_nonneg _).trans (hB 0); simp at this; exact this
      positivity
    have ha := abs_nonneg (coefD p)
    calc |coefD p| * 1 * ‖(∫ y : ℝ, RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 -
          ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) / ((c : ℂ) + y * I)) -
          (Real.pi : ℂ) * (V (lg p.1 + lg p.2 - ℓ) : ℂ)‖ / Real.pi
        ≤ |coefD p| * 1 * (C₁ * Real.exp (-(c * (lg p.1 + lg p.2 - ℓ)))) / Real.pi := by gcongr
      _ = _ := by
        rw [show -(c * (lg p.1 + lg p.2 - ℓ)) = c * ℓ + -((6 + c - 6) * (lg p.1 + lg p.2)) by ring,
          Real.exp_add]
        ring
  have hds : Summable d := Summable.of_norm_bounded ((summable_tt hσ).mul_left _) hdb
  have hsplit : ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) = ∑' p : ℕ × ℕ, bD t ℓ p + ∑' p, d p := by
    rw [← (summable_bD t ℓ).tsum_add hds]
    have : ∀ p, bD t ℓ p + d p = (∫ y : ℝ, afeTermD t c p y) / Real.pi := by
      intro p; simp only [hd]; ring
    simp_rw [this]
    rw [tsum_div_const, ← hafe]
    field_simp
  rw [hsplit, add_sub_cancel_left]
  have hs2 : Summable fun p => ‖d p‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdb
    ((summable_tt hσ).mul_left _)
  refine (norm_tsum_le_tsum_norm hs2).trans ?_
  refine (hs2.tsum_le_tsum hdb ((summable_tt hσ).mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_tt hσ]

end RamanujanTau.GoodSecondTerm
