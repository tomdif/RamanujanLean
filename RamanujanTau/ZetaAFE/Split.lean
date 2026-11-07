/-
# Main term and error of the AFE

Write `M = m+1`, `N = n+1`, `Λ = log M + log N`, `ℓ = log(t/2π)`. Then
`∫ afeTerm = (MN)^{−1/2} (N/M)^{it} K_t(Λ)` with `K_t(Λ) = ∫ R_t(z) e^{z² − zΛ}/z dy`, and if
`‖R_t(z) e^{−zℓ} − 1‖ ≤ B e^{y²/2}` on the line then `K_t(Λ) = π V(Λ − ℓ) + O(B e^{−c(Λ−ℓ)})`.
Summing: `|ζ(1/2+it)|² = Σ_{m,n} (MN)^{−1/2}(N/M)^{it} V(Λ−ℓ) + O(B e^{cℓ} Z²)`, `Z = Σ n^{−1/2−c}`.
-/
import RamanujanTau.ZetaAFE.AFE

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

noncomputable def lg (m : ℕ) : ℝ := Real.log ((m : ℝ) + 1)

lemma lg_nonneg (m : ℕ) : 0 ≤ lg m := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])

lemma one_div_cpow_eq (m : ℕ) (s : ℂ) : 1 / ((m : ℂ) + 1) ^ s = cexp (-((lg m : ℂ) * s)) := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
    Complex.exp_neg, one_div]
  rfl

/-- `K_t(Λ) = ∫ R_t(c+iy) e^{z²−zΛ}/z dy`. -/
noncomputable def KerI (t c Λ : ℝ) : ℂ :=
  ∫ y : ℝ, Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) / ((c : ℂ) + y * I)

lemma afeTerm_eq (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) :
    afeTerm t c p y = cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2)) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      (Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) /
        ((c : ℂ) + y * I)) := by
  unfold afeTerm
  rw [one_div_cpow_eq, one_div_cpow_eq]
  unfold sp sm
  have e : cexp (((c : ℂ) + y * I) ^ 2) * (cexp (-((lg p.1 : ℂ) * (1 / 2 + (c + y * I) + t * I))) *
      cexp (-((lg p.2 : ℂ) * (1 / 2 + (c + y * I) - t * I)))) =
      cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2)) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((lg p.1 + lg p.2 : ℝ) : ℂ)) := by
    simp only [← Complex.exp_add]; congr 1; push_cast; ring
  calc Rt t (↑c + ↑y * I) * cexp ((↑c + ↑y * I) ^ 2) / (↑c + ↑y * I) *
        (cexp (-(↑(lg p.1) * (1 / 2 + (↑c + ↑y * I) + ↑t * I))) *
          cexp (-(↑(lg p.2) * (1 / 2 + (↑c + ↑y * I) - ↑t * I))))
      = Rt t (↑c + ↑y * I) * (cexp ((↑c + ↑y * I) ^ 2) *
        (cexp (-(↑(lg p.1) * (1 / 2 + (↑c + ↑y * I) + ↑t * I))) *
          cexp (-(↑(lg p.2) * (1 / 2 + (↑c + ↑y * I) - ↑t * I))))) / (↑c + ↑y * I) := by ring
    _ = _ := by rw [e]; ring

lemma integral_afeTerm (t c : ℝ) (p : ℕ × ℕ) :
    ∫ y : ℝ, afeTerm t c p y = cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2)) *
      cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) * KerI t c (lg p.1 + lg p.2) := by
  simp_rw [afeTerm_eq]
  rw [integral_const_mul]
  rfl

lemma exp_sq_sub (z L : ℂ) : cexp (z ^ 2 - z * L) = cexp (-(z * L)) * cexp (z ^ 2) := by
  rw [← Complex.exp_add]; ring_nf

lemma norm_cexp_neg_line (c y Λ : ℝ) : ‖cexp (-(((c : ℂ) + y * I) * Λ))‖ = Real.exp (-(c * Λ)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `K_t(Λ) − π V(Λ−ℓ)` is `O(B e^{−c(Λ−ℓ)})`. -/
theorem KerI_sub_V {t c : ℝ} (hc : 0 < c) (hRc : Continuous fun y : ℝ => Rt t (c + y * I))
    {KR : ℝ} (hR : ∀ y : ℝ, ‖Rt t (c + y * I)‖ ≤ KR * Real.exp (y ^ 2 / 2)) {ℓ B : ℝ}
    (hB : ∀ y : ℝ, ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1‖ ≤ B * Real.exp (y ^ 2 / 2))
    (Λ : ℝ) :
    ‖KerI t c Λ - (Real.pi : ℂ) * (V (Λ - ℓ) : ℂ)‖ ≤
      B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) * Real.exp (-(c * (Λ - ℓ))) := by
  rw [← line_gauss hc (Λ - ℓ)]
  unfold KerI
  have hint1 : Integrable fun y : ℝ => Rt t (c + y * I) *
      cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) / ((c : ℂ) + y * I) := by
    have := integrable_line_gauss hc (G := fun y : ℝ => Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * Λ)))
      (hRc.mul (by fun_prop)) (K := KR * Real.exp (-(c * Λ))) (fun y => by
        rw [norm_mul, norm_cexp_neg_line]
        calc ‖Rt t (↑c + ↑y * I)‖ * Real.exp (-(c * Λ)) ≤ KR * Real.exp (y ^ 2 / 2) * Real.exp (-(c * Λ)) := by
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
    have heq : Rt t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * Λ) /
        ((c : ℂ) + y * I) - cexp (((c : ℂ) + y * I) ^ 2 - ((c : ℂ) + y * I) * ((Λ - ℓ : ℝ) : ℂ)) /
        ((c : ℂ) + y * I) =
        (Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1) *
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
    calc ‖Rt t (↑c + ↑y * I) * cexp (-((↑c + ↑y * I) * ↑ℓ)) - 1‖ *
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

/-- `Z_σ = Σ_{n≥1} n^{−σ}`. -/
noncomputable def Zs (σ : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)

lemma summable_uu {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ℕ × ℕ => ((p.1 : ℝ) + 1) ^ (-σ) * ((p.2 : ℝ) + 1) ^ (-σ)) :=
  summable_mul_of_summable_norm (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-σ))
    (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-σ))
    (by simpa [Real.norm_eq_abs] using (summable_rpow_neg hσ).abs)
    (by simpa [Real.norm_eq_abs] using (summable_rpow_neg hσ).abs)

lemma tsum_uu {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : ℕ × ℕ, ((p.1 : ℝ) + 1) ^ (-σ) * ((p.2 : ℝ) + 1) ^ (-σ) = Zs σ ^ 2 := by
  rw [sq, Zs]
  exact (tsum_mul_tsum_of_summable_norm (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-σ))
    (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-σ))
    (by simpa [Real.norm_eq_abs] using (summable_rpow_neg hσ).abs)
    (by simpa [Real.norm_eq_abs] using (summable_rpow_neg hσ).abs)).symm

lemma exp_neg_lg (σ : ℝ) (p : ℕ × ℕ) :
    Real.exp (-(σ * (lg p.1 + lg p.2))) = ((p.1 : ℝ) + 1) ^ (-σ) * ((p.2 : ℝ) + 1) ^ (-σ) := by
  unfold lg
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1; ring

/-- The main-term coefficient `b_p(t) = (MN)^{−1/2} (N/M)^{it} V(Λ − ℓ)`. -/
noncomputable def bterm (t ℓ : ℝ) (p : ℕ × ℕ) : ℂ :=
  cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2)) * cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
    (V (lg p.1 + lg p.2 - ℓ) : ℂ)

lemma norm_exp_half (p : ℕ × ℕ) :
    ‖cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2))‖ = Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

lemma norm_exp_osc (t : ℝ) (p : ℕ × ℕ) : ‖cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_bterm_le (t ℓ : ℝ) (p : ℕ × ℕ) :
    ‖bterm t ℓ p‖ ≤ 2 * Real.exp ℓ * (((p.1 : ℝ) + 1) ^ (-(3 / 2 : ℝ)) * ((p.2 : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  unfold bterm
  rw [norm_mul, norm_mul, norm_exp_half, norm_exp_osc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (V_nonneg _), ← exp_neg_lg]
  have := V_le_exp (lg p.1 + lg p.2 - ℓ)
  calc Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) * 1 * V (lg p.1 + lg p.2 - ℓ)
      ≤ Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) * 1 * (2 * Real.exp (-(lg p.1 + lg p.2 - ℓ))) := by
        gcongr
    _ = _ := by
        rw [mul_one, mul_left_comm, mul_assoc 2, ← Real.exp_add, ← Real.exp_add]; congr 2; ring

lemma summable_bterm (t ℓ : ℝ) : Summable (bterm t ℓ) :=
  Summable.of_norm_bounded ((summable_uu (by norm_num)).mul_left _) (norm_bterm_le t ℓ)

/-- **The AFE with explicit main term.** If `‖R_t(z)e^{−zℓ} − 1‖ ≤ B e^{y²/2}` on `Re z = c`, then
`|ζ(1/2+it)|² = Σ_{m,n} b_{m,n}(t) + O(B e^{cℓ} Z²)`. -/
theorem zeta_sq_approx {t c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1)
    (hRc : Continuous fun y : ℝ => Rt t (c + y * I)) {KR : ℝ}
    (hR : ∀ y : ℝ, ‖Rt t (c + y * I)‖ ≤ KR * Real.exp (y ^ 2 / 2)) {ℓ B : ℝ}
    (hB : ∀ y : ℝ, ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ℓ)) - 1‖ ≤ B * Real.exp (y ^ 2 / 2)) :
    ‖((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) - ∑' p : ℕ × ℕ, bterm t ℓ p‖ ≤
      B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) / Real.pi * Real.exp (c * ℓ) *
        Zs (1 / 2 + c) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hafe := afe_exact hc hc1 hRc hR
  set C₁ : ℝ := B * (Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c) with hC₁
  set d : ℕ × ℕ → ℂ := fun p => (∫ y : ℝ, afeTerm t c p y) / Real.pi - bterm t ℓ p with hd
  have hdb : ∀ p, ‖d p‖ ≤ C₁ / Real.pi * Real.exp (c * ℓ) *
      (((p.1 : ℝ) + 1) ^ (-(1 / 2 + c)) * ((p.2 : ℝ) + 1) ^ (-(1 / 2 + c))) := by
    intro p
    have hk := KerI_sub_V hc0 hRc hR hB (lg p.1 + lg p.2)
    have heq : d p = cexp (-(((lg p.1 + lg p.2 : ℝ) : ℂ) / 2)) *
        cexp (t * I * ((lg p.2 - lg p.1 : ℝ) : ℂ)) *
        (KerI t c (lg p.1 + lg p.2) - (Real.pi : ℂ) * (V (lg p.1 + lg p.2 - ℓ) : ℂ)) / Real.pi := by
      simp only [hd, integral_afeTerm, bterm]; field_simp
    rw [heq, norm_div, norm_mul, norm_mul, norm_exp_half, norm_exp_osc, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, ← exp_neg_lg]
    have hC0 : 0 ≤ C₁ := by
      rw [hC₁]
      have hB0 : 0 ≤ B := by
        have := (norm_nonneg _).trans (hB 0); simp at this; exact this
      positivity
    calc Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) * 1 *
          ‖KerI t c (lg p.1 + lg p.2) - ↑Real.pi * ↑(V (lg p.1 + lg p.2 - ℓ))‖ / Real.pi
        ≤ Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) * 1 * (C₁ * Real.exp (-(c * (lg p.1 + lg p.2 - ℓ))))
          / Real.pi := by gcongr
      _ = C₁ / Real.pi * (Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) *
            Real.exp (-(c * (lg p.1 + lg p.2 - ℓ)))) := by ring
      _ = _ := by
        have e : Real.exp (-((1 / 2) * (lg p.1 + lg p.2))) * Real.exp (-(c * (lg p.1 + lg p.2 - ℓ))) =
            Real.exp (c * ℓ) * Real.exp (-((1 / 2 + c) * (lg p.1 + lg p.2))) := by
          simp only [← Real.exp_add]; congr 1; ring
        rw [e]; ring
  have hds : Summable d := Summable.of_norm_bounded ((summable_uu (by linarith)).mul_left _) hdb
  have hsplit : ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, bterm t ℓ p + ∑' p, d p := by
    rw [← (summable_bterm t ℓ).tsum_add hds]
    have : ∀ p, bterm t ℓ p + d p = (∫ y : ℝ, afeTerm t c p y) / Real.pi := by
      intro p; simp only [hd]; ring
    simp_rw [this]
    rw [tsum_div_const, ← hafe]
    field_simp
  rw [hsplit, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded
    ((summable_uu (by linarith)).mul_left _) (fun p => (norm_norm (d p)).le.trans (hdb p)))).trans ?_
  refine (Summable.tsum_le_tsum hdb (Summable.of_norm_bounded
    ((summable_uu (by linarith)).mul_left _) (fun p => (norm_norm (d p)).le.trans (hdb p)))
    ((summable_uu (by linarith)).mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_uu (by linarith)]

end RamanujanTau.ZetaAFE
