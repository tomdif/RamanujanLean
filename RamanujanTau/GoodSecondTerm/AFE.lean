/-
# The symmetric (χ-free) AFE for `|L(Δ, 6+it)|²`

`Φ_t(z) = Λ(6+z+it) Λ(6+z−it)`, `Λ(s) = (2π)^{−s}Γ(s)L(Δ,s)` (`heckeLambda`, entire, `Λ(12−s) = Λ(s)`),
is entire and even in `z`; `ZetaAFE.afe_line` gives `∫_{(c)} Φ_t(z) e^{z²}/z dy = π Φ_t(0)`. On
`Re z = c > 1/2` the Dirichlet series of `L(6+z±it)` converge absolutely (`Σ|τ(n)| n^{−σ} < ∞` for
`σ > 13/2`, from Rankin–Selberg + Cauchy–Schwarz, `HeckeConvex`), so

    π |L(6+it)|² = Σ_{m,n≥1} ∫_ℝ R_t(z) e^{z²}/z · τ(m) m^{−6−z−it} τ(n) n^{−6−z+it} dy,

`R_t(z) = (2π)^{−2z} Γ(6+z+it)Γ(6+z−it) / (Γ(6+it)Γ(6−it))`.
-/
import RamanujanTau.ZetaAFE.Split
import RamanujanTau.HeckeZeros.Zeros
import RamanujanTau.HeckeConvex.Convex

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL

noncomputable def dp (t : ℝ) (z : ℂ) : ℂ := 6 + z + t * I
noncomputable def dm (t : ℝ) (z : ℂ) : ℂ := 6 + z - t * I
noncomputable def PhiD (t : ℝ) (z : ℂ) : ℂ := heckeLambda (dp t z) * heckeLambda (dm t z)
/-- `g(s) = (2π)^{−s} Γ(s)`. -/
noncomputable def gD (s : ℂ) : ℂ := (2 * Real.pi : ℂ) ^ (-s) * Gamma s
noncomputable def G0D (t : ℝ) : ℂ := gD (dp t 0) * gD (dm t 0)
noncomputable def RtD (t : ℝ) (z : ℂ) : ℂ := gD (dp t z) * gD (dm t z) / G0D t

noncomputable def tC (n : ℕ) : ℂ := ((tau (n + 1) : ℤ) : ℂ)

/-- The `(m,n)` term of the Δ-AFE (indices shifted by one). -/
noncomputable def afeTermD (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) : ℂ :=
  RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) *
    (tC p.1 / ((p.1 : ℂ) + 1) ^ dp t (c + y * I) * (tC p.2 / ((p.2 : ℂ) + 1) ^ dm t (c + y * I)))

lemma PhiD_neg (t : ℝ) (z : ℂ) : PhiD t (-z) = PhiD t z := by
  unfold PhiD
  have h1 : dp t (-z) = 12 - dm t z := by unfold dp dm; ring
  have h2 : dm t (-z) = 12 - dp t z := by unfold dp dm; ring
  rw [h1, h2, heckeLambda_functional_equation, heckeLambda_functional_equation, mul_comm]

lemma differentiable_PhiD (t : ℝ) : Differentiable ℂ (PhiD t) := by
  unfold PhiD dp dm
  have := heckeLambda_entire
  fun_prop

lemma norm_PhiD_le (t : ℝ) {c : ℝ} (hc1 : c ≤ 1) :
    ∃ K : ℝ, ∀ x y : ℝ, |x| ≤ c → ‖PhiD t (x + y * I)‖ ≤ K * Real.exp (y ^ 2 / 2) := by
  obtain ⟨L, hL⟩ := heckeLambda_bdd_strip 5 7
  refine ⟨L ^ 2, fun x y hx => ?_⟩
  have hx' := abs_le.mp (hx.trans hc1)
  have h1 := hL (dp t (x + y * I)) (by simp [dp]; linarith) (by simp [dp]; linarith)
  have h2 := hL (dm t (x + y * I)) (by simp [dm]; linarith) (by simp [dm]; linarith)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans h1
  have he : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
  unfold PhiD; rw [norm_mul]
  calc ‖heckeLambda (dp t (↑x + ↑y * I))‖ * ‖heckeLambda (dm t (↑x + ↑y * I))‖ ≤ L * L := by gcongr
    _ = L ^ 2 * 1 := by ring
    _ ≤ _ := by gcongr

lemma not_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n h; rw [h] at hs; simp at hs; linarith [Nat.cast_nonneg (α := ℝ) n]

lemma heckeLambda_eq_gD {s : ℂ} (hs : 0 < s.re) : heckeLambda s = gD s * tauL s := by
  rw [heckeLambda_eq_tauL (not_neg_nat_of_re_pos hs)]; rfl

lemma gD_ne_zero {s : ℂ} (hs : 0 < s.re) : gD s ≠ 0 := by
  unfold gD
  exact mul_ne_zero (by rw [cpow_neg]; exact inv_ne_zero (two_pi_cpow_ne_zero s))
    (Gamma_ne_zero (not_neg_nat_of_re_pos hs))

lemma G0D_ne_zero (t : ℝ) : G0D t ≠ 0 :=
  mul_ne_zero (gD_ne_zero (by simp [dp])) (gD_ne_zero (by simp [dm]))

lemma dm_zero (t : ℝ) : dm t 0 = (starRingEnd ℂ) (6 + t * I) := by
  unfold dm; apply Complex.ext <;> simp

lemma PhiD_zero (t : ℝ) : PhiD t 0 = G0D t * ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold PhiD G0D
  rw [heckeLambda_eq_gD (by simp [dp]), heckeLambda_eq_gD (by simp [dm])]
  rw [show dp t 0 = 6 + t * I by unfold dp; ring, dm_zero, HeckeZeros.tauL_conj]
  have : tauL (6 + t * I) * (starRingEnd ℂ) (tauL (6 + t * I)) =
      ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

lemma norm_tC_div_cpow (n : ℕ) (s : ℂ) :
    ‖tC n / ((n : ℂ) + 1) ^ s‖ = |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-s.re) := by
  rw [div_eq_mul_one_div, norm_mul, norm_one_div_cpow]
  unfold tC; rw [show ((tau (n + 1) : ℤ) : ℂ) = (((tau (n + 1) : ℤ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- `Σ |τ(n+1)| (n+1)^{−σ}` converges for `σ > 13/2`. -/
lemma summable_abs_tau_shift {σ : ℝ} (hσ : 13 / 2 < σ) :
    Summable fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-σ) := by
  have h := (summable_nat_add_iff 1).mpr (HeckeConvex.summable_abs_tau_div_rpow hσ)
  refine h.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg (by positivity), div_eq_mul_inv]

lemma tauL_eq_tsum {s : ℂ} (hs : 13 / 2 < s.re) :
    tauL s = ∑' n : ℕ, tC n / ((n : ℂ) + 1) ^ s := by
  rw [HeckeConvex.tauL_eq_LSeries_of_gt hs, LSeries]
  have hsum : Summable (LSeries.term tauC s) := HeckeConvex.LSeriesSummable_tau_of_gt_13_2 hs
  rw [hsum.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  congr 1; funext n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  unfold tC tauC; push_cast; rfl

lemma re_dp (t c y : ℝ) : (dp t (c + y * I)).re = 6 + c := by simp [dp]
lemma re_dm (t c y : ℝ) : (dm t (c + y * I)).re = 6 + c := by simp [dm]

lemma norm_afeTermD (t c : ℝ) (p : ℕ × ℕ) (y : ℝ) :
    ‖afeTermD t c p y‖ = ‖RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)‖ *
      (|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-(6 + c)) *
        (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-(6 + c)))) := by
  unfold afeTermD
  rw [norm_mul, norm_mul, norm_tC_div_cpow, norm_tC_div_cpow, re_dp, re_dm]

/-- **The exact Δ-AFE for `|L(Δ,6+it)|²`.** -/
theorem afe_exact_delta {t c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1)
    (hRc : Continuous fun y : ℝ => RtD t (c + y * I)) {KR : ℝ}
    (hR : ∀ y : ℝ, ‖RtD t (c + y * I)‖ ≤ KR * Real.exp (y ^ 2 / 2)) :
    (Real.pi : ℂ) * ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ, ∫ y : ℝ, afeTermD t c p y := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK⟩ := norm_PhiD_le t hc1
  have hline := afe_line (differentiable_PhiD t) (PhiD_neg t) hc0 hK
  rw [PhiD_zero] at hline
  have hbase : Integrable fun y : ℝ =>
      RtD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) :=
    integrable_line_gauss hc0 hRc hR
  have hsum1 := summable_abs_tau_shift (σ := 6 + c) (by linarith)
  have hsumP : Summable fun p : ℕ × ℕ =>
      |((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-(6 + c)) *
        (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-(6 + c))) :=
    summable_mul_of_summable_norm
      (f := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(6 + c)))
      (g := fun n : ℕ => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(6 + c)))
      (by simpa [Real.norm_eq_abs] using hsum1.abs) (by simpa [Real.norm_eq_abs] using hsum1.abs)
  have hcpow : ∀ (n : ℕ) (f : ℝ → ℂ), Continuous f → Continuous fun y => tC n / ((n : ℂ) + 1) ^ f y := by
    intro n f hf
    refine continuous_const.div (Continuous.const_cpow hf (Or.inl ?_)) (fun y => ?_)
    · intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
    · rw [Ne, cpow_eq_zero_iff]; push_neg; intro h
      have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hint : ∀ p : ℕ × ℕ, Integrable (afeTermD t c p) := by
    intro p
    refine (hbase.norm.mul_const _).mono' ?_ (Eventually.of_forall fun y => (norm_afeTermD t c p y).le)
    refine Continuous.aestronglyMeasurable ?_
    unfold afeTermD
    refine Continuous.mul ?_ (Continuous.mul (hcpow p.1 _ (by unfold dp; fun_prop))
      (hcpow p.2 _ (by unfold dm; fun_prop)))
    exact (hRc.mul (by fun_prop)).div (by fun_prop) fun y => line_ne_zero hc0.ne' y
  have hsumI : Summable fun p : ℕ × ℕ => ∫ y : ℝ, ‖afeTermD t c p y‖ := by
    simp_rw [norm_afeTermD, integral_mul_const]
    exact hsumP.mul_left _
  rw [integral_tsum_of_summable_integral_norm hint hsumI]
  have hpt : ∀ y : ℝ, PhiD t (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) =
      G0D t * ∑' p : ℕ × ℕ, afeTermD t c p y := by
    intro y
    set z : ℂ := (c : ℂ) + y * I with hz
    have hre1 : 13 / 2 < (dp t z).re := by rw [hz, re_dp]; linarith
    have hre2 : 13 / 2 < (dm t z).re := by rw [hz, re_dm]; linarith
    have hzz : tauL (dp t z) * tauL (dm t z) =
        ∑' p : ℕ × ℕ, tC p.1 / ((p.1 : ℂ) + 1) ^ dp t z * (tC p.2 / ((p.2 : ℂ) + 1) ^ dm t z) := by
      rw [tauL_eq_tsum hre1, tauL_eq_tsum hre2]
      refine tsum_mul_tsum_of_summable_norm ?_ ?_
      · simp_rw [norm_tC_div_cpow]; rw [hz, re_dp]; exact hsum1
      · simp_rw [norm_tC_div_cpow]; rw [hz, re_dm]; exact hsum1
    unfold afeTermD
    rw [← hz, tsum_mul_left, ← hzz]
    unfold PhiD RtD
    rw [heckeLambda_eq_gD (by linarith), heckeLambda_eq_gD (by linarith)]
    have := G0D_ne_zero t
    field_simp
  simp_rw [hpt] at hline
  rw [integral_const_mul] at hline
  have hG := G0D_ne_zero t
  have : G0D t * ((Real.pi : ℂ) * ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ)) =
      G0D t * ∫ y : ℝ, ∑' p : ℕ × ℕ, afeTermD t c p y := by
    rw [hline]; ring
  exact mul_left_cancel₀ hG this

end RamanujanTau.GoodSecondTerm
