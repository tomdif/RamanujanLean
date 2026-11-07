/-
# The dual expansion, part B: the exact Voronoi-type formula for the Riesz mean

For `RSDataM m a κ` (`m ≥ 2`) and any `b ≥ 0` with `∑ bₙ n^{−w} = ζ(2w) ∑ aₙ n^{−w}` (`Re w > 2`),
for `k ≥ 18` and `x ≥ 1`:

    W_k(x) = ∑_{n ≤ x} bₙ (x−n)^k = (Ψ(1) − Ψ(0)) x^k + ∑ₙ bₙ n^{−1−k} J_k^{(1/2)}(n x)

(`dual_rep`), where `Ψ(1) = κ R_k(1) x` and `Ψ(0) = κ R_k(0)`. Proof:

1. Perron on `Re s = 5/2` (`RankinError.perron_riesz`), integrand `= Φ` (`Phi_eq_right`);
2. `Φ = H + Ψ(1)u₁ − Ψ(0)u₀` on both lines, `H` holomorphic with `‖H‖ ≪ (1+|t|)^{−2}`, so
   `∫_{5/2} H = ∫_{−3/2} H` (`Stirling.integral_line_eq_rpow`);
3. `∫ u` over the lines by `integral_inv_sub_line` (the residues `Ψ(1)`, `−Ψ(0)`);
4. on `Re s = −3/2`, `Φ(s) = x^s Q_k(s) ∑ bₙ n^{s−1}` (`Phi_eq_left` + functional equation), and
   the sum and the integral are exchanged (`integral_tsum_of_summable_integral_norm`);
5. `J_k^{(−3/2)} = J_k^{(1/2)}` (`Jc_shift`).
-/
import RamanujanTau.RankinLandau.DualA
import RamanujanTau.RankinError.PerronShift
import RamanujanTau.RankinSharp.Sharp

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral

lemma u1_line (σ t : ℝ) : u1 ((σ : ℂ) + t * I) =
    1 / (((σ - 1 : ℝ) : ℂ) + t * I) - 1 / (((σ + 2 : ℝ) : ℂ) + t * I) := by
  unfold u1
  rw [show (σ : ℂ) + t * I - 1 = ((σ - 1 : ℝ) : ℂ) + t * I by push_cast; ring,
    show (σ : ℂ) + t * I + 2 = ((σ + 2 : ℝ) : ℂ) + t * I by push_cast; ring]

lemma u0_line (σ t : ℝ) : u0 ((σ : ℂ) + t * I) =
    1 / ((σ : ℂ) + t * I) - 1 / (((σ + 2 : ℝ) : ℂ) + t * I) := by
  unfold u0
  rw [show (σ : ℂ) + t * I + 2 = ((σ + 2 : ℝ) : ℂ) + t * I by push_cast; ring]

lemma integral_u1 (σ : ℝ) (h1 : σ - 1 ≠ 0) (h2 : σ + 2 ≠ 0) :
    ∫ t : ℝ, u1 ((σ : ℂ) + t * I) = (π * ((σ - 1) / |σ - 1| - (σ + 2) / |σ + 2|) : ℝ) := by
  simp_rw [u1_line]; exact integral_inv_sub_line h1 h2

lemma integral_u0 (σ : ℝ) (h1 : σ ≠ 0) (h2 : σ + 2 ≠ 0) :
    ∫ t : ℝ, u0 ((σ : ℂ) + t * I) = (π * (σ / |σ| - (σ + 2) / |σ + 2|) : ℝ) := by
  simp_rw [u0_line]; exact integral_inv_sub_line h1 h2

lemma integrable_u1 (σ : ℝ) (h1 : σ - 1 ≠ 0) (h2 : σ + 2 ≠ 0) :
    Integrable fun t : ℝ => u1 ((σ : ℂ) + t * I) := by
  simp_rw [u1_line]; exact integrable_inv_sub_line h1 h2

lemma integrable_u0 (σ : ℝ) (h1 : σ ≠ 0) (h2 : σ + 2 ≠ 0) :
    Integrable fun t : ℝ => u0 ((σ : ℂ) + t * I) := by
  simp_rw [u0_line]; exact integrable_inv_sub_line h1 h2

/-- `∫ y^{σ+it} Q_k(σ+it) dt = 2π y^{−k} J_k^{(σ)}(y)`. -/
lemma integral_cpow_Qk (m k : ℕ) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Qk m k (σ + t * I) =
      (2 * π : ℂ) * ((y : ℂ) ^ k)⁻¹ * Jc m k σ y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hyk : (y : ℂ) ^ k ≠ 0 := pow_ne_zero _ hy0
  have e : ∀ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I + k) * Qk m k (σ + t * I) =
      (y : ℂ) ^ k * ((y : ℂ) ^ ((σ : ℂ) + t * I) * Qk m k (σ + t * I)) := by
    intro t; rw [Complex.cpow_add _ _ hy0, Complex.cpow_natCast]; ring
  unfold Jc
  simp_rw [e]
  rw [integral_const_mul]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  set Iv := ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Qk m k (σ + t * I) with hIv
  push_cast
  field_simp

section Rep

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ) (k : ℕ)

/-- **The dual series on the left line** `Re s = −3/2`. -/
theorem left_line_tsum (hm : 2 ≤ m) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hb0 : b 0 = 0)
    (hbL : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => (b n : ℂ)) w = riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w)
    (hbS : LSeriesSummable (fun n => (b n : ℂ)) ((5 / 2 : ℝ) : ℂ))
    (hk : 18 ≤ k) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, Phi d k x (((-3 / 2 : ℝ) : ℂ) + t * I) =
      ∑' n : ℕ, ((b n / n : ℝ) : ℂ) * ((2 * π : ℂ) * ((((n : ℝ) * x : ℝ) : ℂ) ^ k)⁻¹ *
        Jc m k (-3 / 2) (n * x)) := by
  have hm1 : 1 ≤ m := by omega
  have hk8 : 1 - 4 * (-3 / 2 : ℝ) - k < -1 := by
    have : (18 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set s : ℝ → ℂ := fun t => ((-3 / 2 : ℝ) : ℂ) + t * I with hs
  have hsre : ∀ t, (s t).re = -3 / 2 := fun t => by simp [hs]
  have h1re : ∀ t, (1 - s t).re = 5 / 2 := fun t => by simp [hs]; norm_num
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- integrability of `Q_k` on the line
  have hQint : Integrable fun t : ℝ => Qk m k (s t) := by
    have := integrable_jint m k hm1 (σ := -3 / 2) (by norm_num) hk8 (y := 1) one_pos
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [jint, hs]
  -- the terms
  set F : ℕ → ℝ → ℂ := fun n t =>
    (x : ℂ) ^ (s t) * Qk m k (s t) * LSeries.term (fun n => (b n : ℂ)) (1 - s t) n with hF
  have hterm_norm : ∀ n t, ‖LSeries.term (fun n => (b n : ℂ)) (1 - s t) n‖ =
      ‖LSeries.term (fun n => (b n : ℂ)) ((5 / 2 : ℝ) : ℂ) n‖ := by
    intro n t; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, h1re]; simp
  have hFnorm : ∀ n t, ‖F n t‖ = x ^ (-3 / 2 : ℝ) *
      ‖LSeries.term (fun n => (b n : ℂ)) ((5 / 2 : ℝ) : ℂ) n‖ * ‖Qk m k (s t)‖ := by
    intro n t
    simp only [hF]
    rw [norm_mul, norm_mul, hterm_norm, Complex.norm_cpow_eq_rpow_re_of_pos hx, hsre]; ring
  have hcont_term : ∀ n, Continuous fun t => LSeries.term (fun n => (b n : ℂ)) (1 - s t) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]; exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      refine continuous_const.div (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
        (fun t => Complex.cpow_ne_zero_iff.2 (Or.inl hn0))
  have hcontQ : Continuous fun t : ℝ => Qk m k (s t) :=
    (differentiableOn_Qk m k).continuousOn.comp_continuous (by fun_prop)
      (fun t => by simp only [mem_setOf_eq, hsre]; norm_num)
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have hc : Continuous (F n) := by
      simp only [hF]
      exact ((Continuous.const_cpow (by fun_prop) (Or.inl hx0)).mul hcontQ).mul
        (hcont_term n)
    refine (hQint.norm.const_mul (x ^ (-3 / 2 : ℝ) *
      ‖LSeries.term (fun n => (b n : ℂ)) ((5 / 2 : ℝ) : ℂ) n‖)).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [hFnorm]
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hFnorm, integral_const_mul]
    exact ((hbS.norm.mul_left (x ^ (-3 / 2 : ℝ))).mul_right _)
  have key := integral_tsum_of_summable_integral_norm hFint hFsum
  -- `Φ = ∑ F n` on the line
  have hPhi : ∀ t, Phi d k x (s t) = ∑' n, F n t := by
    intro t
    rw [Phi_eq_left d k x (by rw [hsre]; norm_num), ← hbL _ (by rw [h1re]; norm_num)]
    simp only [hF]
    rw [LSeries, tsum_mul_left]
  simp_rw [show ∀ t : ℝ, ((-3 / 2 : ℝ) : ℂ) + t * I = s t from fun t => rfl, hPhi]
  rw [← key]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hF, LSeries.term_zero, hb0]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnx : (0 : ℝ) < n * x := by positivity
    have e : ∀ t, F n t = ((b n / n : ℝ) : ℂ) *
        ((((n : ℝ) * x : ℝ) : ℂ) ^ ((((-3 / 2 : ℝ) : ℂ)) + t * I) * Qk m k (((-3 / 2 : ℝ) : ℂ) + t * I)) := by
      intro t
      simp only [hF, hs, LSeries.term_of_ne_zero hn]
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn0.le hx.le,
        Complex.cpow_sub _ _ hnc, Complex.cpow_one]
      have h1 : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
      rw [h1]
      have h2 : (n : ℂ) ^ (((-3 / 2 : ℝ) : ℂ) + t * I) ≠ 0 :=
        Complex.cpow_ne_zero_iff.2 (Or.inl hnc)
      push_cast
      field_simp
    simp_rw [e]
    rw [integral_const_mul, integral_cpow_Qk m k (-3 / 2) hnx]

/-- **The exact dual expansion of the Riesz mean** (complex form). -/
theorem dual_rep (hm : 2 ≤ m) (hsumA : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ))
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hb0 : b 0 = 0)
    (hbL : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => (b n : ℂ)) w = riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w)
    (hbS : LSeriesSummable (fun n => (b n : ℂ)) ((5 / 2 : ℝ) : ℂ))
    (hk : 18 ≤ k) {x : ℝ} (hx1 : 1 ≤ x) :
    ((W b k x : ℝ) : ℂ) = (Psi d k x 1 - Psi d k x 0) * (x : ℂ) ^ k +
      ∑' n : ℕ, ((b n / (n : ℝ) ^ (k + 1) : ℝ) : ℂ) * Jc m k (1 / 2) (n * x) := by
  have hx : 0 < x := by linarith
  have hm1 : 1 ≤ m := by omega
  have hk1 : 1 ≤ k := by omega
  have hk8 : 1 - 4 * (-3 / 2 : ℝ) - k < -1 := by
    have : (18 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsumB : Summable fun n : ℕ => b n * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
    RamanujanTau.RankinSharp.summable_of_LSeriesSummable hb hb0 hbS
  have hP := perron_riesz b hb hb0 hk1 (c := 5 / 2) (by norm_num) hx hsumB
  -- the Perron integrand is `Φ`
  have e1 : ∀ y : ℝ, (x : ℂ) ^ ln (5 / 2) y * Pk k (ln (5 / 2) y) *
      LSeries (fun n => (b n : ℂ)) (ln (5 / 2) y) = Phi d k x (((5 / 2 : ℝ) : ℂ) + y * I) := by
    intro y
    have hre : 2 < (ln (5 / 2) y).re := by simp [ln]; norm_num
    rw [hbL _ hre, Phi_eq_right d k x hre]
  simp_rw [e1] at hP
  -- `Φ = H + Ψ(1)u₁ − Ψ(0)u₀` on the two lines
  have hdec : ∀ σ : ℝ, (σ = 5 / 2 ∨ σ = -3 / 2) → ∀ t : ℝ,
      Phi d k x ((σ : ℂ) + t * I) = Hfun d k x ((σ : ℂ) + t * I) +
        Psi d k x 1 * u1 ((σ : ℂ) + t * I) - Psi d k x 0 * u0 ((σ : ℂ) + t * I) := by
    intro σ hσ t
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have h0 : (σ : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this
      rcases hσ with rfl | rfl <;> norm_num at this
    have h1 : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this
      rcases hσ with rfl | rfl <;> norm_num at this
    have h2 : (σ : ℂ) + t * I + 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      rcases hσ with rfl | rfl <;> norm_num at this
    rw [Hfun_eq d k x hx h0 h1 h2]; ring
  obtain ⟨CH, hCH⟩ := H_bound d k x hx hx1 hk hm hsumA
  have hHc : ContinuousOn (Hfun d k x) {s : ℂ | -3 / 2 ≤ s.re ∧ s.re ≤ 5 / 2} :=
    (differentiableOn_Hfun d k x hx).continuousOn.mono (fun s hs => by
      simp only [mem_setOf_eq] at hs ⊢; linarith [hs.1])
  have hHint : ∀ σ : ℝ, -3 / 2 ≤ σ → σ ≤ 5 / 2 →
      Integrable fun t : ℝ => Hfun d k x ((σ : ℂ) + t * I) := fun σ h1 h2 =>
    Stirling.integrable_line_of_strip_rpow (p := 2) (by norm_num) hHc
      (fun s h1 h2 => hCH s h1 h2) h1 h2
  have hshift : ∫ t : ℝ, Hfun d k x (((5 / 2 : ℝ) : ℂ) + t * I) =
      ∫ t : ℝ, Hfun d k x (((-3 / 2 : ℝ) : ℂ) + t * I) :=
    Stirling.integral_line_eq_rpow (p := 2) (by norm_num) (by norm_num)
      ((differentiableOn_Hfun d k x hx).mono (fun s hs => by
        simp only [mem_setOf_eq] at hs ⊢; linarith [hs.1])) (fun s h1 h2 => hCH s h1 h2)
  have hlineint : ∀ σ : ℝ, (σ = 5 / 2 ∨ σ = -3 / 2) →
      ∫ t : ℝ, Phi d k x ((σ : ℂ) + t * I) = (∫ t : ℝ, Hfun d k x ((σ : ℂ) + t * I)) +
        Psi d k x 1 * (∫ t : ℝ, u1 ((σ : ℂ) + t * I)) -
        Psi d k x 0 * (∫ t : ℝ, u0 ((σ : ℂ) + t * I)) := by
    intro σ hσ
    have hs1 : σ - 1 ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hs2 : σ + 2 ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hs0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hσ1 : -3 / 2 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
    have hσ2 : σ ≤ 5 / 2 := by rcases hσ with rfl | rfl <;> norm_num
    simp_rw [hdec σ hσ]
    have iA := hHint σ hσ1 hσ2
    have iB := (integrable_u1 σ hs1 hs2).const_mul (Psi d k x 1)
    have iC := (integrable_u0 σ hs0 hs2).const_mul (Psi d k x 0)
    have iAB : Integrable (fun t : ℝ => Hfun d k x ((σ : ℂ) + t * I) +
        Psi d k x 1 * u1 ((σ : ℂ) + t * I)) := iA.add iB
    rw [integral_sub iAB iC, integral_add iA iB, integral_const_mul, integral_const_mul]
  have hc := hlineint (5 / 2) (Or.inl rfl)
  have hl := hlineint (-3 / 2) (Or.inr rfl)
  have iu1c : ∫ t : ℝ, u1 (((5 / 2 : ℝ) : ℂ) + t * I) = 0 := by
    rw [integral_u1 _ (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have iu0c : ∫ t : ℝ, u0 (((5 / 2 : ℝ) : ℂ) + t * I) = 0 := by
    rw [integral_u0 _ (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have iu1l : ∫ t : ℝ, u1 (((-3 / 2 : ℝ) : ℂ) + t * I) = -(2 * π) := by
    rw [integral_u1 _ (by norm_num) (by norm_num)]; push_cast; norm_num [abs_of_pos, abs_of_neg]
    ring
  have iu0l : ∫ t : ℝ, u0 (((-3 / 2 : ℝ) : ℂ) + t * I) = -(2 * π) := by
    rw [integral_u0 _ (by norm_num) (by norm_num)]; push_cast; norm_num [abs_of_pos, abs_of_neg]
    ring
  rw [iu1c, iu0c] at hc
  rw [iu1l, iu0l, left_line_tsum d k hm b hb hb0 hbL hbS hk hx] at hl
  -- assemble
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  set T : ℂ := ∑' n : ℕ, ((b n / n : ℝ) : ℂ) * ((((n : ℝ) * x : ℝ) : ℂ) ^ k)⁻¹ *
    Jc m k (-3 / 2) (n * x) with hT
  have hT' : ∑' n : ℕ, ((b n / n : ℝ) : ℂ) * ((2 * π : ℂ) * ((((n : ℝ) * x : ℝ) : ℂ) ^ k)⁻¹ *
      Jc m k (-3 / 2) (n * x)) = (2 * π : ℂ) * T := by
    rw [hT, ← tsum_mul_left]; congr 1; funext n; ring
  rw [hT'] at hl
  have hsumφ : ∑' n : ℕ, (b n : ℂ) * (phi k (n / x) : ℂ) = Psi d k x 1 - Psi d k x 0 + T := by
    have : (2 * π : ℂ) * ∑' n : ℕ, (b n : ℂ) * (phi k (n / x) : ℂ) =
        (2 * π : ℂ) * (Psi d k x 1 - Psi d k x 0 + T) := by
      rw [hP, hc, hshift]
      linear_combination -hl
    exact mul_left_cancel₀ hπ this
  rw [W_eq_tsum b hb0 hk1 hx]
  push_cast
  rw [hsumφ, mul_add, hT, ← tsum_mul_left]
  rw [mul_comm ((x : ℂ) ^ k)]
  congr 1
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hb0]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnx : (0 : ℝ) < n * x := by positivity
    rw [Jc_shift m k hm1 hk8 (σ₁ := -3 / 2) (σ₂ := 1 / 2) le_rfl (by norm_num) (by norm_num)
      (by norm_num) hnx]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
    ring

end Rep

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.left_line_tsum
#print axioms RamanujanTau.RankinLandau.dual_rep
