/-
# The Riesz kernel `φ_k(u) = (1 − u)_+^k` and its Mellin transform

`mellin φ_k s = P_k(s) = k! / (s (s+1) ⋯ (s+k))` for `Re s > 0` (`mellin_phi`), the bound
`‖P_k(s)‖ ≤ k! (2/m)^{k+1} (1 + |Im s|)^{-(k+1)}` for `Re s ≥ σ₁ > 0`, `m = min σ₁ 1`
(`norm_Pk_le`), and Mellin inversion `mellinInv σ P_k u = φ_k(u)` for `u > 0`, `k ≥ 1`
(`mellinInv_Pk`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Finset Filter Topology

/-- The Riesz kernel `φ_k(u) = (max (1 - u) 0)^k`. -/
noncomputable def phi (k : ℕ) (u : ℝ) : ℝ := (max (1 - u) 0) ^ k

/-- `P_k(s) = k! / ∏_{j=0}^{k} (s + j)`. -/
noncomputable def Pk (k : ℕ) (s : ℂ) : ℂ := (k.factorial : ℂ) / ∏ j ∈ range (k + 1), (s + j)

lemma phi_nonneg (k : ℕ) (u : ℝ) : 0 ≤ phi k u := pow_nonneg (le_max_right _ _) _

lemma phi_of_le {k : ℕ} {u : ℝ} (hu : u ≤ 1) : phi k u = (1 - u) ^ k := by
  rw [phi, max_eq_left (by linarith)]

lemma phi_of_gt {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 1 < u) : phi k u = 0 := by
  rw [phi, max_eq_right (by linarith), zero_pow (by omega)]

lemma continuous_phi (k : ℕ) : Continuous (phi k) := by
  unfold phi; fun_prop

lemma prod_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∏ j ∈ range (k + 1), (s + j) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro j _ h
  have := congrArg re h
  simp at this
  have : (0:ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma beta_eq_Pk (k : ℕ) : ∀ {s : ℂ}, 0 < s.re → betaIntegral s (k + 1) = Pk k s := by
  induction k with
  | zero =>
    intro s hs
    simp only [CharP.cast_eq_zero, zero_add]
    rw [betaIntegral_eval_one_right hs, Pk]
    simp
  | succ k ih =>
    intro s hs
    have hs1 : 0 < (s + 1).re := by simp; linarith
    have hv : 0 < ((k : ℂ) + 1).re := by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hrec := betaIntegral_recurrence hs hv
    rw [ih hs1] at hrec
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    push_cast
    have e : betaIntegral s ((k : ℂ) + 1 + 1) = ((k : ℂ) + 1) * Pk k (s + 1) / s := by
      field_simp; rw [mul_comm]; exact hrec
    rw [e, Pk, Pk, prod_range_succ' _ (k + 1)]
    have h1 := prod_ne_zero_of_re_pos hs1 k
    simp only [CharP.cast_eq_zero, add_zero]
    have e2 : ∏ j ∈ range (k + 1), (s + ((j + 1 : ℕ) : ℂ)) = ∏ j ∈ range (k + 1), (s + 1 + j) := by
      apply prod_congr rfl; intro j _; push_cast; ring
    rw [e2, Nat.factorial_succ]
    push_cast
    field_simp

lemma mellin_phi {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun u : ℝ => ((phi k u : ℝ) : ℂ)) s = Pk k s ∧
      MellinConvergent (fun u : ℝ => ((phi k u : ℝ) : ℂ)) s := by
  have hv : 0 < ((k : ℂ) + 1).re := by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hconv := betaIntegral_convergent hs hv
  set f : ℝ → ℂ := fun t : ℝ => (t : ℂ) ^ (s - 1) • ((phi k t : ℝ) : ℂ) with hf
  have heq : EqOn f
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ (((k : ℂ) + 1) - 1)) (Set.Ioc 0 1) := by
    intro t ht
    simp only [hf, smul_eq_mul]
    rw [phi_of_le ht.2, add_sub_cancel_right, cpow_natCast]
    push_cast; rfl
  have hint01 : IntegrableOn f (Set.Ioc 0 1) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hconv
    exact this.congr_fun heq.symm measurableSet_Ioc
  have hzero : EqOn f 0 (Set.Ioi 1) := by
    intro t ht
    simp only [hf, Pi.zero_apply, smul_eq_mul]
    rw [phi_of_gt hk ht]; simp
  have hint1 : IntegrableOn f (Set.Ioi 1) := (integrableOn_zero).congr_fun hzero.symm measurableSet_Ioi
  have hU : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hint : IntegrableOn f (Set.Ioi 0) := by rw [hU]; exact hint01.union hint1
  refine ⟨?_, hint⟩
  rw [mellin, ← hf, hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint01 hint1,
    setIntegral_congr_fun measurableSet_Ioi hzero]
  simp only [Pi.zero_apply, integral_zero, add_zero]
  rw [setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le zero_le_one]
  rw [← beta_eq_Pk k hs]
  rfl


lemma norm_add_nat_ge {s : ℂ} {σ₁ : ℝ} (h0 : 0 < σ₁) (hs : σ₁ ≤ s.re) (j : ℕ) :
    min σ₁ 1 * (1 + |s.im|) / 2 ≤ ‖s + j‖ := by
  have h1 : |(s + j).re| ≤ ‖s + j‖ := Complex.abs_re_le_norm _
  have h2 : |(s + j).im| ≤ ‖s + j‖ := Complex.abs_im_le_norm _
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero] at h1 h2
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hre : σ₁ ≤ |s.re + j| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hm1 : min σ₁ 1 ≤ σ₁ := min_le_left _ _
  have hm2 : min σ₁ 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 < min σ₁ 1 := lt_min h0 one_pos
  have : min σ₁ 1 * |s.im| ≤ |s.im| := by
    have := abs_nonneg s.im; nlinarith
  nlinarith

lemma norm_Pk_le (k : ℕ) {s : ℂ} {σ₁ : ℝ} (h0 : 0 < σ₁) (hs : σ₁ ≤ s.re) :
    ‖Pk k s‖ ≤ k.factorial * (2 / min σ₁ 1) ^ (k + 1) / (1 + |s.im|) ^ (k + 1) := by
  have hm0 : 0 < min σ₁ 1 := lt_min h0 one_pos
  set b : ℝ := min σ₁ 1 * (1 + |s.im|) / 2 with hb
  have hb0 : 0 < b := by positivity
  have hprod : b ^ (k + 1) ≤ ∏ j ∈ range (k + 1), ‖s + j‖ := by
    have : b ^ (k + 1) = ∏ _j ∈ range (k + 1), b := by rw [prod_const, card_range]
    rw [this]
    exact prod_le_prod (fun _ _ => hb0.le) (fun j _ => norm_add_nat_ge h0 hs j)
  rw [Pk, norm_div, norm_prod, Complex.norm_natCast]
  calc (k.factorial : ℝ) / ∏ j ∈ range (k + 1), ‖s + j‖ ≤ k.factorial / b ^ (k + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = k.factorial * (2 / min σ₁ 1) ^ (k + 1) / (1 + |s.im|) ^ (k + 1) := by
        have hm : min σ₁ 1 ≠ 0 := hm0.ne'
        rw [hb, div_pow, mul_pow, div_pow]; field_simp

/-- A continuous function bounded by `C/(1+|y|)²` is integrable. -/
lemma integrable_of_le_div_sq {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (h : ∀ y, ‖g y‖ ≤ C / (1 + |y|) ^ 2) : Integrable g := by
  have hi : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-(2:ℝ))) :=
    (integrable_one_add_norm (by simp)).const_mul C
  refine hi.mono' hg.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.rpow_neg (by positivity), Real.norm_eq_abs, ← div_eq_mul_inv]
  exact_mod_cast h y

lemma continuous_Pk_line (k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun y : ℝ => Pk k (σ + y * I) := by
  unfold Pk
  refine Continuous.div continuous_const (by fun_prop) (fun y => prod_ne_zero_of_re_pos ?_ k)
  simpa using hσ

lemma Pk_line_le (k : ℕ) {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    ‖Pk k (σ + y * I)‖ ≤ k.factorial * (2 / min σ 1) ^ (k + 1) / (1 + |y|) ^ (k + 1) := by
  have := norm_Pk_le k hσ (s := σ + y * I) (by simp)
  simpa using this

lemma integrable_Pk_line {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun y : ℝ => Pk k (σ + y * I) := by
  refine integrable_of_le_div_sq (continuous_Pk_line k hσ)
    (C := k.factorial * (2 / min σ 1) ^ (k + 1)) (fun y => ?_)
  refine (Pk_line_le k hσ y).trans ?_
  have h1 : (1:ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ (k + 1) := pow_le_pow_right₀ h1 (by omega)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) this

/-- Mellin inversion for the Riesz kernel. -/
theorem mellinInv_Pk {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 < σ) {u : ℝ} (hu : 0 < u) :
    mellinInv σ (Pk k) u = (phi k u : ℂ) := by
  have hline : ∀ y : ℝ, mellin (fun u : ℝ => ((phi k u : ℝ) : ℂ)) (σ + y * I) = Pk k (σ + y * I) :=
    fun y => (mellin_phi hk (s := σ + y * I) (by simpa using hσ)).1
  have hconv : MellinConvergent (fun u : ℝ => ((phi k u : ℝ) : ℂ)) σ :=
    (mellin_phi hk (s := σ) (by simpa using hσ)).2
  have hvi : VerticalIntegrable (mellin fun u : ℝ => ((phi k u : ℝ) : ℂ)) σ := by
    unfold VerticalIntegrable
    simp_rw [hline]
    exact integrable_Pk_line hk hσ
  have hcont : ContinuousAt (fun u : ℝ => ((phi k u : ℝ) : ℂ)) u :=
    (continuous_ofReal.comp (continuous_phi k)).continuousAt
  have := mellinInv_mellin_eq σ _ hu hconv hvi hcont
  rw [← this]
  unfold mellinInv
  simp_rw [hline]

end RamanujanTau.RankinError
