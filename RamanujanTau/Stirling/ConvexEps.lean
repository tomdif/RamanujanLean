/-
# The convexity bound with strip edges `−ε` and `1+ε`

For the weight-`(m+1)` Rankin–Selberg function `E(s) = (s−1)ζ(2s)D(s)` (`RankinSharpGeneral`),
put `b = 3 + 2ε` and

    f_ε(s) = E(s) Γ(s+1) / (Γ(b−s)(s+3)).

* Right edge `Re s = 1+ε`: `b − s = conj(s+1)`, so the `Γ`-ratio has modulus `1`, and `D`
  converges absolutely.
* Left edge `Re s = −ε` (`ratioEps_le`): with `v = 1 − s`, the functional equation gives a
  `Γ`-ratio whose real parts differ by **non-integers** (`2ε`, `1−2ε`). Here the new
  `Stirling.norm_Gamma_mul_rpow_le` does the work: `‖Γ(v)‖² ‖v‖ ≤ e²⁰ ‖s+1‖ ‖s‖ ‖Γ(s)‖ ‖Γ(v+2ε)‖`.
  The rest is a degree-`(m+2)`/degree-`(m+2)` rational function of bounded size.
* Phragmén–Lindelöf on `[−ε, 1+ε]` bounds `f_ε` (`fEps_bound`).
* On each line `0 ≤ Re s = σ ≤ 1+ε`, `Γ(b−s) = Γ(conj(s+1) + θ)` with `θ = 2+2ε−2σ` real, so
  `Stirling.norm_Gamma_add_le` gives `‖E(s)‖ ≤ C ‖s+3‖^{3+2ε−2σ}` (`Efun_line_eps`), the
  convexity bound, and `Efun_bound_eps` makes it uniform on `σ₁ ≤ Re s ≤ 5/2`.
-/
import RamanujanTau.Stirling.GammaRatio
import RamanujanTau.RankinSharpGeneral.Convex

set_option autoImplicit false

namespace RamanujanTau.Stirling

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinSharp (pl_strip norm_prod_ge LSeriesSummable_of_one_lt)

/-- The left-edge constant. -/
noncomputable def RL (m : ℕ) : ℝ := Real.exp 20 * 6 * ((m : ℝ) + 1) ^ m * 3 ^ m

lemma RL_nonneg (m : ℕ) : 0 ≤ RL m := by unfold RL; positivity

lemma exists_norm_zeta_le2 : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ w : ℂ, 2 ≤ w.re → ‖riemannZeta w‖ ≤ Z := by
  have h1 : LSeriesSummable 1 ((2 : ℝ) : ℂ) := LSeriesSummable_one_iff.2 (by simp)
  refine ⟨∑' n, ‖LSeries.term 1 ((2 : ℝ) : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _,
    fun w hw => ?_⟩
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  exact norm_LSeries_le h1 (by simpa using hw)

/-- **The left-edge `Γ`-ratio** on `Re s = −ε`, `0 < ε ≤ 1/2`, weight `m + 1 ≥ 2`. -/
theorem ratioEps_le {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {s : ℂ}
    (hs : s.re = -ε) :
    ‖(s - 1) * gamM m (1 - s) * invGamM m s * Complex.Gamma (s + 1) *
      (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3)‖ ≤ RL m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set v : ℂ := 1 - s with hv
  set t : ℝ := s.im with ht
  have hvre : v.re = 1 + ε := by rw [hv]; simp [hs]
  have hvim : v.im = -t := by rw [hv]; simp [ht]
  have hv0 : 0 < v.re := by rw [hvre]; linarith
  have hv1 : 1 ≤ v.re := by rw [hvre]; linarith
  set V : ℝ := ‖v‖ with hV
  have hV1 : 1 ≤ V := one_le_norm_of_re hv1
  have hVsq : V ^ 2 = (1 + ε) ^ 2 + t ^ 2 := by rw [hV, sq_norm_eq, hvre, hvim]; ring
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1re : 0 < (s + 1).re := by simp [hs]; linarith
  -- the `Γ` identities
  set w2 : ℂ := v + ((2 * ε : ℝ) : ℂ) with hw2
  have hw2re : 0 < w2.re := by rw [hw2]; simp [hvre]; linarith
  have Gm : Complex.Gamma (1 - s + ((m' + 1 : ℕ) : ℂ)) =
      (∏ j ∈ Finset.range (m' + 1), (v + j)) * Complex.Gamma v := by
    rw [← Gamma_add_nat hv0 (m' + 1)]
  have Gs1 : Complex.Gamma (s + 1) = s * Complex.Gamma s := Complex.Gamma_add_one s hs0
  have Gsm : Complex.Gamma (s + ((m' + 1 : ℕ) : ℂ)) =
      (∏ j ∈ Finset.range m', (s + 1 + j)) * (s * Complex.Gamma s) := by
    rw [← Gs1, ← Gamma_add_nat hs1re m']; congr 1; push_cast; ring
  have Gb : Complex.Gamma (3 + 2 * ε - s) =
      (∏ j ∈ Finset.range 2, (w2 + j)) * Complex.Gamma w2 := by
    rw [← Gamma_add_nat hw2re 2]; congr 1; rw [hw2, hv]; push_cast; ring
  have hGs : Complex.Gamma s ≠ 0 := by
    intro h; have := Complex.Gamma_ne_zero_of_re_pos hs1re; rw [Gs1, h, mul_zero] at this
    exact this rfl
  have hGv : Complex.Gamma v ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv0
  have hGw : Complex.Gamma w2 ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw2re
  have hPs : ∏ j ∈ Finset.range m', (s + 1 + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _ h; have := congrArg re h; simp [hs] at this
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hP2 : ∏ j ∈ Finset.range 2, (w2 + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _ h; have := congrArg re h; simp at this
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hs3 : s + 3 ≠ 0 := by intro h; have := congrArg re h; simp [hs] at this; linarith
  -- the π-factors
  have hpi : ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ ≤ 1 := by
    rw [norm_mul, show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π Real.pi_pos,
      norm_cpow_pos π Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; linarith
  have h4pi : ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - ((m' + 1 : ℕ) : ℂ)) *
      ((4 * π : ℝ) : ℂ) ^ (s + ((m' + 1 : ℕ) : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_pos _ (by positivity), norm_cpow_pos _ (by positivity),
      ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    simp [hs]; linarith
  have hsplit : (s - 1) * gamM (m' + 1) (1 - s) * invGamM (m' + 1) s * Complex.Gamma (s + 1) *
      (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3) =
      ((π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s) *
      (((4 * π : ℝ) : ℂ) ^ (-(1 - s) - ((m' + 1 : ℕ) : ℂ)) *
        ((4 * π : ℝ) : ℂ) ^ (s + ((m' + 1 : ℕ) : ℂ))) *
      ((s - 1) * Complex.Gamma (1 - s) * Complex.Gamma (1 - s + ((m' + 1 : ℕ) : ℂ)) *
        (Complex.Gamma s)⁻¹ * (Complex.Gamma (s + ((m' + 1 : ℕ) : ℂ)))⁻¹ *
        Complex.Gamma (s + 1) * (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3)) := by
    unfold gamM invGamM; ring
  have hY : (s - 1) * Complex.Gamma (1 - s) * Complex.Gamma (1 - s + ((m' + 1 : ℕ) : ℂ)) *
        (Complex.Gamma s)⁻¹ * (Complex.Gamma (s + ((m' + 1 : ℕ) : ℂ)))⁻¹ *
        Complex.Gamma (s + 1) * (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3) =
      ((s - 1) * (∏ j ∈ Finset.range (m' + 1), (v + j)) * Complex.Gamma v ^ 2) /
        ((∏ j ∈ Finset.range m', (s + 1 + j)) * Complex.Gamma s *
          (∏ j ∈ Finset.range 2, (w2 + j)) * Complex.Gamma w2 * (s + 3)) := by
    rw [Gm, Gsm, Gb, Gs1, show 1 - s = v from rfl]
    field_simp
  rw [hsplit, hY]
  generalize (π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s = P at hpi ⊢
  generalize ((4 * π : ℝ) : ℂ) ^ (-(1 - s) - ((m' + 1 : ℕ) : ℂ)) *
    ((4 * π : ℝ) : ℂ) ^ (s + ((m' + 1 : ℕ) : ℂ)) = Q at h4pi ⊢
  rw [norm_mul, norm_mul]
  -- the key `Γ` inequality
  have I1 := norm_Gamma_mul_rpow_le hv1 (θ := 2 * ε) (by linarith) (by linarith)
  have hcv1 : 1 ≤ (starRingEnd ℂ v).re := by simpa using hv1
  have I2 := norm_Gamma_mul_rpow_le hcv1 (θ := 1 - 2 * ε) (by linarith) (by linarith)
  have e2 : starRingEnd ℂ v + ((1 - 2 * ε : ℝ) : ℂ) = (s + 1) + 1 := by
    apply Complex.ext <;> simp [hv, hs] <;> ring
  rw [e2, Complex.Gamma_add_one _ (by intro h; have := congrArg re h; simp [hs] at this; linarith),
    Gs1, norm_Gamma_conj, Complex.norm_conj, norm_mul, norm_mul] at I2
  have I12 : ‖Complex.Gamma v‖ ^ 2 * V ≤
      Real.exp 20 * (‖s + 1‖ * ‖s‖ * ‖Complex.Gamma s‖ * ‖Complex.Gamma w2‖) := by
    have hVsplit : V = V ^ (2 * ε) * V ^ (1 - 2 * ε) := by
      rw [← Real.rpow_add (by linarith), show 2 * ε + (1 - 2 * ε) = 1 by ring, Real.rpow_one]
    have e20 : Real.exp 20 = Real.exp 10 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
    calc ‖Complex.Gamma v‖ ^ 2 * V
        = ‖Complex.Gamma v‖ ^ 2 * (V ^ (2 * ε) * V ^ (1 - 2 * ε)) := by rw [← hVsplit]
      _ = (‖Complex.Gamma v‖ * V ^ (2 * ε)) * (‖Complex.Gamma v‖ * V ^ (1 - 2 * ε)) := by ring
      _ ≤ (Real.exp 10 * ‖Complex.Gamma w2‖) *
          (Real.exp 10 * (‖s + 1‖ * (‖s‖ * ‖Complex.Gamma s‖))) :=
          mul_le_mul I1 I2 (by positivity) (by positivity)
      _ = _ := by rw [e20]; ring
  -- norms of the rational factors
  have hsv : s = 1 - v := by rw [hv]; ring
  have n1 : ‖s - 1‖ = V := by rw [hsv, show 1 - v - 1 = -v by ring, norm_neg]
  have n2 : ‖s‖ ≤ 2 * V := by
    rw [hsv]; refine (norm_sub_le _ _).trans ?_; rw [norm_one]; linarith
  have n3 : ‖s + 1‖ ≤ 3 * V := by
    rw [hsv, show 1 - v + 1 = 2 - v by ring]; refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_two]; linarith
  have n4 : ‖∏ j ∈ Finset.range (m' + 1), (v + j)‖ ≤ (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) *
      V ^ (m' + 1) := by
    refine (norm_prod_le_pow (u := v) (m' + 1)).trans ?_
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ ((m' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have n5 : (V / 3) ^ m' ≤ ‖∏ j ∈ Finset.range m', (s + 1 + j)‖ := by
    rw [norm_prod]
    have : (V / 3) ^ m' = ∏ _j ∈ Finset.range m', V / 3 := by
      rw [Finset.prod_const, Finset.card_range]
    rw [this]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j _
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), sq_norm_eq, div_pow, hVsq]
    simp [hs, ht]
    nlinarith
  have n6 : V ^ 2 ≤ ‖∏ j ∈ Finset.range 2, (w2 + j)‖ := by
    refine le_trans ?_ (norm_prod_ge hw2re.le 2)
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by rw [hw2]; exact norm_le_norm_add_ofReal hv0.le (by linarith)) 2
  have n7 : V ≤ ‖s + 3‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hVsq, sq_norm_eq]
    simp [hs, ht]; nlinarith
  -- assemble
  set Gv := ‖Complex.Gamma v‖
  set Gs := ‖Complex.Gamma s‖
  set Gw := ‖Complex.Gamma w2‖
  have hGs0 : 0 < Gs := norm_pos_iff.2 hGs
  have hGw0 : 0 < Gw := norm_pos_iff.2 hGw
  have hV0 : 0 < V := by linarith
  have hden : 0 < ‖(∏ j ∈ Finset.range m', (s + 1 + j)) * Complex.Gamma s *
      (∏ j ∈ Finset.range 2, (w2 + j)) * Complex.Gamma w2 * (s + 3)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hPs hGs) hP2) hGw) hs3
  have hfrac : ‖((s - 1) * (∏ j ∈ Finset.range (m' + 1), (v + j)) * Complex.Gamma v ^ 2) /
        ((∏ j ∈ Finset.range m', (s + 1 + j)) * Complex.Gamma s *
          (∏ j ∈ Finset.range 2, (w2 + j)) * Complex.Gamma w2 * (s + 3))‖ ≤ RL (m' + 1) := by
    rw [norm_div, div_le_iff₀ hden]
    simp only [norm_mul, norm_pow]
    rw [n1]
    set Pv := ‖∏ j ∈ Finset.range (m' + 1), (v + j)‖
    set Ps := ‖∏ j ∈ Finset.range m', (s + 1 + j)‖
    set P2 := ‖∏ j ∈ Finset.range 2, (w2 + j)‖
    have hPv0 : 0 ≤ Pv := norm_nonneg _
    have hc0 : (0:ℝ) ≤ (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) := by positivity
    -- `V Pv Gv² ≤ e²⁰ (‖s+1‖‖s‖ Pv) Gs Gw`
    have step1 : V * Pv * Gv ^ 2 ≤ Real.exp 20 * (‖s + 1‖ * ‖s‖ * Pv) * (Gs * Gw) := by
      have := mul_le_mul_of_nonneg_left I12 hPv0
      calc V * Pv * Gv ^ 2 = Pv * (Gv ^ 2 * V) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    -- `‖s+1‖‖s‖ Pv ≤ 6 (m+2)^{m+1} V^{m+3}`
    have step2 : ‖s + 1‖ * ‖s‖ * Pv ≤
        6 * (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) * V ^ (m' + 3) := by
      calc ‖s + 1‖ * ‖s‖ * Pv ≤ (3 * V) * (2 * V) *
            ((((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) * V ^ (m' + 1)) := by gcongr
        _ = _ := by ring
    -- `V^{m+3} ≤ 3^{m+1} Ps P2 ‖s+3‖`
    have step3 : V ^ (m' + 3) ≤ 3 ^ (m' + 1) * (Ps * P2 * ‖s + 3‖) := by
      have h3 : (3:ℝ) ^ (m' + 1) * ((V / 3) ^ m' * V ^ 2 * V) = 3 * V ^ (m' + 3) := by
        rw [div_pow]; field_simp; ring
      have : (V / 3) ^ m' * V ^ 2 * V ≤ Ps * P2 * ‖s + 3‖ := by gcongr
      have hVp : 0 ≤ V ^ (m' + 3) := by positivity
      calc V ^ (m' + 3) ≤ 3 * V ^ (m' + 3) := by linarith
        _ = (3:ℝ) ^ (m' + 1) * ((V / 3) ^ m' * V ^ 2 * V) := h3.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    have hRL : RL (m' + 1) = Real.exp 20 * 6 * (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) *
        3 ^ (m' + 1) := rfl
    have hGG : 0 ≤ Gs * Gw := by positivity
    calc V * Pv * Gv ^ 2 ≤ Real.exp 20 * (‖s + 1‖ * ‖s‖ * Pv) * (Gs * Gw) := step1
      _ ≤ Real.exp 20 * (6 * (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) * V ^ (m' + 3)) *
          (Gs * Gw) := by gcongr
      _ ≤ Real.exp 20 * (6 * (((m' + 1 : ℕ) : ℝ) + 1) ^ (m' + 1) *
          (3 ^ (m' + 1) * (Ps * P2 * ‖s + 3‖))) * (Gs * Gw) := by gcongr
      _ = RL (m' + 1) * (Ps * Gs * P2 * Gw * ‖s + 3‖) := by rw [hRL]; ring
  exact (mul_le_mul (mul_le_one₀ hpi (norm_nonneg _) h4pi) hfrac (norm_nonneg _)
    zero_le_one).trans (one_mul _).le

section A

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)

/-- The Phragmén–Lindelöf function for the strip `[−ε, 1+ε]`. -/
noncomputable def fEps (ε : ℝ) (s : ℂ) : ℂ :=
  Efun d s * Complex.Gamma (s + 1) * (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3)

lemma differentiableOn_fEps (ε : ℝ) : DifferentiableOn ℂ (fEps d ε) {s : ℂ | -1 < s.re} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have h3 : s + 3 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : DifferentiableAt ℂ (fun s => Complex.Gamma (s + 1)) s := by
    refine (Complex.differentiableAt_Gamma (s + 1) fun m h => ?_).comp s
      (differentiableAt_id.add_const (1 : ℂ))
    have := congrArg re h; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hG4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (3 + 2 * ε - s))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (3 + 2 * ε - s)).comp s
      ((differentiableAt_const (3 + 2 * (ε : ℂ))).sub differentiableAt_id)
    simpa [Function.comp_def] using this
  unfold fEps
  exact ((((differentiable_Efun d s).mul hG).mul hG4).div (by fun_prop) h3).differentiableWithinAt

/-- `D_{1+ε} = ∑ ‖aₙ n^{−1−ε}‖`. -/
noncomputable def Deps (a : ℕ → ℝ) (ε : ℝ) : ℝ :=
  ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 + ε : ℝ) : ℂ) n‖

lemma Deps_nonneg (ε : ℝ) : 0 ≤ Deps a ε := tsum_nonneg fun _ => norm_nonneg _

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
lemma norm_LSeries_le_Deps {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 1 + ε ≤ s.re) :
    ‖LSeries (fun n => (a n : ℂ)) s‖ ≤ Deps a ε :=
  norm_LSeries_le (LSeriesSummable_of_one_lt habs (by simp; linarith)) (by simpa using hs)

include habs in
/-- `‖E(s)‖ ≤ ‖s+3‖ Z D_{1+ε}` for `Re s ≥ 1+ε`. -/
lemma Efun_right_eps {ε : ℝ} (hε : 0 < ε) {Z : ℝ}
    (hZ : ∀ w : ℂ, 2 ≤ w.re → ‖riemannZeta w‖ ≤ Z) {s : ℂ} (hs : 1 + ε ≤ s.re) :
    ‖Efun d s‖ ≤ ‖s + 3‖ * (Z * Deps a ε) := by
  rw [Efun_eq_LSeries' d habs (by linarith), norm_mul, norm_mul]
  have h1 := norm_sub_one_le_norm_add_three (s := s) (by linarith)
  have h2 := hZ (2 * s) (by simp; linarith)
  have h3 := norm_LSeries_le_Deps habs hε hs
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans h2
  calc ‖s - 1‖ * ‖riemannZeta (2 * s)‖ * ‖LSeries (fun n => (a n : ℂ)) s‖
      ≤ ‖s + 3‖ * Z * Deps a ε := by gcongr
    _ = _ := by ring

include habs in
lemma fEps_right {ε : ℝ} (hε : 0 < ε) {Z : ℝ}
    (hZ : ∀ w : ℂ, 2 ≤ w.re → ‖riemannZeta w‖ ≤ Z) {s : ℂ} (hs : s.re = 1 + ε) :
    ‖fEps d ε s‖ ≤ Z * Deps a ε := by
  have hc : 3 + 2 * (ε : ℂ) - s = starRingEnd ℂ (s + 1) := by
    apply Complex.ext <;> simp [hs] <;> ring
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s + 1) (by simp [hs]; linarith)
  have hrat : ‖Complex.Gamma (s + 1) * (Complex.Gamma (3 + 2 * ε - s))⁻¹‖ = 1 := by
    rw [hc, norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0)]
  have h3 : 0 < ‖s + 3‖ := lt_of_lt_of_le one_pos (one_le_norm_add_three (by linarith))
  unfold fEps
  rw [mul_assoc, norm_div, norm_mul, hrat, mul_one, div_le_iff₀ h3]
  have := Efun_right_eps d habs hε hZ (s := s) (by rw [hs])
  linarith

include habs in
lemma fEps_left (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {Z : ℝ} (hZ0 : 0 ≤ Z)
    (hZ : ∀ w : ℂ, 2 ≤ w.re → ‖riemannZeta w‖ ≤ Z) {s : ℂ} (hs : s.re = -ε) :
    ‖fEps d ε s‖ ≤ RL m * (Z * Deps a ε) := by
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 1 + ε := by rw [hw]; simp [hs]
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs; linarith
  have hE : Efun d s = (s - 1) * gamM m w * invGamM m s *
      (riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) := by
    rw [Efun_eq d h0 h1, ← Lam_fe d s, ← hw, Lam_eq d habs (by rw [hwre]; linarith)]; ring
  have hsplit : fEps d ε s = ((s - 1) * gamM m (1 - s) * invGamM m s * Complex.Gamma (s + 1) *
      (Complex.Gamma (3 + 2 * ε - s))⁻¹ / (s + 3)) *
      (riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w) := by
    unfold fEps; rw [hE, hw]; ring
  rw [hsplit, norm_mul, norm_mul]
  have hr := ratioEps_le hm hε0 hε hs
  have hz := hZ (2 * w) (by simp [hwre]; linarith)
  have hD := norm_LSeries_le_Deps habs hε0 (s := w) (by rw [hwre])
  calc _ ≤ RL m * (Z * Deps a ε) := by gcongr; exact RL_nonneg m

lemma fEps_growth {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ K L : ℝ, ∀ s : ℂ, -ε < s.re → s.re < 1 + ε → 1 ≤ |s.im| →
      ‖fEps d ε s‖ ≤ K * Real.exp (L * |s.im|) := by
  obtain ⟨K, L, hKL⟩ := Efun_growth d
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gamma_le (A := 3 / 2) (by norm_num)
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) (5 / 2)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    intro h; have := hx.1; rw [h] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hG⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨|K| * |G| * C, |L| + π, fun s h1 h2 ht => ?_⟩
  have hE := hKL s (by linarith) (by linarith) ht
  have hE' : ‖Efun d s‖ ≤ |K| * Real.exp (|L| * |s.im|) :=
    hE.trans (mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (le_abs_self L) (abs_nonneg _))) (Real.exp_pos _).le (abs_nonneg K))
  have hg1 : ‖Complex.Gamma (s + 1)‖ ≤ |G| := by
    refine (norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
    have := hG (s + 1).re ⟨by simp; linarith, by simp; linarith⟩
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_abs_self G)
  have hg4 := hC (3 + 2 * ε - s) (by simp; linarith) (by simpa using ht)
  simp only [sub_im, add_im, mul_im, ofReal_im, re_ofNat, im_ofNat, ofReal_re, zero_mul,
    mul_zero, add_zero, zero_add, zero_sub, abs_neg] at hg4
  have h3 : 1 ≤ ‖s + 3‖ := one_le_norm_add_three (by linarith)
  unfold fEps
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
  have hexp : Real.exp ((|L| + π) * |s.im|) = Real.exp (|L| * |s.im|) * Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Efun d s‖ * ‖Complex.Gamma (s + 1)‖ * ‖(Complex.Gamma (3 + 2 * ε - s))⁻¹‖
      ≤ (|K| * Real.exp (|L| * |s.im|)) * |G| * (C * Real.exp (π * |s.im|)) := by gcongr
    _ = |K| * |G| * C * Real.exp ((|L| + π) * |s.im|) := by rw [hexp]; ring
    _ ≤ |K| * |G| * C * Real.exp ((|L| + π) * |s.im|) * ‖s + 3‖ :=
        le_mul_of_one_le_right (by positivity) h3

include habs in
/-- **Phragmén–Lindelöf on `[−ε, 1+ε]`**: `f_ε` is bounded on the closed strip. -/
theorem fEps_bound (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -ε ≤ s.re → s.re ≤ 1 + ε → ‖fEps d ε s‖ ≤ C := by
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_zeta_le2
  obtain ⟨K, L, hKL⟩ := fEps_growth d hε0 hε
  have hD0 := Deps_nonneg (a := a) ε
  have hRL : 1 ≤ RL m := by
    unfold RL
    have : 1 ≤ Real.exp 20 := Real.one_le_exp (by norm_num)
    have h2 : (1:ℝ) ≤ ((m : ℝ) + 1) ^ m := one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    have h3 : (1:ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    have : (1:ℝ) ≤ Real.exp 20 * 6 := by linarith
    calc (1:ℝ) = 1 * 1 * 1 := by ring
      _ ≤ Real.exp 20 * 6 * ((m : ℝ) + 1) ^ m * 3 ^ m := by gcongr
  refine ⟨RL m * (Z * Deps a ε), by positivity, fun s h1 h2 => ?_⟩
  refine pl_strip (a' := -1) (by linarith) (by linarith) (by linarith [Real.pi_gt_three])
    (differentiableOn_fEps d ε) hKL (fun z hz => fEps_left d habs hm hε0 hε hZ0 hZ hz)
    (fun z hz => (fEps_right d habs hε0 hZ hz).trans ?_) h1 h2
  have : 0 ≤ Z * Deps a ε := by positivity
  nlinarith

/-- **The convexity bound on a line.** For `0 ≤ Re s = σ ≤ 1+ε`:
`‖E(s)‖ ≤ 6e¹⁰ C ‖s+3‖^{3+2ε−2σ}`. -/
lemma Efun_line_eps {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {C : ℝ}
    (hC : ∀ s : ℂ, -ε ≤ s.re → s.re ≤ 1 + ε → ‖fEps d ε s‖ ≤ C) {s : ℂ} (h0 : 0 ≤ s.re)
    (h1 : s.re ≤ 1 + ε) :
    ‖Efun d s‖ ≤ 6 * Real.exp 10 * C * ‖s + 3‖ ^ (3 + 2 * ε - 2 * s.re) := by
  set θ : ℝ := 2 + 2 * ε - 2 * s.re with hθ
  set u : ℂ := starRingEnd ℂ (s + 1) with hu
  have hu1 : 1 ≤ u.re := by simp [hu]; linarith
  have hb : 3 + 2 * (ε : ℂ) - s = u + θ := by
    apply Complex.ext <;> simp [hu, hθ] <;> ring
  have hG1 := Complex.Gamma_ne_zero_of_re_pos (s := s + 1) (by simp; linarith)
  have h3 : s + 3 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hE : Efun d s = fEps d ε s *
      (Complex.Gamma (3 + 2 * ε - s) * (Complex.Gamma (s + 1))⁻¹) * (s + 3) := by
    have hGb : Complex.Gamma (3 + 2 * ε - s) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    unfold fEps; field_simp
  have hratio : ‖Complex.Gamma (3 + 2 * ε - s) * (Complex.Gamma (s + 1))⁻¹‖ ≤
      6 * Real.exp 10 * ‖s + 3‖ ^ θ := by
    have hG := norm_Gamma_add_le hu1 2 (θ := θ) (by rw [hθ]; linarith) (by
      rw [hθ]; push_cast; linarith)
    rw [norm_mul, norm_inv, hb]
    rw [hu, norm_Gamma_conj, Complex.norm_conj] at hG
    have hpos : 0 < ‖Complex.Gamma (s + 1)‖ := norm_pos_iff.2 hG1
    rw [mul_inv_le_iff₀ hpos]
    have hn : ‖s + 1‖ ^ θ ≤ ‖s + 3‖ ^ θ := by
      apply Real.rpow_le_rpow (norm_nonneg _) _ (by rw [hθ]; linarith)
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_eq, sq_norm_eq]
      simp; nlinarith
    have hf : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf] at hG
    calc _ ≤ 6 * Real.exp 10 * ‖s + 1‖ ^ θ * ‖Complex.Gamma (s + 1)‖ := hG
      _ ≤ 6 * Real.exp 10 * ‖s + 3‖ ^ θ * ‖Complex.Gamma (s + 1)‖ := by gcongr
      _ = _ := by ring
  have hfa := hC s (by linarith) h1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hfa
  have hs3 : 0 < ‖s + 3‖ := lt_of_lt_of_le one_pos (one_le_norm_add_three (by linarith))
  rw [hE, norm_mul, norm_mul]
  have hexp : ‖s + 3‖ ^ (3 + 2 * ε - 2 * s.re) = ‖s + 3‖ ^ θ * ‖s + 3‖ := by
    rw [hθ, ← Real.rpow_add_one hs3.ne']; ring_nf
  rw [hexp]
  calc ‖fEps d ε s‖ * ‖Complex.Gamma (3 + 2 * ε - s) * (Complex.Gamma (s + 1))⁻¹‖ * ‖s + 3‖
      ≤ C * (6 * Real.exp 10 * ‖s + 3‖ ^ θ) * ‖s + 3‖ := by gcongr
    _ = _ := by ring

include habs in
/-- **Uniform convexity bound.** For `0 < ε ≤ 1/2` and `0 ≤ σ₁ ≤ 1`:
`‖E(s)‖ ≤ B ‖s+3‖^{3+2ε−2σ₁}` on `σ₁ ≤ Re s ≤ 5/2`. -/
theorem Efun_bound_eps (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {σ₁ : ℝ}
    (h0 : 0 ≤ σ₁) (h1 : σ₁ ≤ 1) :
    ∃ B : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 5 / 2 →
      ‖Efun d s‖ ≤ B * ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) := by
  obtain ⟨C, hC0, hC⟩ := fEps_bound d habs hm hε0 hε
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_zeta_le2
  have hD0 := Deps_nonneg (a := a) ε
  refine ⟨6 * Real.exp 10 * C + Z * Deps a ε, fun s hs1 hs2 => ?_⟩
  have h3 : 1 ≤ ‖s + 3‖ := one_le_norm_add_three (by linarith)
  have hB1 : 0 ≤ 6 * Real.exp 10 * C := by positivity
  have hB2 : 0 ≤ Z * Deps a ε := by positivity
  rcases le_or_gt s.re (1 + ε) with hr | hr
  · have := Efun_line_eps d hε0 hε hC (by linarith) hr
    have hmono : ‖s + 3‖ ^ (3 + 2 * ε - 2 * s.re) ≤ ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) :=
      Real.rpow_le_rpow_of_exponent_le h3 (by linarith)
    have hp : 0 ≤ ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) := by positivity
    calc ‖Efun d s‖ ≤ 6 * Real.exp 10 * C * ‖s + 3‖ ^ (3 + 2 * ε - 2 * s.re) := this
      _ ≤ 6 * Real.exp 10 * C * ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) := by gcongr
      _ ≤ _ := by nlinarith
  · have := Efun_right_eps d habs hε0 hZ (s := s) hr.le
    have hmono : ‖s + 3‖ ≤ ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) := by
      calc ‖s + 3‖ = ‖s + 3‖ ^ (1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h3 (by linarith)
    have hp : 0 ≤ ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) := by positivity
    calc ‖Efun d s‖ ≤ ‖s + 3‖ * (Z * Deps a ε) := this
      _ ≤ ‖s + 3‖ ^ (3 + 2 * ε - 2 * σ₁) * (Z * Deps a ε) := by gcongr
      _ ≤ _ := by nlinarith

end A

end RamanujanTau.Stirling

#print axioms RamanujanTau.Stirling.ratioEps_le
#print axioms RamanujanTau.Stirling.fEps_bound
#print axioms RamanujanTau.Stirling.Efun_bound_eps
