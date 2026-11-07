/-
# The convexity bound for `L(f,s)`, `f ∈ S_k(SL₂(ℤ))`

Unnormalized coordinates: critical line `Re s = k/2`, absolute convergence for
`Re s > (k+1)/2` (`LSeriesSummable_coef`). For `k < 12` the space `S_k` is zero
(Mathlib `CuspForm.rank_eq_zero_of_weight_lt_twelve`), so all bounds are trivial; for `k ≥ 12`
the proof of `HeckeConvex/Convex.lean` (`f = Δ`) runs with `13 ↦ k+1`, `12 ↦ k`:

Fix `0 < ε ≤ 1/2`, `a = (k−1)/2 − ε`, `b = (k+1)/2 + ε` and

    f_ε(s) = L(f,s) Γ(s/2) / Γ((k + 1 + 2ε − s)/2).

* Right edge `Re s = b`: `(k+1+2ε−s)/2 = conj(s/2)`, so `‖f_ε‖ ≤ ∑ |a(n)| n^{−b}`.
* Left edge `Re s = a`: `L(f,s) = i^k (2π)^{2s−k} Γ(k−s)/Γ(s) · L(f,k−s)` with `Re(k−s) = b`;
  again `k − s = s̄ + θ`, `(k+1+2ε−s)/2 = conj(s/2) + θ`, `θ = 1 + 2ε`, giving `8e²⁰`.
* Order `≤ e^{2π|t|}` inside, then Phragmén–Lindelöf (`RankinSharp.pl_strip`).
-/
import RamanujanTau.HeckeConvexGeneral.Hecke
import RamanujanTau.Stirling.GammaRatio
import RamanujanTau.RankinSharp.PL
import RamanujanTau.RankinError.GammaBound

set_option autoImplicit false

namespace RamanujanTau.HeckeConvexGeneral

open Complex LSeries Set Filter Topology ModularForm
open scoped Real MatrixGroups

variable {k : ℕ}

/-! ### `L(f,s)` on `Re s > (k+1)/2` -/

lemma norm_LSeries_le' {a : ℕ → ℂ} {σ : ℝ} (hσ : LSeriesSummable a σ) {s : ℂ} (h : σ ≤ s.re) :
    ‖LSeries a s‖ ≤ ∑' n, ‖LSeries.term a σ n‖ := by
  have hs : LSeriesSummable a s := hσ.of_re_le_re (by simpa using h)
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  exact hs.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re a (by simpa using h) n)
    hσ.norm

/-- `‖L(f,s)‖ ≤ ∑ |a(n)| n^{−σ}` for `Re s ≥ σ > (k+1)/2`. -/
theorem fL_bounded_of_gt (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {σ : ℝ}
    (hσ : ((k : ℝ) + 1) / 2 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, σ ≤ s.re → ‖fL f s‖ ≤ D := by
  have hsum : LSeriesSummable (coef f) (σ : ℂ) := LSeriesSummable_coef f hk (by simpa using hσ)
  refine ⟨∑' n, ‖LSeries.term (coef f) σ n‖, tsum_nonneg fun _ => norm_nonneg _,
    fun s hs => ?_⟩
  rw [fL_eq_LSeries f hk (by linarith)]
  exact norm_LSeries_le' hsum hs

/-! ### Elementary `Γ` facts -/

/-- `1/Γ(w) ≪ e^{π|Im w|}` uniformly for `0 ≤ Re w ≤ R` (all `Im w`). -/
lemma exists_norm_inv_Gamma_le_strip (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ R →
    ‖(Complex.Gamma w)⁻¹‖ ≤ C * Real.exp (π * |w.im|) := by
  obtain ⟨C1, hC1, h1⟩ := RamanujanTau.RankinError.exists_norm_inv_Gamma_le (A := 1 / 2)
    (by norm_num)
  have hc : Continuous fun w : ℂ => (Complex.Gamma w)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (|R| + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C1 M, le_max_of_le_left hC1, fun w h0 hR => ?_⟩
  have he : 1 ≤ Real.exp (π * |w.im|) := Real.one_le_exp (by positivity)
  rcases le_or_gt 1 |w.im| with hi | hi
  · calc ‖(Complex.Gamma w)⁻¹‖ ≤ C1 * Real.exp (π * |w.im|) := h1 w (by linarith) hi
      _ ≤ max C1 M * Real.exp (π * |w.im|) := by gcongr; exact le_max_left _ _
  · have hw : w ∈ Metric.closedBall (0 : ℂ) (|R| + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_nonneg h0]; linarith [le_abs_self R]
    have := hM w hw
    have hM0 : 0 ≤ M := (norm_nonneg _).trans this
    calc ‖(Complex.Gamma w)⁻¹‖ ≤ M := this
      _ ≤ max C1 M := le_max_right _ _
      _ ≤ max C1 M * Real.exp (π * |w.im|) := le_mul_of_one_le_right (by positivity) he

@[simp] lemma re_conj_half (s : ℂ) : (starRingEnd ℂ (s / 2)).re = s.re / 2 := by
  rw [map_div₀, map_ofNat]; simp

@[simp] lemma im_conj_half (s : ℂ) : (starRingEnd ℂ (s / 2)).im = -(s.im / 2) := by
  rw [map_div₀, map_ofNat]; simp; ring

/-- `(K+1+2ε−s)/2 = conj(s/2) + θ`, `θ = (K+1+2ε−2 Re s)/2`. -/
lemma half_eq_conj_add (K : ℕ) (ε : ℝ) (s : ℂ) :
    ((K : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2 =
      starRingEnd ℂ (s / 2) + ((((K : ℝ) + 1 + 2 * ε - 2 * s.re) / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, re_conj_half, Complex.ofReal_re]; simp; ring
  · simp only [Complex.add_im, im_conj_half, Complex.ofReal_im]; simp; ring

/-- `K − s = conj s + (K − 2 Re s)`. -/
lemma sub_eq_conj_add (K : ℕ) (s : ℂ) :
    (K : ℂ) - s = starRingEnd ℂ s + (((K : ℝ) - 2 * s.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma norm_two_pi_cpow' (s : ℂ) : ‖(2 * π : ℂ) ^ s‖ = (2 * π) ^ s.re := by
  have h : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [h, norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-! ### The Phragmén–Lindelöf function -/

/-- `f_ε(s) = L(f,s) Γ(s/2) / Γ((k+1+2ε−s)/2)`. -/
noncomputable def fC (f : CuspForm 𝒮ℒ (k : ℤ)) (ε : ℝ) (s : ℂ) : ℂ :=
  fL f s * Complex.Gamma (s / 2) * (Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹

lemma differentiableOn_fC (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (ε : ℝ) :
    DifferentiableOn ℂ (fC f ε) {s : ℂ | 4 < s.re} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have hG : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s := by
    refine (Complex.differentiableAt_Gamma (s / 2) fun m h => ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    have := congrArg re h; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hG2 : DifferentiableAt ℂ
      (fun s : ℂ => (Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2)).comp s
      (((differentiableAt_const ((k : ℂ) + 1 + 2 * (ε : ℂ))).sub differentiableAt_id).div_const
        (2 : ℂ))
    simpa [Function.comp_def] using this
  unfold fC
  exact (((fL_entire f hk s).mul hG).mul hG2).differentiableWithinAt

lemma fC_growth (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ K L : ℝ, ∀ s : ℂ, ((k : ℝ) - 1) / 2 - ε < s.re → s.re < ((k : ℝ) + 1) / 2 + ε →
      1 ≤ |s.im| → ‖fC f ε s‖ ≤ K * Real.exp (L * |s.im|) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set κ : ℝ := (k : ℝ) with hκ
  obtain ⟨C0, hC0, hC⟩ := exists_norm_inv_Gamma_le_strip (κ + 2)
  obtain ⟨L0, hL0⟩ := heckeLambda_bdd_strip f hk1 (κ / 2 - 1) (κ / 2 + 1)
  have hcont : ContinuousOn Real.Gamma (Icc (κ / 4 - 1 / 2) (κ / 4 + 1 / 2)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    intro h; have := hx.1; rw [h] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hG⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨(2 * π) ^ (κ / 2 + 1) * C0 * |L0| * |G| * C0, 2 * π, fun s h1 h2 _ => ?_⟩
  have hre5 : κ / 2 - 1 ≤ s.re := by linarith
  have hre7 : s.re ≤ κ / 2 + 1 := by linarith
  have hT : ‖fL f s‖ ≤ (2 * π) ^ (κ / 2 + 1) * (C0 * Real.exp (π * |s.im|)) * |L0| := by
    unfold fL
    rw [norm_mul, norm_mul, norm_two_pi_cpow']
    have hp : (2 * π) ^ s.re ≤ (2 * π) ^ (κ / 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hre7
    have hg := hC s (by linarith) (by linarith)
    have hl := (hL0 s hre5 hre7).trans (le_abs_self L0)
    gcongr
  have hg1 : ‖Complex.Gamma (s / 2)‖ ≤ |G| := by
    refine (RamanujanTau.RankinError.norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
    have := hG (s / 2).re ⟨by simp; linarith, by simp; linarith⟩
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_abs_self G)
  have hg2 : ‖(Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹‖ ≤
      C0 * Real.exp (π * |s.im|) := by
    refine (hC _ (by simp; linarith) (by simp; linarith)).trans ?_
    have him : |(((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2).im| = |s.im| / 2 := by simp [abs_div]
    rw [him]
    gcongr
    have : 0 ≤ |s.im| := abs_nonneg _
    linarith
  have hexp : Real.exp (2 * π * |s.im|) = Real.exp (π * |s.im|) * Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; ring_nf
  unfold fC
  rw [norm_mul, norm_mul]
  calc ‖fL f s‖ * ‖Complex.Gamma (s / 2)‖ *
        ‖(Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹‖
      ≤ ((2 * π) ^ (κ / 2 + 1) * (C0 * Real.exp (π * |s.im|)) * |L0|) * |G| *
          (C0 * Real.exp (π * |s.im|)) := by gcongr
    _ = _ := by rw [hexp]; ring

/-- **Right edge** `Re s = (k+1)/2 + ε`. -/
lemma fC_right (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε0 : 0 < ε) {D : ℝ}
    (hD : ∀ z : ℂ, ((k : ℝ) + 1) / 2 + ε ≤ z.re → ‖fL f z‖ ≤ D) {s : ℂ}
    (hs : s.re = ((k : ℝ) + 1) / 2 + ε) : ‖fC f ε s‖ ≤ D := by
  have hc : ((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2 = starRingEnd ℂ (s / 2) := by
    rw [half_eq_conj_add, hs]; simp; ring_nf
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s / 2)
    (by simp [hs]; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hrat : ‖Complex.Gamma (s / 2) *
      (Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹‖ = 1 := by
    rw [hc, norm_mul, norm_inv, RamanujanTau.RankinError.norm_Gamma_conj,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0)]
  unfold fC
  rw [mul_assoc, norm_mul, hrat, mul_one]
  exact hD s hs.ge

/-- **Left edge** `Re s = (k−1)/2 − ε`, via the functional equation. -/
lemma fC_left (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    {D : ℝ} (hD : ∀ z : ℂ, ((k : ℝ) + 1) / 2 + ε ≤ z.re → ‖fL f z‖ ≤ D) {s : ℂ}
    (hs : s.re = ((k : ℝ) - 1) / 2 - ε) : ‖fC f ε s‖ ≤ 8 * Real.exp 20 * D := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set θ : ℝ := 1 + 2 * ε with hθ
  have hs0 : ∀ n : ℕ, (k : ℂ) - s ≠ -n := by
    intro n h; have := congrArg re h; simp [hs] at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hFE : heckeLambda f s = I ^ k * heckeLambda f ((k : ℂ) - s) := by
    have := heckeLambda_functional_equation f hk1 ((k : ℂ) - s)
    rwa [sub_sub_cancel] at this
  have hT : fL f s = I ^ k * (((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-((k : ℂ) - s))) *
      (Complex.Gamma ((k : ℂ) - s) * (Complex.Gamma s)⁻¹) * fL f ((k : ℂ) - s)) := by
    conv_lhs => rw [fL, hFE, heckeLambda_eq_fL f hs0]
    ring
  have e1 : (k : ℂ) - s = starRingEnd ℂ s + (θ : ℂ) := by
    rw [sub_eq_conj_add, hs, hθ]; congr 1; push_cast; ring
  have e2 : ((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2 = starRingEnd ℂ (s / 2) + (θ : ℂ) := by
    rw [half_eq_conj_add, hs, hθ]; congr 1; push_cast; ring
  have hcs1 : 1 ≤ (starRingEnd ℂ s).re := by simp [hs]; linarith
  have hcs2 : 1 ≤ (starRingEnd ℂ (s / 2)).re := by rw [re_conj_half, hs]; linarith
  have I1 := RamanujanTau.Stirling.norm_Gamma_add_le hcs1 1 (θ := θ) (by positivity)
    (by rw [hθ]; push_cast; linarith)
  rw [← e1, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I1
  have hf2 : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf2] at I1
  have I2 := RamanujanTau.Stirling.norm_Gamma_mul_rpow_le_add hcs2 (θ := θ) (by positivity)
  rw [← e2, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I2
  set R : ℝ := ‖s‖ with hR
  have hR0 : 0 < R := by
    rw [hR, norm_pos_iff]; intro h; rw [h] at hs; simp at hs; linarith
  have hs2 : ‖s / 2‖ = R / 2 := by rw [norm_div]; simp [hR]
  rw [hs2] at I2
  set A : ℝ := ‖Complex.Gamma s‖
  set B : ℝ := ‖Complex.Gamma (s / 2)‖
  set W : ℝ := ‖Complex.Gamma (((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2)‖
  have hA : 0 < A := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; linarith))
  have hW : 0 < W := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; linarith))
  have hB : 0 ≤ B := norm_nonneg _
  have hRθ : (R / 2) ^ θ * 2 ^ θ = R ^ θ := by
    rw [← Real.mul_rpow (by positivity) (by norm_num)]; congr 1; ring
  have h2θ : (2 : ℝ) ^ θ ≤ 4 := by
    calc (2 : ℝ) ^ θ ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hθ]; linarith)
      _ = 4 := by norm_num
  have hP : ‖(2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-((k : ℂ) - s))‖ ≤ 1 := by
    rw [norm_mul, norm_two_pi_cpow', norm_two_pi_cpow', ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; linarith
  have hQ : ‖(Complex.Gamma ((k : ℂ) - s) * (Complex.Gamma s)⁻¹) *
      (Complex.Gamma (s / 2) * (Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹)‖ ≤
        8 * Real.exp 20 := by
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
    have q1 : ‖Complex.Gamma ((k : ℂ) - s)‖ * A⁻¹ ≤ 2 * Real.exp 10 * R ^ θ := by
      rw [mul_inv_le_iff₀ hA]; linarith
    have q2 : B * W⁻¹ * (R / 2) ^ θ ≤ Real.exp 10 := by
      rw [mul_comm B, mul_assoc, inv_mul_le_iff₀ hW]; linarith
    have hBW : 0 ≤ B * W⁻¹ := by positivity
    have e20 : Real.exp 20 = Real.exp 10 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
    calc ‖Complex.Gamma ((k : ℂ) - s)‖ * A⁻¹ * (B * W⁻¹)
        ≤ (2 * Real.exp 10 * R ^ θ) * (B * W⁻¹) := by gcongr
      _ = 2 * Real.exp 10 * 2 ^ θ * (B * W⁻¹ * (R / 2) ^ θ) := by rw [← hRθ]; ring
      _ ≤ 2 * Real.exp 10 * 4 * Real.exp 10 := by gcongr
      _ = 8 * Real.exp 20 := by rw [e20]; ring
  have hL := hD ((k : ℂ) - s) (by simp [hs]; linarith)
  have hIk : ‖I ^ k‖ = 1 := by rw [norm_pow, Complex.norm_I, one_pow]
  have hsplit : fC f ε s = I ^ k * (((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-((k : ℂ) - s))) *
      ((Complex.Gamma ((k : ℂ) - s) * (Complex.Gamma s)⁻¹) *
        (Complex.Gamma (s / 2) * (Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2))⁻¹)) *
        fL f ((k : ℂ) - s)) := by
    unfold fC; rw [hT]; ring
  rw [hsplit, norm_mul, hIk, one_mul, norm_mul, norm_mul]
  calc _ ≤ 1 * (8 * Real.exp 20) * D := by gcongr
    _ = 8 * Real.exp 20 * D := by ring

/-- **Phragmén–Lindelöf**: `f_ε` is bounded on the closed strip `[(k−1)/2−ε, (k+1)/2+ε]`. -/
theorem fC_bound (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ((k : ℝ) - 1) / 2 - ε ≤ s.re → s.re ≤ ((k : ℝ) + 1) / 2 + ε →
      ‖fC f ε s‖ ≤ C := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk1 (σ := ((k : ℝ) + 1) / 2 + ε) (by linarith)
  obtain ⟨K, L, hKL⟩ := fC_growth f hk hε0 hε
  have h8 : 1 ≤ 8 * Real.exp 20 := by
    have := Real.one_le_exp (show (0:ℝ) ≤ 20 by norm_num); linarith
  refine ⟨8 * Real.exp 20 * D, by positivity, fun s h1 h2 => ?_⟩
  refine RamanujanTau.RankinSharp.pl_strip (a' := 4) (by linarith) (by linarith)
    (by linarith [Real.pi_gt_three]) (differentiableOn_fC f hk1 ε) hKL
    (fun z hz => fC_left f hk hε0 hε hD hz) (fun z hz => (fC_right f hε0 hD hz).trans ?_) h1 h2
  nlinarith

/-- **The convexity bound on a line** `(k−1)/2 − ε ≤ σ ≤ (k+1)/2 + ε`:
`‖L(f,s)‖ ≤ 2e¹⁰ C ‖s/2‖^{(k+1)/2+ε−σ}`. -/
lemma fL_line (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    {C : ℝ} (hC : ∀ s : ℂ, ((k : ℝ) - 1) / 2 - ε ≤ s.re → s.re ≤ ((k : ℝ) + 1) / 2 + ε →
      ‖fC f ε s‖ ≤ C) {s : ℂ}
    (h1 : ((k : ℝ) - 1) / 2 - ε ≤ s.re) (h2 : s.re ≤ ((k : ℝ) + 1) / 2 + ε) :
    ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ (((k : ℝ) + 1) / 2 + ε - s.re) := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set θ : ℝ := ((k : ℝ) + 1 + 2 * ε - 2 * s.re) / 2 with hθ
  have hθ' : θ = ((k : ℝ) + 1) / 2 + ε - s.re := by rw [hθ]; ring
  have e3 := half_eq_conj_add k ε s
  rw [← hθ] at e3
  have hcs : 1 ≤ (starRingEnd ℂ (s / 2)).re := by rw [re_conj_half]; linarith
  have I3 := RamanujanTau.Stirling.norm_Gamma_add_le hcs 1 (θ := θ) (by rw [hθ']; linarith)
    (by rw [hθ']; push_cast; linarith)
  rw [← e3, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I3
  have hf2 : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf2] at I3
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s / 2) (by simp; linarith)
  have hW0 := Complex.Gamma_ne_zero_of_re_pos (s := ((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2)
    (by simp; linarith)
  have hT : fL f s = fC f ε s * Complex.Gamma (((k : ℂ) + 1 + 2 * ε - s) / 2) *
      (Complex.Gamma (s / 2))⁻¹ := by
    unfold fC; field_simp
  have hfa := hC s h1 h2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hfa
  have hpos : 0 < ‖Complex.Gamma (s / 2)‖ := norm_pos_iff.2 hG0
  rw [hT, norm_mul, norm_mul, norm_inv, ← hθ']
  have hq : ‖Complex.Gamma (((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2)‖ *
      ‖Complex.Gamma (s / 2)‖⁻¹ ≤ 2 * Real.exp 10 * ‖s / 2‖ ^ θ := by
    rw [mul_inv_le_iff₀ hpos]; linarith
  calc ‖fC f ε s‖ * ‖Complex.Gamma (((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2)‖ *
        ‖Complex.Gamma (s / 2)‖⁻¹
      = ‖fC f ε s‖ * (‖Complex.Gamma (((k : ℂ) + 1 + 2 * (ε : ℂ) - s) / 2)‖ *
          ‖Complex.Gamma (s / 2)‖⁻¹) := by ring
    _ ≤ C * (2 * Real.exp 10 * ‖s / 2‖ ^ θ) := by gcongr
    _ = _ := by ring

/-! ### Headline theorems -/

/-- `S_k(SL₂(ℤ)) = 0` for `k < 12` (Mathlib dimension formula). -/
lemma eq_zero_of_lt_twelve (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : k < 12) : f = 0 :=
  rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk)) f

/-- **Convexity bound, uniform in the strip** `(k−1)/2 ≤ σ ≤ (k+1)/2`: for every `ε > 0`,
`‖L(f, σ+it)‖ ≤ C (1+|t|)^{(k+1)/2 − σ + ε}`. -/
theorem fL_convexity_strip (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, ((k : ℝ) - 1) / 2 ≤ σ → σ ≤ ((k : ℝ) + 1) / 2 →
      ‖fL f ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (((k : ℝ) + 1) / 2 - σ + ε) := by
  rcases lt_or_ge k 12 with hk | hk
  · refine ⟨0, le_rfl, fun σ t _ _ => ?_⟩
    rw [fL_of_eq_zero (eq_zero_of_lt_twelve f hk)]; simp
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk hε'0 hε'1
  set M : ℝ := (k : ℝ) + 1 with hM
  refine ⟨2 * Real.exp 10 * C * M ^ (2 : ℝ), by positivity, fun σ t h1 h2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hL := fL_line f hk hε'0 hε'1 hC (s := s) (by rw [hsre]; linarith)
    (by rw [hsre]; linarith)
  rw [hsre] at hL
  set θ : ℝ := ((k : ℝ) + 1) / 2 + ε' - σ with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hn : ‖s / 2‖ ≤ M * (1 + |t|) := by
    rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ), hM]; nlinarith
  have hb1 : (1 : ℝ) ≤ 1 + |t| := by linarith
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; linarith
  have hp1 : ‖s / 2‖ ^ θ ≤ (M * (1 + |t|)) ^ θ :=
    Real.rpow_le_rpow (norm_nonneg _) hn hθ0
  have hp2 : (M * (1 + |t|)) ^ θ = M ^ θ * (1 + |t|) ^ θ :=
    Real.mul_rpow (by linarith) (by linarith)
  have hp3 : M ^ θ ≤ M ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by rw [hθ]; linarith)
  have hp4 : (1 + |t|) ^ θ ≤ (1 + |t|) ^ (((k : ℝ) + 1) / 2 - σ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by rw [hθ]; linarith)
  have hK : 0 ≤ 2 * Real.exp 10 * C := by positivity
  calc ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
    _ ≤ 2 * Real.exp 10 * C * (M ^ θ * (1 + |t|) ^ θ) := by rw [← hp2]; gcongr
    _ ≤ 2 * Real.exp 10 * C * (M ^ (2 : ℝ) * (1 + |t|) ^ (((k : ℝ) + 1) / 2 - σ + ε)) := by
        gcongr
    _ = _ := by ring

/-- **The convexity bound on the critical line** `Re s = k/2`: for every `ε > 0`,
`‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2+ε}`. -/
theorem fL_convexity (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f (((k : ℝ) / 2 : ℝ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := fL_convexity_strip f hε
  refine ⟨C, hC0, fun t => ?_⟩
  have := hC ((k : ℝ) / 2) t (by linarith) (by linarith)
  have e : (((k : ℝ) + 1) / 2 - (k : ℝ) / 2 + ε : ℝ) = 1 / 2 + ε := by ring
  rw [e] at this
  exact this

/-- **Convexity bound for the Dirichlet series itself** (`f ≠ 0` not needed): on the critical
line, `L(f,s)` (the analytic continuation `fL f` of `∑ a_f(n) n^{−s}`) is `≪ (1+|t|)^{1/2+ε}`;
and `fL f = LSeries (coef f)` on `Re s > (k+1)/2`. -/
theorem fL_convexity_and_continuation (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    Differentiable ℂ (fL f) ∧
    (∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → fL f s = LSeries (coef f) s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f (((k : ℝ) / 2 : ℝ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε) :=
  ⟨fL_entire f hk, fun _ hs => fL_eq_LSeries f hk hs, fL_convexity f hε⟩

end RamanujanTau.HeckeConvexGeneral
