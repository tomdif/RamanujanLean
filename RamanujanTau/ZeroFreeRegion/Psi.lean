/-
# The auxiliary function `Ψ = (z−1)³ F(z)`

For a fixed height `γ` (`|γ| ≥ 1`) put `L(w) = tauL(w + 11/2)` and

  `Ψ(z) = L(z+iγ)² L(z−iγ)² · (z−1)ζ(z) · ((z−1)ζ(2z)R(z))² · ζ(2z+4iγ)R(z+2iγ) · ζ(2z−4iγ)R(z−2iγ)`,

with `(z−1)ζ(z)`, `(z−1)R(z)`, `R(z±2iγ)` the Abel continuations of `Continuation`.  Then:

* `Ψ` is holomorphic on `Ω = {Re z > 3/5, |Im z| < 1/2}` (`differentiableOn_Psi`);
* `Ψ(σ) = (σ−1)³ F(σ)` for real `σ > 1` (`Psi_real`), `F = EdgeNonvanishing.Fval σ γ`;
* `Ψ(u) ≠ 0` for `Re u > 1` (`Psi_ne_zero`);
* if `L(β+iγ) = 0` then `Ψ` vanishes to order `≥ 4` at `β` (`four_le_order`);
* `‖Ψ(z)‖ ≤ B (9+|γ|)^{10}` on `|z − (1+δ)| ≤ 1/4`, `0 < δ ≤ 1/8` (`norm_Psi_le`).
-/
import RamanujanTau.ZeroFreeRegion.Continuation
import RamanujanTau.ZeroFreeRegion.Monotone
import RamanujanTau.ZeroCount.Bounds

set_option autoImplicit false

namespace RamanujanTau.ZeroFreeRegion

open Complex Metric Set Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL
open scoped ComplexConjugate

/-- The normalized `L(w) = L(Δ, w + 11/2)` (edge at `Re w = 1`). -/
noncomputable def Ln (w : ℂ) : ℂ := tauL (w + 11 / 2)

/-- `L(z+iγ)² L(z−iγ)²`. -/
noncomputable def Lpart (γ : ℝ) (z : ℂ) : ℂ :=
  Ln (z + γ * I) * Ln (z + γ * I) * (Ln (z - γ * I) * Ln (z - γ * I))

/-- The `ζ`/Rankin–Selberg part, with the pole at `1` removed. -/
noncomputable def Rest (γ : ℝ) (z : ℂ) : ℂ :=
  Z1 z * ((riemannZeta (2 * z) * R1 z) * (riemannZeta (2 * z) * R1 z)) *
    (riemannZeta (2 * z + 4 * γ * I) * Rt (z + 2 * γ * I)) *
    (riemannZeta (2 * z - 4 * γ * I) * Rt (z - 2 * γ * I))

/-- `Ψ = (z−1)³ F(z)`. -/
noncomputable def Psi (γ : ℝ) (z : ℂ) : ℂ := Lpart γ z * Rest γ z

/-- The region of holomorphy used. -/
def Om : Set ℂ := {z : ℂ | 3 / 5 < z.re} ∩ {z : ℂ | |z.im| < 1 / 2}

lemma isOpen_Om : IsOpen Om :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

lemma differentiable_Ln : Differentiable ℂ Ln := fun w =>
  (tauLSeries_entire _).comp w (differentiableAt_id.add_const _)

lemma differentiable_Lpart (γ : ℝ) : Differentiable ℂ (Lpart γ) := by
  have h := differentiable_Ln
  unfold Lpart; fun_prop

lemma two_mul_ne_one {z : ℂ} (hz : 3 / 5 < z.re) (c : ℝ) : 2 * z + c * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma shift_ne_one {z : ℂ} (hz : |z.im| < 1 / 2) {γ : ℝ} (hγ : 1 ≤ |γ|) (e : ℝ)
    (he : |e| = 2) : z + e * γ * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  have h1 : z.im = -(e * γ) := by linarith
  have h2 : |z.im| = 2 * |γ| := by rw [h1, abs_neg, abs_mul, he]
  linarith

lemma differentiableAt_Rest {γ : ℝ} (hγ : 1 ≤ |γ|) {z : ℂ} (hz : z ∈ Om) :
    DifferentiableAt ℂ (Rest γ) z := by
  obtain ⟨h1, h2⟩ := hz
  simp only [mem_setOf_eq] at h1 h2
  have hZ : DifferentiableAt ℂ Z1 z := differentiableAt_Z1 (by linarith)
  have hR : DifferentiableAt ℂ R1 z := differentiableAt_R1 h1
  have hz2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z := by
    have : 2 * z ≠ 1 := by simpa using two_mul_ne_one h1 0
    exact (differentiableAt_riemannZeta this).comp z (differentiableAt_id.const_mul 2)
  have hz3 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z + 4 * γ * I)) z := by
    have : 2 * z + 4 * γ * I ≠ 1 := by simpa [mul_assoc] using two_mul_ne_one h1 (4 * γ)
    exact (differentiableAt_riemannZeta this).comp z (by fun_prop)
  have hz4 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z - 4 * γ * I)) z := by
    have : 2 * z - 4 * γ * I ≠ 1 := by
      have := two_mul_ne_one h1 (-(4 * γ))
      simpa [sub_eq_add_neg, mul_assoc] using this
    exact (differentiableAt_riemannZeta this).comp z (by fun_prop)
  have hr3 : DifferentiableAt ℂ (fun z : ℂ => Rt (z + 2 * γ * I)) z := by
    have hne : z + 2 * γ * I ≠ 1 := by
      have := shift_ne_one h2 hγ 2 (by norm_num)
      simpa using this
    exact (differentiableAt_Rt (by simpa using h1) hne).comp
      (f := fun w : ℂ => w + 2 * γ * I) z (by fun_prop)
  have hr4 : DifferentiableAt ℂ (fun z : ℂ => Rt (z - 2 * γ * I)) z := by
    have hne : z - 2 * γ * I ≠ 1 := by
      have := shift_ne_one h2 hγ (-2) (by norm_num)
      simpa [sub_eq_add_neg] using this
    exact (differentiableAt_Rt (by simpa using h1) hne).comp
      (f := fun w : ℂ => w - 2 * γ * I) z (by fun_prop)
  exact ((hZ.mul ((hz2.mul hR).mul (hz2.mul hR))).mul (hz3.mul hr3)).mul (hz4.mul hr4)

lemma differentiableOn_Rest {γ : ℝ} (hγ : 1 ≤ |γ|) : DifferentiableOn ℂ (Rest γ) Om := fun z hz =>
  (differentiableAt_Rest hγ hz).differentiableWithinAt

lemma differentiableOn_Psi {γ : ℝ} (hγ : 1 ≤ |γ|) : DifferentiableOn ℂ (Psi γ) Om := fun z hz =>
  ((differentiable_Lpart γ z).mul (differentiableAt_Rest hγ hz)).differentiableWithinAt

lemma analyticOnNhd_Psi {γ : ℝ} (hγ : 1 ≤ |γ|) : AnalyticOnNhd ℂ (Psi γ) Om :=
  (differentiableOn_Psi hγ).analyticOnNhd isOpen_Om

lemma closedBall_subset_Om {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) :
    closedBall ((1 + δ : ℝ) : ℂ) (1 / 4) ⊆ Om := by
  intro z hz
  rw [mem_closedBall, dist_eq] at hz
  have h1 := Complex.abs_re_le_norm (z - ((1 + δ : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (z - ((1 + δ : ℝ) : ℂ))
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [mem_setOf_eq]
    have := (abs_le.mp (h1.trans hz)).1
    linarith
  · simp only [mem_setOf_eq]
    linarith

/-- `Ψ(σ) = (σ−1)³ F(σ)` for real `σ > 1`. -/
theorem Psi_real (γ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Psi γ (σ : ℂ) = ((σ : ℂ) - 1) ^ 3 * Fval σ γ := by
  have hre : 1 < (σ : ℂ).re := by simpa using hσ
  have hp : 1 < ((σ : ℂ) + 2 * γ * I).re := by simpa using hσ
  have hm : 1 < ((σ : ℂ) - 2 * γ * I).re := by simpa using hσ
  rw [Psi, Lpart, Rest, Z1_eq hre, R1_eq hre, Rt_eq hp, Rt_eq hm, Fval]
  have e1 : (σ : ℂ) + γ * I + 11 / 2 = sL σ γ := by simp [sL]; ring
  have e2 : (σ : ℂ) - γ * I + 11 / 2 = sL σ (-γ) := by simp [sL]; ring
  have e3 : (σ : ℂ) + 2 * γ * I = sR σ γ := by simp [sR]
  have e4 : (σ : ℂ) - 2 * γ * I = sR σ (-γ) := by simp [sR]; ring
  have e5 : 2 * (σ : ℂ) + 4 * γ * I = 2 * sR σ γ := by simp [sR]; ring
  have e6 : 2 * (σ : ℂ) - 4 * γ * I = 2 * sR σ (-γ) := by simp [sR]; ring
  simp only [Ln, e1, e2, e3, e4, e5, e6]
  ring

/-- `Ψ` has no zeros on `Re u > 1`. -/
theorem Psi_ne_zero (γ : ℝ) {u : ℂ} (hu : 1 < u.re) : Psi γ u ≠ 0 := by
  have hu1 : u - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hL : ∀ e : ℝ, Ln (u + e * I) ≠ 0 := fun e =>
    HeckeZeros.tauL_ne_zero_of_gt (by simp; linarith)
  have hL' : Ln (u - γ * I) ≠ 0 := by
    have := hL (-γ); simpa [sub_eq_add_neg] using this
  have hZ : ∀ w : ℂ, 1 < w.re → riemannZeta w ≠ 0 := fun w hw => riemannZeta_ne_zero_of_one_lt_re hw
  have hRt : ∀ w : ℂ, 1 < w.re → Rt w ≠ 0 := fun w hw => by
    rw [Rt_eq hw]; exact RS_ne_zero hw
  rw [Psi, Lpart, Rest, Z1_eq hu, R1_eq hu]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (hL γ) (hL γ)) (mul_ne_zero hL' hL')) ?_
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact mul_ne_zero hu1 (hZ u hu)
  · have h2 : riemannZeta (2 * u) * ((u - 1) * RS u) ≠ 0 :=
      mul_ne_zero (hZ _ (by simp; linarith)) (mul_ne_zero hu1 (RS_ne_zero hu))
    exact mul_ne_zero h2 h2
  · exact mul_ne_zero (hZ _ (by simp; linarith)) (hRt _ (by simp; linarith))
  · exact mul_ne_zero (hZ _ (by simp; linarith)) (hRt _ (by simp; linarith))

/-- A zero `L(β+iγ) = 0` gives a zero of order `≥ 4` of `Ψ` at `β`. -/
theorem four_le_order {γ : ℝ} (hγ : 1 ≤ |γ|) {β : ℝ} (hβ : (β : ℂ) ∈ Om)
    (h0 : Ln ((β : ℂ) + γ * I) = 0) : (4 : ℕ∞) ≤ analyticOrderAt (Psi γ) (β : ℂ) := by
  have h0' : Ln ((β : ℂ) - γ * I) = 0 := by
    have := HeckeZeros.tauL_zero_conj h0
    show tauL _ = 0
    convert this using 2
    apply Complex.ext <;> simp [map_ofNat]
  set b : ℂ := (β : ℂ)
  have hA : ∀ e : ℂ, AnalyticAt ℂ (fun z => Ln (z + e)) b := fun e =>
    (differentiable_Ln.comp (differentiable_id.add_const e)).analyticAt b
  have hB := hA (γ * I)
  have hC : AnalyticAt ℂ (fun z => Ln (z - γ * I)) b := by
    simpa [sub_eq_add_neg] using hA (-(γ * I))
  have hR : AnalyticAt ℂ (Rest γ) b :=
    (differentiableOn_Rest hγ).analyticOnNhd isOpen_Om b hβ
  have o1 : 1 ≤ analyticOrderAt (fun z => Ln (z + γ * I)) b :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hB, h0⟩)
  have o2 : 1 ≤ analyticOrderAt (fun z => Ln (z - γ * I)) b :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hC, h0'⟩)
  have hfun : Psi γ = ((fun z => Ln (z + γ * I)) * (fun z => Ln (z + γ * I)) *
      ((fun z => Ln (z - γ * I)) * (fun z => Ln (z - γ * I)))) * Rest γ := by
    funext z; simp [Psi, Lpart]
  rw [hfun, analyticOrderAt_mul ((hB.mul hB).mul (hC.mul hC)) hR,
    analyticOrderAt_mul (hB.mul hB) (hC.mul hC), analyticOrderAt_mul hB hB,
    analyticOrderAt_mul hC hC]
  have : (4 : ℕ∞) = 1 + 1 + (1 + 1) + 0 := by norm_num
  rw [this]
  gcongr
  exact bot_le

/-! ### Growth on the disc `|z − (1+δ)| ≤ 1/4` -/

lemma norm_zeta_le_of_re {w : ℂ} (hw : 3 / 2 ≤ w.re) :
    ‖riemannZeta w‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by linarith)]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine tsum_of_norm_bounded hs.hasSum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
    simp [zero_cpow hw0]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]
    exact one_div_le_one_div_of_le (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 hw)

lemma ball_facts {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) {z : ℂ}
    (hz : z ∈ closedBall ((1 + δ : ℝ) : ℂ) (1 / 4)) :
    3 / 4 ≤ z.re ∧ z.re ≤ 11 / 8 ∧ |z.im| ≤ 1 / 4 ∧ ‖z‖ ≤ 2 := by
  rw [mem_closedBall, dist_eq] at hz
  have h1 := Complex.abs_re_le_norm (z - ((1 + δ : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (z - ((1 + δ : ℝ) : ℂ))
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
  have h3 := (abs_le.mp (h1.trans hz))
  refine ⟨by linarith [h3.1], by linarith [h3.2], h2.trans hz, ?_⟩
  have : ‖z‖ ≤ ‖z - ((1 + δ : ℝ) : ℂ)‖ + ‖((1 + δ : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
  linarith

lemma norm_Ln_shift_le {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s : ℂ, 5 ≤ s.re → s.re ≤ 9 → ‖tauL s‖ ≤ A * (1 + ‖s‖) ^ 2)
    {z : ℂ} (h1 : 3 / 4 ≤ z.re) (h2 : z.re ≤ 11 / 8) (h4 : ‖z‖ ≤ 2) (e : ℝ) :
    ‖Ln (z + e * I)‖ ≤ A * (9 + |e|) ^ 2 := by
  have hre : (z + e * I + 11 / 2).re = z.re + 11 / 2 := by simp
  have hn : 1 + ‖z + e * I + 11 / 2‖ ≤ 9 + |e| := by
    have : ‖z + e * I + 11 / 2‖ ≤ ‖z‖ + ‖(e : ℂ) * I‖ + ‖(11 / 2 : ℂ)‖ := norm_add₃_le
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
    have h112 : ‖(11 / 2 : ℂ)‖ = 11 / 2 := by
      rw [show (11 / 2 : ℂ) = ((11 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]
      norm_num
    linarith
  calc ‖Ln (z + e * I)‖ ≤ A * (1 + ‖z + e * I + 11 / 2‖) ^ 2 :=
        hA _ (by rw [hre]; linarith) (by rw [hre]; linarith)
    _ ≤ A * (9 + |e|) ^ 2 := by gcongr

lemma norm_Rt_shift_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 3 / 5 < s.re → ‖Rt s‖ ≤ |rsc| * ‖s‖ / ‖s - 1‖ + ‖s‖ * (K / (s.re - 3 / 5)))
    {z : ℂ} (h1 : 3 / 4 ≤ z.re) (h3 : |z.im| ≤ 1 / 4) (h4 : ‖z‖ ≤ 2) {γ : ℝ} (hγ : 1 ≤ |γ|)
    (e : ℝ) (he : |e| = 2) :
    ‖Rt (z + e * γ * I)‖ ≤ (|rsc| + 7 * K) * (2 * (9 + |γ|)) := by
  set w := z + e * γ * I
  have hwre : w.re = z.re := by simp [w]
  have hwim : w.im = z.im + e * γ := by simp [w]
  have hwn : ‖w‖ ≤ 2 * (9 + |γ|) := by
    have : ‖w‖ ≤ ‖z‖ + ‖(e : ℂ) * γ * I‖ := norm_add_le _ _
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, he] at this
    linarith
  have hw1 : 1 ≤ ‖w - 1‖ := by
    have h := Complex.abs_im_le_norm (w - 1)
    have hi : (w - 1).im = z.im + e * γ := by simp [hwim]
    rw [hi] at h
    have : |e * γ| = 2 * |γ| := by rw [abs_mul, he]
    have h5 : |e * γ| ≤ |z.im + e * γ| + |z.im| := by
      have := abs_sub_abs_le_abs_sub (z.im + e * γ) z.im
      have h6 : |z.im + e * γ - z.im| = |e * γ| := by ring_nf
      have := abs_add_le (z.im + e * γ) (-z.im)
      rw [abs_neg] at this
      calc |e * γ| = |z.im + e * γ + -z.im| := by ring_nf
        _ ≤ _ := this
    linarith
  have hb := hK w (by rw [hwre]; linarith)
  have hd1 : |rsc| * ‖w‖ / ‖w - 1‖ ≤ |rsc| * ‖w‖ :=
    div_le_self (by positivity) hw1
  have hd2 : K / (w.re - 3 / 5) ≤ 7 * K := by
    rw [hwre, div_le_iff₀ (by linarith)]
    nlinarith
  calc ‖Rt w‖ ≤ |rsc| * ‖w‖ + ‖w‖ * (7 * K) := by
        have := mul_le_mul_of_nonneg_left hd2 (norm_nonneg w)
        linarith
    _ = (|rsc| + 7 * K) * ‖w‖ := by ring
    _ ≤ (|rsc| + 7 * K) * (2 * (9 + |γ|)) := by gcongr

/-- **Polynomial growth of `Ψ`** on the disc. -/
theorem norm_Psi_le : ∃ B : ℝ, 1 ≤ B ∧ ∀ γ : ℝ, 1 ≤ |γ| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
    ∀ z ∈ closedBall ((1 + δ : ℝ) : ℂ) (1 / 4), ‖Psi γ z‖ ≤ B * (9 + |γ|) ^ 10 := by
  obtain ⟨A, hA0, hA⟩ := ZeroCount.tauL_poly_bound
  obtain ⟨K, hK0, hK⟩ := norm_Rt_le
  set Zb : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ ((3 : ℝ) / 2) with hZb
  have hZb0 : 0 ≤ Zb := tsum_nonneg fun n => by positivity
  set f0 : ℂ → ℂ := fun z => Z1 z * ((riemannZeta (2 * z) * R1 z) * (riemannZeta (2 * z) * R1 z))
    with hf0
  have hK0Om : closedBall (1 : ℂ) (3 / 8) ⊆ Om := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - 1)
    have h2 := Complex.abs_im_le_norm (z - 1)
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h1 h2
    refine ⟨?_, ?_⟩
    · simp only [mem_setOf_eq]; linarith [(abs_le.mp (h1.trans hz)).1]
    · simp only [mem_setOf_eq]; linarith
  have hcont : ContinuousOn f0 (closedBall (1 : ℂ) (3 / 8)) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hK0Om hz
    simp only [mem_setOf_eq] at h1 h2
    have hZ : DifferentiableAt ℂ Z1 z := differentiableAt_Z1 (by linarith)
    have hR : DifferentiableAt ℂ R1 z := differentiableAt_R1 h1
    have hz2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z := by
      have : 2 * z ≠ 1 := by simpa using two_mul_ne_one h1 0
      exact (differentiableAt_riemannZeta this).comp z (differentiableAt_id.const_mul 2)
    exact (hZ.mul ((hz2.mul hR).mul (hz2.mul hR))).continuousAt.continuousWithinAt
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (1 : ℂ) (3 / 8)).exists_bound_of_continuousOn hcont
  set C0' := max C0 0
  set B := max 1 (A ^ 4 * C0' * (Zb * ((|rsc| + 7 * K) * 2)) ^ 2) with hB
  refine ⟨B, le_max_left _ _, fun γ hγ δ hδ0 hδ z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := ball_facts hδ0 hδ hz
  have hzK : z ∈ closedBall (1 : ℂ) (3 / 8) := by
    rw [mem_closedBall, dist_eq]
    rw [mem_closedBall, dist_eq] at hz
    have : ‖z - 1‖ ≤ ‖z - ((1 + δ : ℝ) : ℂ)‖ + ‖((1 + δ : ℝ) : ℂ) - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have e : ((1 + δ : ℝ) : ℂ) - 1 = ((δ : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at this
    linarith
  have hf0b : ‖f0 z‖ ≤ C0' := (hC0 z hzK).trans (le_max_left _ _)
  have hC0' : 0 ≤ C0' := le_max_right _ _
  set T := |γ|
  have hT : 0 ≤ T := abs_nonneg _
  have hLa := norm_Ln_shift_le hA0 hA h1 h2 h4 γ
  have hLb : ‖Ln (z - γ * I)‖ ≤ A * (9 + T) ^ 2 := by
    have := norm_Ln_shift_le hA0 hA h1 h2 h4 (-γ)
    simpa [sub_eq_add_neg, abs_neg] using this
  have hRa : ‖Rt (z + 2 * γ * I)‖ ≤ (|rsc| + 7 * K) * (2 * (9 + T)) := by
    have := norm_Rt_shift_le hK0 hK h1 h3 h4 hγ 2 (by norm_num)
    simpa using this
  have hRb : ‖Rt (z - 2 * γ * I)‖ ≤ (|rsc| + 7 * K) * (2 * (9 + T)) := by
    have := norm_Rt_shift_le hK0 hK h1 h3 h4 hγ (-2) (by norm_num)
    simpa [sub_eq_add_neg] using this
  have hZa : ‖riemannZeta (2 * z + 4 * γ * I)‖ ≤ Zb :=
    norm_zeta_le_of_re (by simp; linarith)
  have hZbb : ‖riemannZeta (2 * z - 4 * γ * I)‖ ≤ Zb :=
    norm_zeta_le_of_re (by simp; linarith)
  have hPsi : ‖Psi γ z‖ = ‖Ln (z + γ * I)‖ ^ 2 * ‖Ln (z - γ * I)‖ ^ 2 * ‖f0 z‖ *
      (‖riemannZeta (2 * z + 4 * γ * I)‖ * ‖Rt (z + 2 * γ * I)‖) *
      (‖riemannZeta (2 * z - 4 * γ * I)‖ * ‖Rt (z - 2 * γ * I)‖) := by
    simp only [Psi, Lpart, Rest, hf0, norm_mul]; ring
  have hRK : 0 ≤ |rsc| + 7 * K := by positivity
  calc ‖Psi γ z‖ ≤ (A * (9 + T) ^ 2) ^ 2 * (A * (9 + T) ^ 2) ^ 2 * C0' *
        (Zb * ((|rsc| + 7 * K) * (2 * (9 + T)))) * (Zb * ((|rsc| + 7 * K) * (2 * (9 + T)))) := by
        rw [hPsi]; gcongr
    _ = (A ^ 4 * C0' * (Zb * ((|rsc| + 7 * K) * 2)) ^ 2) * (9 + T) ^ 10 := by ring
    _ ≤ B * (9 + T) ^ 10 := by gcongr; exact le_max_right _ _

end RamanujanTau.ZeroFreeRegion
