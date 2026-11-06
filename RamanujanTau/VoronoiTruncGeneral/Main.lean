/-
# The `L²`-truncated Voronoi formula, the Cramér limit and exact `Ω±` for every level-one cusp form

Evidence level (1): Lean, axiom-clean, unconditional; Deligne is not used.

For `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0`, with real q-expansion coefficients `a(n) = (coef f n).re`
(`hreal : ∀ n, (coef f n).im = 0`), `S(x) = Σ_{n≤x} a(n)`:

* `cusp_voronoi_truncated_L2` (A): for every `0 < θ ≤ 1/4`,

      X^{−(k+1/2)} ∫_X^{2X} ( S(x) − x^{(k−1)/2+1/4}/(π√2) Σ_{n≤X^θ} a(n) n^{−(k/2+1/4)} cos(4π√(nx) − π/4) )² dx → 0.

  The phase is `−π/4` for every even `k`: the factor `(−1)^{k/2} = i^{−k}` of the modular relation
  cancels the sign `(−1)^{k/2}` of `J_k(2L) ~ cos(2L − kπ/2 − π/4)/√(πL)` (`Ik_asymp_even`).
* `cusp_voronoi_truncated_L2_rate` (A′): majorant `C X^{k+1/2}(X^{−1/16} + Σ_{n>X^θ} a(n)² n^{−(k+1/2)})`.
* `cusp_cramer` (B): `X^{−(k+1/2)} ∫₁^X S(x)² dx → (Σ a(n)² n^{−(k+1/2)}) / ((4k+2)π²)`
  (for `k = 12`: `B/(50π²)`).
* `cusp_omega_pm_exact` (B′): if `a(1) ≠ 0`, for every `c < |a(1)|/(2π√2)` and all large `X` both
  `S(x) > c x^{(k−1)/2+1/4}` and `S(x) < −c x^{(k−1)/2+1/4}` occur in `[X, 2X]`;
  `eigenform_omega_pm_exact`: the case of a normalized Hecke eigenform (`a(1) = 1`).

The analytic core (`Data` … `Omega`) is proved for any real sequence satisfying `VData m a`
(modular relation of weight `2m` with sign `(−1)^m`, Rankin's bound `Σ_{n≤N} a(n)² ≪ N^{2m}`);
`Cusp.lean` supplies it for cusp forms.

Build: `nice -n 10 lake build RamanujanTau.VoronoiTruncGeneral.Main`.  See `docs/VORONOI_TRUNC_GENERAL.md`.
-/
import RamanujanTau.VoronoiTruncGeneral.Omega
import RamanujanTau.VoronoiTruncGeneral.Cusp
import RamanujanTau.HardyZerosGeneral.Main
import RamanujanTau.EigenformEdge.Eigenform

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- The real coefficient sequence `a(n) = Re a_f(n)`. -/
noncomputable def cre (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : ℝ := (coef f n).re

/-- A nonzero level-one cusp form has weight `k = 2m` with `m ≥ 6`. -/
lemma exists_half (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : ∃ m : ℕ, k = 2 * m ∧ 6 ≤ m := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | h
  · refine ⟨m, by omega, ?_⟩
    by_contra hlt
    exact hf (eq_zero_of_lt_twelve f (by omega))
  · exact absurd (RamanujanTau.HardyZerosGeneral.eq_zero_of_odd f h) hf

lemma vdata_cre (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hreal : ∀ n, (coef f n).im = 0) :
    ∃ m : ℕ, k = 2 * m ∧ VData m (cre f) := by
  obtain ⟨m, hk, hm⟩ := exists_half f hf
  exact ⟨m, hk, vdata_of_cusp hk (by omega) f (coef_eq_re f hreal)⟩

lemma exps {m : ℕ} (hk : k = 2 * m) :
    ((k : ℝ) - 1) / 2 + 1 / 4 = (m : ℝ) - 1 / 4 ∧ (k : ℝ) / 2 + 1 / 4 = (m : ℝ) + 1 / 4 ∧
      (k : ℝ) + 1 / 2 = 2 * (m : ℝ) + 1 / 2 := by
  subst hk; push_cast; refine ⟨by ring, by ring, by ring⟩

lemma Vth_eq_explicit (m : ℕ) (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    Vth m a N x = x ^ ((m : ℝ) - 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 N,
      a n * (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4) := by
  unfold Vth bco th
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  ring_nf

lemma Sre_eq (a : ℕ → ℝ) (x : ℝ) : Sre a x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := rfl

/-- **(A) The `L²`-truncated Voronoi formula for every nonzero real level-one cusp form.** -/
theorem cusp_voronoi_truncated_L2 (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re -
          x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (coef f n).re * (n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop (𝓝 0) := by
  obtain ⟨m, hk, hd⟩ := vdata_cre f hf hreal
  obtain ⟨e1, e2, e3⟩ := exps hk
  rw [e1, e2, e3]
  refine (voronoi_L2 hd hθ0 hθ).congr fun X => ?_
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  show (Sre (cre f) x - Vth m (cre f) ⌊X ^ θ⌋₊ x) ^ 2 = _
  rw [Vth_eq_explicit, Sre_eq]; rfl

/-- **(A′) With an explicit rate.** -/
theorem cusp_voronoi_truncated_L2_rate (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 144 ≤ X →
      ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re -
          x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (coef f n).re * (n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2 ≤
        C * X ^ ((k : ℝ) + 1 / 2) * (X ^ (-(1 / 16) : ℝ) +
          ∑' j : ℕ, (coef f (j + (⌊X ^ θ⌋₊ + 1))).re ^ 2 *
            ((j + (⌊X ^ θ⌋₊ + 1) : ℕ) : ℝ) ^ (-((k : ℝ) + 1 / 2))) := by
  obtain ⟨m, hk, hd⟩ := vdata_cre f hf hreal
  obtain ⟨e1, e2, e3⟩ := exps hk
  rw [e1, e2, e3]
  obtain ⟨C, hC0, hC⟩ := voronoi_L2_bound hd hθ0 hθ
  refine ⟨C, hC0, fun X hX => ?_⟩
  have h := hC X hX
  rw [intervalIntegral.integral_of_le (by linarith)]
  have e4 : ∫ x in Ioc X (2 * X), (Sre (cre f) x - Vth m (cre f) ⌊X ^ θ⌋₊ x) ^ 2 =
      ∫ x in Ioc X (2 * X), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re -
          x ^ ((m : ℝ) - 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (coef f n).re * (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2 := by
    congr 1; funext x; rw [Vth_eq_explicit, Sre_eq]; rfl
  have e5 : tl m (cre f) ⌊X ^ θ⌋₊ = ∑' j : ℕ, (coef f (j + (⌊X ^ θ⌋₊ + 1))).re ^ 2 *
      ((j + (⌊X ^ θ⌋₊ + 1) : ℕ) : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) := by
    unfold tl; congr 1; funext j; rw [sq_bco]; rfl
  rw [← e4, ← e5]; exact h

/-- **(B) The Cramér–Tong limit for every nonzero real level-one cusp form**:
`X^{−(k+1/2)} ∫₁^X S(x)² dx → (Σ a(n)² n^{−(k+1/2)}) / ((4k+2)π²)`. -/
theorem cusp_cramer (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hreal : ∀ n, (coef f n).im = 0) :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop
      (𝓝 ((∑' n : ℕ, (coef f n).re ^ 2 * (n : ℝ) ^ (-((k : ℝ) + 1 / 2))) / ((4 * k + 2) * π ^ 2))) := by
  obtain ⟨m, hk, hd⟩ := vdata_cre f hf hreal
  obtain ⟨-, -, e3⟩ := exps hk
  have e4 : (4 * (k : ℝ) + 2) = 8 * (m : ℝ) + 2 := by rw [hk]; push_cast; ring
  rw [e3, e4]
  have hB : Bsum m (cre f) = ∑' n : ℕ, (coef f n).re ^ 2 * (n : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) := by
    unfold Bsum; congr 1; funext n; rw [sq_bco]; rfl
  rw [← hB]
  exact cramer_core hd

/-- `Sre` of a rescaled sequence. -/
lemma Sre_smul (a : ℕ → ℝ) (c x : ℝ) : Sre (fun n => c * a n) x = c * Sre a x := by
  unfold Sre; rw [Finset.mul_sum]

/-- **(B′) Exact `Ω±(x^{(k−1)/2+1/4})` in every dyadic interval** for every nonzero real level-one
cusp form with `a(1) ≠ 0`, with constant `|a(1)|/(2π√2)`. -/
theorem cusp_omega_pm_exact (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) (h1 : (coef f 1).re ≠ 0) {c : ℝ}
    (hc : c < |(coef f 1).re| / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ∧
      (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  obtain ⟨m, hk, hd⟩ := vdata_cre f hf hreal
  obtain ⟨e1, -, -⟩ := exps hk
  rw [e1]
  set α := (coef f 1).re with hα
  have hαa : 0 < |α| := abs_pos.2 h1
  set b : ℕ → ℝ := fun n => α⁻¹ * cre f n with hbdef
  have hb : VData m b := hd.smul α⁻¹
  have hb1 : b 1 = 1 := by simp only [hbdef, cre]; rw [← hα]; field_simp
  have hSb : ∀ x, Sre b x = α⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re := fun x => Sre_smul _ _ _
  set c' := c / |α| with hc'
  have hc'lt : c' < 1 / (2 * π * √2) := by
    rw [hc', div_lt_iff₀ hαa]
    have : |α| / (2 * π * √2) = 1 / (2 * π * √2) * |α| := by ring
    linarith
  have hcα : c' * |α| = c := by rw [hc']; field_simp
  filter_upwards [omega_plus hb hb1 hc'lt, omega_minus hb hb1 hc'lt] with X hP hM
  obtain ⟨x1, hx1, hP1⟩ := hP
  obtain ⟨x2, hx2, hM2⟩ := hM
  rw [hSb] at hP1 hM2
  set S1 := ∑ n ∈ Finset.Icc 1 ⌊x1⌋₊, (coef f n).re
  set S2 := ∑ n ∈ Finset.Icc 1 ⌊x2⌋₊, (coef f n).re
  rcases lt_or_gt_of_ne h1 with hneg | hpos
  · -- `α < 0`: the signs swap
    have habs : |α| = -α := abs_of_neg hneg
    refine ⟨⟨x2, hx2, ?_⟩, ⟨x1, hx1, ?_⟩⟩
    · -- from `S2/α < −c' x2^e`
      have : α⁻¹ * S2 * α > -c' * x2 ^ ((m : ℝ) - 1 / 4) * α :=
        mul_lt_mul_of_neg_right hM2 hneg
      rw [show α⁻¹ * S2 * α = S2 by field_simp] at this
      have e : -c' * x2 ^ ((m : ℝ) - 1 / 4) * α = c * x2 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
    · have : c' * x1 ^ ((m : ℝ) - 1 / 4) * α > α⁻¹ * S1 * α :=
        mul_lt_mul_of_neg_right hP1 hneg
      rw [show α⁻¹ * S1 * α = S1 by field_simp] at this
      have e : c' * x1 ^ ((m : ℝ) - 1 / 4) * α = -c * x1 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
  · have habs : |α| = α := abs_of_pos hpos
    refine ⟨⟨x1, hx1, ?_⟩, ⟨x2, hx2, ?_⟩⟩
    · have : c' * x1 ^ ((m : ℝ) - 1 / 4) * α < α⁻¹ * S1 * α :=
        mul_lt_mul_of_pos_right hP1 hpos
      rw [show α⁻¹ * S1 * α = S1 by field_simp] at this
      have e : c' * x1 ^ ((m : ℝ) - 1 / 4) * α = c * x1 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith
    · have : α⁻¹ * S2 * α < -c' * x2 ^ ((m : ℝ) - 1 / 4) * α :=
        mul_lt_mul_of_pos_right hM2 hpos
      rw [show α⁻¹ * S2 * α = S2 by field_simp] at this
      have e : -c' * x2 ^ ((m : ℝ) - 1 / 4) * α = -c * x2 ^ ((m : ℝ) - 1 / 4) := by
        rw [← hcα, habs]; ring
      linarith

/-- **(B′) for a normalized Hecke eigenform**: exact `Ω±(x^{(k−1)/2+1/4})` in every dyadic
interval with constant `1/(2π√2)`. -/
theorem eigenform_omega_pm_exact (f : CuspForm 𝒮ℒ (k : ℤ))
    (hf : RamanujanTau.EigenformEdge.IsNormalizedEigenform f) {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ∧
      (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  have h1 : (coef f 1).re = 1 := by rw [hf.one]; simp
  refine cusp_omega_pm_exact f hf.ne_zero hf.real (by rw [h1]; norm_num) ?_
  rw [h1, abs_one]; exact hc

/-- `Ω±` in the unbounded form: `S(x) > c x^{(k−1)/2+1/4}` and `S(x) < −c x^{(k−1)/2+1/4}` for
arbitrarily large `x`. -/
theorem cusp_partial_sum_omega_pm_exact (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) (h1 : (coef f 1).re ≠ 0) {c : ℝ}
    (hc : c < |(coef f 1).re| / (2 * π * √2)) (X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) := by
  obtain ⟨Y, hY⟩ := (cusp_omega_pm_exact f hf hreal h1 hc).exists_forall_of_atTop
  obtain ⟨⟨x1, hx1, h1'⟩, ⟨x2, hx2, h2'⟩⟩ := hY (max X Y) (le_max_right _ _)
  exact ⟨⟨x2, le_trans (le_max_left _ _) hx2.1, h2'⟩, ⟨x1, le_trans (le_max_left _ _) hx1.1, h1'⟩⟩

/-- The kernel asymptotic with phase for even index (`(−1)^m I_{2m}(L) ≈ cos(2L − π/4)/√(πL)`). -/
theorem kernel_asymp_even {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L) :
    |(-1 : ℝ) ^ m * VoronoiTrunc.Ik (2 * m) L - Real.cos (2 * L - π / 4) / √(π * L)| ≤
      VoronoiTrunc.Ck (2 * m) / (π * L) :=
  Ik_asymp_even hm hL

end RamanujanTau.VoronoiTruncGeneral

#print axioms RamanujanTau.VoronoiTruncGeneral.cusp_voronoi_truncated_L2
#print axioms RamanujanTau.VoronoiTruncGeneral.cusp_voronoi_truncated_L2_rate
#print axioms RamanujanTau.VoronoiTruncGeneral.cusp_cramer
#print axioms RamanujanTau.VoronoiTruncGeneral.cusp_omega_pm_exact
#print axioms RamanujanTau.VoronoiTruncGeneral.eigenform_omega_pm_exact
#print axioms RamanujanTau.VoronoiTruncGeneral.cusp_partial_sum_omega_pm_exact
#print axioms RamanujanTau.VoronoiTruncGeneral.kernel_asymp_even
#print axioms RamanujanTau.VoronoiTruncGeneral.vdata_of_cusp
#print axioms RamanujanTau.VoronoiTruncGeneral.Dq_modular_cusp
#print axioms RamanujanTau.VoronoiTruncGeneral.dual_W
#print axioms RamanujanTau.VoronoiTruncGeneral.kB_eq_Ik
#print axioms RamanujanTau.VoronoiTruncGeneral.DkC_WC_eq
#print axioms RamanujanTau.VoronoiTruncGeneral.mean_value
#print axioms RamanujanTau.VoronoiTruncGeneral.voronoi_L2
#print axioms RamanujanTau.VoronoiTruncGeneral.cramer_core
#print axioms RamanujanTau.VoronoiTruncGeneral.omega_plus
#print axioms RamanujanTau.VoronoiTruncGeneral.omega_minus
