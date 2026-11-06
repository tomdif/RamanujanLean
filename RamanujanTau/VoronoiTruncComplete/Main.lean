/-
# Voronoi / Cramér / `Ω±` for every nonzero level-one cusp form: no `a(1) ≠ 0`, complex coefficients

Evidence level (1): Lean, axiom-clean, unconditional; Deligne is not used.

For `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0`, with q-expansion coefficients `a(n) = coef f n ∈ ℂ` and
`S_f(x) = Σ_{n≤x} a(n)`:

* `cusp_omega_pm_exact'` (gap 1 of `docs/VORONOI_TRUNC_GENERAL.md`): for real `f` let `n₀` be the
  first index with `a(n₀) ≠ 0`; for every `c < |a(n₀)| n₀^{−(k/2+1/4)}/(2π√2)` and all large `X`
  both `S(x) > c x^{(k−1)/2+1/4}` and `S(x) < −c x^{(k−1)/2+1/4}` occur in `[X, 2X]`.
  (Ingham's kernel `1 ± cos θ_{n₀}`; `Omega0.lean`.)
* `cusp_re_omega_pm`, `cusp_im_omega_pm`: the same for `Re S_f` and `Im S_f` of an arbitrary
  (complex) `f`, at the first index where `Re a` (resp. `Im a`) is nonzero.
* `cusp_cramer_complex` (gap 2): `X^{−(k+1/2)} ∫₁^X |S_f|² → Σ |a(n)|² n^{−(k+1/2)} / ((4k+2)π²)`.
* `cusp_voronoi_truncated_L2_complex` (gap 2): for `0 < θ ≤ 1/4`,
  `X^{−(k+1/2)} ∫_X^{2X} |S_f(x) − V_f(x)|² → 0`, where
  `V_f(x) = x^{(k−1)/2+1/4}/(π√2) Σ_{n≤X^θ} a(n) n^{−(k/2+1/4)} cos(4π√(nx) − π/4)` (complex).

Route for complex coefficients (`Complex.lean`): `Re a(n)` and `Im a(n)` each satisfy `VData`
directly (the modular relation passes to `Re(w a(n))` because `conj` commutes with `z ↦ 1/z`); then
`|S_f|² = (Re S_f)² + (Im S_f)²` and `|S_f − V_f|² = (S_{Re a} − V_{Re a})² + (S_{Im a} − V_{Im a})²`.
No real basis of `S_k` and no Hermitian mean-value theorem is needed.

Build: `nice -n 10 lake build RamanujanTau.VoronoiTruncComplete.Main`.  See
`docs/VORONOI_TRUNC_COMPLETE.md`.
-/
import RamanujanTau.VoronoiTruncComplete.Omega0
import RamanujanTau.VoronoiTruncComplete.Complex
import RamanujanTau.VoronoiTruncGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncComplete

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.HeckeConvexGeneral RamanujanTau.VoronoiTruncGeneral
open scoped MatrixGroups

variable {k : ℕ}

lemma re_partial (f : CuspForm 𝒮ℒ (k : ℤ)) (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re = Sre (fun n => (coef f n).re) x := by
  rw [Complex.re_sum]; rfl

lemma im_partial (f : CuspForm 𝒮ℒ (k : ℤ)) (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).im = Sre (fun n => (coef f n).im) x := by
  rw [Complex.im_sum]; rfl

/-- **`Ω±` for `Re S_f`** (any complex `f ≠ 0`) at the first index `n₀` with `Re a(n₀) ≠ 0`. -/
theorem cusp_re_omega_pm (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {n₀ : ℕ} (h0 : 1 ≤ n₀)
    (hz : ∀ n < n₀, (coef f n).re = 0) (hn₀ : (coef f n₀).re ≠ 0) {c : ℝ}
    (hc : c < |(coef f n₀).re| * (n₀ : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X),
        c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re) ∧
      (∃ x ∈ Icc X (2 * X),
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  obtain ⟨m, hk, hm⟩ := exists_half f hf
  obtain ⟨e1, e2, -⟩ := exps hk
  rw [e2] at hc
  rw [e1]
  simp_rw [re_partial]
  exact omega_pm_first (vdata_re hk (by omega) f) h0 hz hn₀ hc

/-- **`Ω±` for `Im S_f`** (any complex `f ≠ 0`) at the first index `n₀` with `Im a(n₀) ≠ 0`. -/
theorem cusp_im_omega_pm (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {n₀ : ℕ} (h0 : 1 ≤ n₀)
    (hz : ∀ n < n₀, (coef f n).im = 0) (hn₀ : (coef f n₀).im ≠ 0) {c : ℝ}
    (hc : c < |(coef f n₀).im| * (n₀ : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X),
        c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).im) ∧
      (∃ x ∈ Icc X (2 * X),
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).im < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  obtain ⟨m, hk, hm⟩ := exists_half f hf
  obtain ⟨e1, e2, -⟩ := exps hk
  rw [e2] at hc
  rw [e1]
  simp_rw [im_partial]
  exact omega_pm_first (vdata_im hk (by omega) f) h0 hz hn₀ hc

/-- A nonzero cusp form has a first nonzero coefficient `a(n₀)`, `n₀ ≥ 1`. -/
theorem exists_first_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ ∀ n < n₀, coef f n = 0 := by
  classical
  have hne : ∃ n, coef f n ≠ 0 := by
    by_contra h; push Not at h; exact hf (eq_zero_of_coef f h)
  refine ⟨Nat.find hne, ?_, Nat.find_spec hne, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hne) with h | h
    · exact absurd (h ▸ Nat.find_spec hne) (by simp [coef_zero])
    · exact h
  · by_contra h; exact Nat.find_min hne hn h

/-- **(B′) without `a(1) ≠ 0`: exact `Ω±(x^{(k−1)/2+1/4})` in every dyadic interval for every
nonzero real level-one cusp form**, with constant `|a(n₀)| n₀^{−(k/2+1/4)}/(2π√2)` at the first
nonzero coefficient `a(n₀)`. -/
theorem cusp_omega_pm_exact' (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ (∀ n < n₀, coef f n = 0) ∧
      ∀ c : ℝ, c < |(coef f n₀).re| * (n₀ : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) / (2 * π * √2) →
        ∀ᶠ X in atTop,
          (∃ x ∈ Icc X (2 * X),
            c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ∧
          (∃ x ∈ Icc X (2 * X),
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4)) := by
  obtain ⟨n₀, h0, hn₀, hz⟩ := exists_first_coef f hf
  refine ⟨n₀, h0, hn₀, hz, fun c hc => ?_⟩
  have hre : (coef f n₀).re ≠ 0 := by
    intro h; exact hn₀ (by rw [coef_eq_re f hreal n₀, h]; simp)
  have := cusp_re_omega_pm f hf h0 (fun n hn => by rw [hz n hn]; simp) hre hc
  simpa only [Complex.re_sum] using this

/-- **The Cramér–Tong limit for every nonzero level-one cusp form (complex coefficients)**:
`X^{−(k+1/2)} ∫₁^X |S_f(x)|² dx → (Σ |a(n)|² n^{−(k+1/2)}) / ((4k+2)π²)`. -/
theorem cusp_cramer_complex (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop
      (𝓝 ((∑' n : ℕ, ‖coef f n‖ ^ 2 * (n : ℝ) ^ (-((k : ℝ) + 1 / 2))) / ((4 * k + 2) * π ^ 2))) := by
  obtain ⟨m, hk, hm⟩ := exists_half f hf
  obtain ⟨-, -, e3⟩ := exps hk
  have e4 : (4 * (k : ℝ) + 2) = 8 * (m : ℝ) + 2 := by rw [hk]; push_cast; ring
  rw [e3, e4]
  set b : ℕ → ℝ := fun n => (coef f n).re
  set d : ℕ → ℝ := fun n => (coef f n).im
  have hdb : VData m b := vdata_re hk (by omega) f
  have hdd : VData m d := vdata_im hk (by omega) f
  have hβ : 2 * (m : ℝ) < 2 * (m : ℝ) + 1 / 2 := by linarith
  have hB : ∑' n : ℕ, ‖coef f n‖ ^ 2 * (n : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) = Bsum m b + Bsum m d := by
    unfold Bsum
    simp_rw [sq_bco]
    rw [← (hdb.summable_sq hβ).tsum_add (hdd.summable_sq hβ)]
    congr 1; funext n
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [b, d]; ring
  rw [hB, add_div]
  refine ((cramer_core hdb).add (cramer_core hdd)).congr fun X => ?_
  unfold Iq
  rw [← add_div]
  congr 1
  rw [← intervalIntegral.integral_add
    ⟨integrableOn_Sre_sq (a := b) 1 X, integrableOn_Sre_sq (a := b) X 1⟩
    ⟨integrableOn_Sre_sq (a := d) 1 X, integrableOn_Sre_sq (a := d) X 1⟩]
  refine intervalIntegral.integral_congr fun x _ => ?_
  try dsimp only
  rw [Complex.sq_norm, Complex.normSq_apply, re_partial, im_partial]; ring

/-- The complex truncated Voronoi sum. -/
noncomputable def Vf (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) (x : ℝ) : ℂ :=
  ((x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N,
    coef f n * (((n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
      Real.cos (4 * π * √((n : ℝ) * x) - π / 4) : ℝ) : ℂ)

lemma Vf_re {m : ℕ} (hk : k = 2 * m) (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) (x : ℝ) :
    (Vf f N x).re = Vth m (fun n => (coef f n).re) N x := by
  obtain ⟨e1, e2, -⟩ := exps hk
  rw [Vth_eq_explicit, Vf, Complex.re_ofReal_mul, Complex.re_sum, e1, e2]
  congr 1; refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_mul_ofReal]; ring

lemma Vf_im {m : ℕ} (hk : k = 2 * m) (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) (x : ℝ) :
    (Vf f N x).im = Vth m (fun n => (coef f n).im) N x := by
  obtain ⟨e1, e2, -⟩ := exps hk
  rw [Vth_eq_explicit, Vf, Complex.im_ofReal_mul, Complex.im_sum, e1, e2]
  congr 1; refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.im_mul_ofReal]; ring

/-- **(A) The `L²`-truncated Voronoi formula for every nonzero level-one cusp form (complex
coefficients)**: `X^{−(k+1/2)} ∫_X^{2X} |S_f − V_f|² → 0` for `0 < θ ≤ 1/4`. -/
theorem cusp_voronoi_truncated_L2_complex (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n -
          ((x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            coef f n * (((n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4) : ℝ) : ℂ)‖ ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop (𝓝 0) := by
  obtain ⟨m, hk, hm⟩ := exists_half f hf
  obtain ⟨-, -, e3⟩ := exps hk
  set b : ℕ → ℝ := fun n => (coef f n).re
  set d : ℕ → ℝ := fun n => (coef f n).im
  have hdb : VData m b := vdata_re hk (by omega) f
  have hdd : VData m d := vdata_im hk (by omega) f
  have hm1 : 1 ≤ m := by omega
  have h := (voronoi_L2 hdb hθ0 hθ).add (voronoi_L2 hdd hθ0 hθ)
  rw [add_zero] at h
  rw [e3]
  refine h.congr fun X => ?_
  rw [← add_div]
  congr 1
  rw [← intervalIntegral.integral_add
    ⟨integrableOn_D_sq (a := b) hm1 _ X (2 * X), integrableOn_D_sq (a := b) hm1 _ (2 * X) X⟩
    ⟨integrableOn_D_sq (a := d) hm1 _ X (2 * X), integrableOn_D_sq (a := d) hm1 _ (2 * X) X⟩]
  refine intervalIntegral.integral_congr fun x _ => ?_
  try dsimp only
  have hV := show ((x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) : ℝ) : ℂ) *
      ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, coef f n * (((n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
        Real.cos (4 * π * √((n : ℝ) * x) - π / 4) : ℝ) : ℂ) = Vf f ⌊X ^ θ⌋₊ x from rfl
  rw [hV, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, re_partial,
    im_partial, Vf_re hk, Vf_im hk]
  ring

end RamanujanTau.VoronoiTruncComplete

#print axioms RamanujanTau.VoronoiTruncComplete.cusp_omega_pm_exact'
#print axioms RamanujanTau.VoronoiTruncComplete.cusp_re_omega_pm
#print axioms RamanujanTau.VoronoiTruncComplete.cusp_im_omega_pm
#print axioms RamanujanTau.VoronoiTruncComplete.cusp_cramer_complex
#print axioms RamanujanTau.VoronoiTruncComplete.cusp_voronoi_truncated_L2_complex
#print axioms RamanujanTau.VoronoiTruncComplete.exists_first_coef
#print axioms RamanujanTau.VoronoiTruncComplete.omega_pm_first
#print axioms RamanujanTau.VoronoiTruncComplete.omega_core0
#print axioms RamanujanTau.VoronoiTruncComplete.term_int0
#print axioms RamanujanTau.VoronoiTruncComplete.vdata_re_mul
#print axioms RamanujanTau.VoronoiTruncComplete.eq_zero_of_coef
