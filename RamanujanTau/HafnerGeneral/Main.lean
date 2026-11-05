/-
# Hafner's theorem for every level-one cusp form with real coefficients: `N₀(T) ≫ T`

Let `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0`, with real Fourier coefficients.  Then there are `≫ T` distinct
`t ∈ (0, T]` with `L(f, k/2 + it) = 0` (J. L. Hafner, Math. Ann. 264 (1983)).
See `docs/HAFNER_GENERAL.md`.

* `k` odd or `k < 12`: `f = 0`; so `k = 2p + 2`, `p ≥ 5` (`GeneralCuspMoments.exists_weight_eq`).
* `Z(t) = Λ(f, p+1+it) = Y(t)·c`: `c = 1`, `Y = Re Z` if `k ≡ 0 mod 4`; `c = i`, `Y = Im Z` if
  `k ≡ 2 mod 4` (root number `i^k`, `HardyZerosGeneral.Zc_conj`).
* `Core.core_count_linear`.
-/
import RamanujanTau.HafnerGeneral.Core
import RamanujanTau.GeneralCuspMoments.Moments
import RamanujanTau.HardyZerosGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
open scoped Real MatrixGroups

variable {p : ℕ}

/-- **Real representation** `Z = Y·c`, `‖c‖ = 1`, for real coefficients. -/
theorem exists_rep (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    ∃ (Y : ℝ → ℝ) (c : ℂ), Rep f Y c := by
  have hk1 : 1 ≤ 2 * p + 2 := by omega
  have hIk : I ^ (2 * p + 2) = (-1) ^ (p + 1) := by
    rw [show 2 * p + 2 = 2 * (p + 1) by ring, pow_mul, I_sq]
  rcases Nat.even_or_odd (p + 1) with hj2 | hj2
  · have h1 : I ^ (2 * p + 2) = 1 := by rw [hIk, hj2.neg_one_pow]
    refine ⟨fun t => (Zc f t).re, 1, ⟨by simp, fun t => ?_⟩⟩
    have hc := Zc_conj f hk1 hreal t
    rw [h1, one_mul] at hc
    rw [mul_one]; exact (Complex.conj_eq_iff_re.mp hc).symm
  · have h1 : I ^ (2 * p + 2) = -1 := by rw [hIk, hj2.neg_one_pow]
    refine ⟨fun t => (Zc f t).im, I, ⟨by simp, fun t => ?_⟩⟩
    have hc := Zc_conj f hk1 hreal t
    rw [h1, neg_one_mul] at hc
    have hre : (Zc f t).re = 0 := by
      have := congrArg Complex.re hc
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    apply Complex.ext <;> simp [hre]

lemma fL_zero_of_Zc_zero {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) {t : ℝ} (h : Zc f t = 0) :
    fL f (sc k t) = 0 := by
  rw [Zc] at h
  rw [fL, h, mul_zero]

/-- Core count in the weight-`(2p+2)` normalisation. -/
theorem fL_critical_zeros_linear_aux (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ))
    (hk : 12 ≤ 2 * p + 2) (hf : f ≠ 0) (hreal : ∀ n, (coef f n).im = 0) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ Zc f t = 0) ∧ c * T ≤ S.card := by
  obtain ⟨Y, c, hRep⟩ := exists_rep f hreal
  obtain ⟨r, T₀, hr, hT₀1, hcore⟩ := core_count_linear f hk hf hRep
  refine ⟨1 / (24 * r), 3 * T₀, by positivity, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := hcore (T / 3) (by linarith)
  refine ⟨S, fun t ht => ?_, ?_⟩
  · obtain ⟨h0, h1, hz⟩ := hS t ht
    exact ⟨h0, by linarith, by rw [hRep.eq, hz, ofReal_zero, zero_mul]⟩
  · calc 1 / (24 * r) * T = T / 3 / (8 * r) := by field_simp; ring
      _ ≤ S.card := hcard

/-- **Hafner's theorem for `Λ(f,s)`**: `≫ T` distinct zeros `k/2 + it`, `0 < t ≤ T`, of the
completed L-function, for every nonzero level-one cusp form `f` with real coefficients. -/
theorem heckeLambda_critical_zeros_linear {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ heckeLambda f ((k : ℂ) / 2 + t * I) = 0) ∧ c * T ≤ S.card := by
  obtain ⟨p, rfl, hk⟩ := GeneralCuspMoments.exists_weight_eq f hf
  obtain ⟨c, T₀, hc, h⟩ := fL_critical_zeros_linear_aux f hk hf hreal
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h0, h1, hz⟩ := hS t ht
  refine ⟨h0, h1, ?_⟩
  rw [GeneralCuspMoments.crit_point]; exact hz

/-- **Hafner's theorem (1983) for level-one cusp forms**: if `f ∈ S_k(SL₂(ℤ))` is nonzero with
real Fourier coefficients, then `L(f,s)` (the entire continuation `fL f` of `∑ a_f(n) n^{−s}`)
has `≫ T` distinct zeros `k/2 + it` with `0 < t ≤ T`: `N₀(T) ≫ T`. -/
theorem fL_critical_zeros_linear {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ fL f ((k : ℂ) / 2 + t * I) = 0) ∧ c * T ≤ S.card := by
  obtain ⟨p, rfl, hk⟩ := GeneralCuspMoments.exists_weight_eq f hf
  obtain ⟨c, T₀, hc, h⟩ := fL_critical_zeros_linear_aux f hk hf hreal
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h0, h1, hz⟩ := hS t ht
  refine ⟨h0, h1, ?_⟩
  rw [GeneralCuspMoments.crit_point]; exact fL_zero_of_Zc_zero f hz

/-- **Sanity check `f = Δ`**: Hafner's `N₀(T) ≫ T` for `L(Δ,s)`, recovered from the general
theorem (stated for `HeckeConvexGeneral.fL Δ`). -/
theorem fL_discriminant_critical_zeros_linear :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧
        fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I) = 0) ∧
      c * T ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := fL_critical_zeros_linear (k := 12) _ discriminant_ne_zero'
    (fun n => by rw [coef_discriminant]; simp [RamanujanTau.tauC])
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h0, h1, hz⟩ := hS t ht
  have e : ((12 : ℕ) : ℂ) / 2 = 6 := by norm_num
  rw [e] at hz
  exact ⟨h0, h1, hz⟩

end RamanujanTau.HafnerGeneral

#print axioms RamanujanTau.HafnerGeneral.fL_critical_zeros_linear
#print axioms RamanujanTau.HafnerGeneral.heckeLambda_critical_zeros_linear
#print axioms RamanujanTau.HafnerGeneral.fL_discriminant_critical_zeros_linear
#print axioms RamanujanTau.HafnerGeneral.core_count_linear
#print axioms RamanujanTau.HafnerGeneral.mean_square_uniform
#print axioms RamanujanTau.HafnerGeneral.horizontal_mean
#print axioms RamanujanTau.HafnerGeneral.window_lower_gen
#print axioms RamanujanTau.HafnerGeneral.exists_normalized
#print axioms RamanujanTau.HafnerGeneral.mean_sq_Iw
#print axioms RamanujanTau.HafnerGeneral.Iw_lower
#print axioms RamanujanTau.HafnerGeneral.Phis_eq_strip
#print axioms RamanujanTau.HafnerGeneral.Fs_eq_fI
#print axioms RamanujanTau.HafnerGeneral.exists_rep
