/-
# Rankin–Selberg for an arbitrary level-one cusp form

For `f ∈ S_k(SL₂(ℤ))` with q-expansion coefficients `a(n)`, put `G_f(z) = |f(z)|² (Im z)^k`.
`G_f` is continuous, nonnegative, bounded (Mathlib's `CuspFormClass.petersson_bounded_left`) and
`SL₂(ℤ)`-invariant (`norm_petersson_smul`), so it is a `HoroFn` and the copied horocycle
argument (`GIdent.tendsto_Aint_zagier`) gives

    ∫₀¹ G_f(x+iy) dx → (3/π) ‖f‖²       (y → 0⁺)            (`horocycle_tendsto`)

with `‖f‖² = ∫_𝓕 |f|² y^k dx dy/y²`. Parseval on horocycles (`RankinSelberg.hasSum_normSq_coeff`),
Karamata with `ρ = k`, and Abel summation then give

    (1/N) ∑_{n≤N} |a(n)|²/n^{k−1} → (3/π)(4π)^k ‖f‖² / (k−1)!     (`rankinSelberg_asymptotic`).
-/
import RamanujanTau.RankinSelbergGeneral.GIdent

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergGeneral

open Finset Real Filter Topology MeasureTheory
open Complex ModularForm
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.EisensteinReal
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- `G_f(z) = |f(z)|² (Im z)^k`. -/
noncomputable def Gf (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℍ) : ℝ := ‖f z‖ ^ 2 * z.im ^ k

/-- The squared coefficient `|a(n)|²`. -/
noncomputable def coeffSq (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : ℝ := ‖(qExpansion 1 f).coeff n‖ ^ 2

/-- The Petersson norm `‖f‖² = ∫_𝓕 |f|² y^k dx dy / y²` over `|x| ≤ 1/2, x² + y² ≥ 1`. -/
noncomputable def petNormSqF (f : CuspForm 𝒮ℒ (k : ℤ)) : ℝ :=
  ∫ p : ℝ × ℝ in {p : ℝ × ℝ | 0 < p.2 ∧ |p.1| ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2},
    Gf f (UpperHalfPlane.ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) / p.2 ^ 2

lemma Gf_eq_norm_petersson (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℍ) :
    Gf f z = ‖petersson k f f z‖ := by
  simp only [Gf, petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  simp only [zpow_natCast]; ring

lemma Gf_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (g : SL(2, ℤ)) (z : ℍ) : Gf f (g • z) = Gf f z := by
  rw [Gf_eq_norm_petersson, Gf_eq_norm_petersson]
  exact SlashInvariantFormClass.norm_petersson_smul (Γ := 𝒮ℒ) (f := f) (f' := f) ⟨g, rfl⟩

lemma continuous_Gf (f : CuspForm 𝒮ℒ (k : ℤ)) : Continuous (Gf f) := by
  unfold Gf
  exact ((ModularFormClass.holo f).continuous.norm.pow 2).mul
    (UpperHalfPlane.continuous_im.pow k)

lemma Gf_nonneg (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℍ) : 0 ≤ Gf f z := by
  unfold Gf; have := z.im_pos; positivity

lemma exists_Gf_le (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, Gf f z ≤ M := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) 𝒮ℒ f f
  exact ⟨max C 0, le_max_right _ _, fun z => by
    rw [Gf_eq_norm_petersson]; exact (hC z).trans (le_max_left _ _)⟩

/-- `G_f` as an abstract bounded continuous invariant function. -/
@[reducible] noncomputable def horoFn (f : CuspForm 𝒮ℒ (k : ℤ)) : HoroFn where
  G := Gf f
  continuous_G := continuous_Gf f
  G_nonneg := Gf_nonneg f
  exists_G_le := exists_Gf_le f
  G_smul := Gf_smul f

/-- The horocycle mean `∫₀¹ G_f(x+iy) dx` (junk `0` for `y ≤ 0`). -/
noncomputable def horoMean (f : CuspForm 𝒮ℒ (k : ℤ)) (y : ℝ) : ℝ :=
  if hy : 0 < y then ∫ x in (0 : ℝ)..1, Gf f (hp hy x) else 0

/-- **Horocycle equidistribution for `G_f = |f|²y^k` (Zagier's theorem for `G_f`).** -/
theorem horocycle_tendsto (f : CuspForm 𝒮ℒ (k : ℤ)) :
    Tendsto (horoMean f) (𝓝[>] 0) (𝓝 (3 / π * petNormSqF f)) :=
  @Horo.tendsto_Aint_zagier (horoFn f)

/-! ### Parseval, Karamata, Abel -/

lemma coeff_zero_eq_zero (f : CuspForm 𝒮ℒ (k : ℤ)) : (qExpansion 1 f).coeff 0 = 0 := by
  rw [qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
  exact (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero

lemma coeffSq_hasSum (f : CuspForm 𝒮ℒ (k : ℤ)) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => coeffSq f n * Real.exp (-((n : ℝ) * t)))
      (∫ x in (0 : ℝ)..1, ‖f (hp (show 0 < t / (4 * π) by positivity) x)‖ ^ 2) := by
  have h := hasSum_normSq_coeff (k := (k : ℤ)) f (show 0 < t / (4 * π) by positivity)
  simpa only [exp_pow_eq] using h

lemma horoMean_eq (f : CuspForm 𝒮ℒ (k : ℤ)) {y : ℝ} (hy : 0 < y) :
    horoMean f y = y ^ k * ∫ x in (0 : ℝ)..1, ‖f (hp hy x)‖ ^ 2 := by
  rw [horoMean, dif_pos hy, ← intervalIntegral.integral_const_mul]
  congr 1; funext x
  unfold Gf; rw [hp_im]; ring

/-- Karamata's hypotheses for `aₙ = |a(n)|²`, `ρ = k`. -/
lemma karHyp_coeffSq (f : CuspForm 𝒮ℒ (k : ℤ)) :
    KarHyp (coeffSq f) k ((4 * π) ^ k * (3 / π * petNormSqF f)) where
  nonneg n := sq_nonneg _
  summ t ht := (coeffSq_hasSum f ht).summable
  lim := by
    have hmap : Tendsto (fun t : ℝ => t / (4 * π)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((continuous_id.div_const (4 * π)).tendsto (0 : ℝ))
        exact (by simpa using this : Tendsto (fun x : ℝ => x / (4 * π)) (𝓝 0) (𝓝 0)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Set.mem_Ioi.2 (div_pos (show (0 : ℝ) < t from ht) (by positivity))
    have h := ((horocycle_tendsto f).comp hmap).const_mul ((4 * π) ^ k)
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hyt : 0 < t / (4 * π) := by positivity
    simp only [Function.comp]
    rw [horoMean_eq f hyt, (coeffSq_hasSum f ht0).tsum_eq, Real.rpow_natCast]
    rw [div_pow, ← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]

lemma sum_range_eq_Icc (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) :
    ∑ n ∈ range (N + 1), coeffSq f n = ∑ n ∈ Icc 1 N, coeffSq f n := by
  induction N with
  | zero => simp [coeffSq, coeff_zero_eq_zero]
  | succ N ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- **Mean square of the coefficients:**
`∑_{n ≤ N} |a(n)|² / N^k → (3/π)(4π)^k ‖f‖² / k!`. -/
theorem tendsto_sum_coeffSq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, coeffSq f n) / (N : ℝ) ^ k) atTop
      (𝓝 (3 / π * (4 * π) ^ k * petNormSqF f / (Nat.factorial k : ℝ))) := by
  have h := karamata (karHyp_coeffSq f) (by exact_mod_cast hk)
  have hΓ : Real.Gamma ((k : ℝ) + 1) = (Nat.factorial k : ℝ) := by
    have := Real.Gamma_nat_eq_factorial k
    push_cast at this
    exact this
  rw [hΓ] at h
  convert h using 1
  · funext N
    rw [sum_range_eq_Icc, Real.rpow_natCast]
  · congr 1; ring

/-- **Rankin–Selberg asymptotic for every level-one cusp form `f` of weight `k ≥ 1`:**
`(1/N) ∑_{n ≤ N} |a(n)|²/n^{k−1} → (3/π)(4π)^k ‖f‖² / (k−1)!`. -/
theorem rankinSelberg_asymptotic (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1)) / N) atTop
      (𝓝 (3 / π * (4 * π) ^ k * petNormSqF f / (Nat.factorial (k - 1) : ℝ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := tendsto_sum_div_pow (b := coeffSq f) j (tendsto_sum_coeffSq f hk)
  simp only [Nat.add_sub_cancel]
  convert h using 2
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The same with `Γ(k)`: `(1/N) ∑_{n ≤ N} |a(n)|²/n^{k−1} → (3/π)(4π)^k ‖f‖² / Γ(k)`. -/
theorem rankinSelberg_asymptotic_Gamma (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1)) / N) atTop
      (𝓝 (3 / π * (4 * π) ^ k * petNormSqF f / Real.Gamma k)) := by
  have hΓ : Real.Gamma (k : ℝ) = (Nat.factorial (k - 1) : ℝ) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := Real.Gamma_nat_eq_factorial j
    push_cast at this ⊢
    simpa using this
  rw [hΓ]
  exact rankinSelberg_asymptotic f hk

end RamanujanTau.RankinSelbergGeneral

#print axioms RamanujanTau.RankinSelbergGeneral.horocycle_tendsto
#print axioms RamanujanTau.RankinSelbergGeneral.tendsto_sum_coeffSq
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_asymptotic_Gamma
