/-
# The Rankin–Selberg asymptotic, conditional on horocycle equidistribution

`rankinSelberg_asymptotic_of_horocycle`: if the long closed horocycles equidistribute for the
single invariant function `G(z) = |Δ(z)|² (Im z)¹²`, i.e.

    ∫₀¹ G(x + iy) dx → L      (y → 0⁺)                               (HorocycleLimit L)

then `(1/N) ∑_{n ≤ N} τ(n)²/n¹¹ → (4π)¹² L / 11!`.

Chain: Parseval (`RankinSelberg.hasSum_tau_sq`) turns the hypothesis into
`t¹² ∑ τ(n)² e^{-nt} → (4π)¹² L`; Karamata (`Karamata.lean`, ρ = 12) gives
`∑_{n ≤ N} τ(n)² / N¹² → (4π)¹² L / 12!`; Abel summation with a Cesàro mean gives the
weighted form. With Zagier's value `L = (3/π)‖Δ‖²` this is `c = (3/π)(4π)¹²‖Δ‖²/11!`.

The hypothesis is the classical theorem (Zagier 1979, Sarnak 1981) and is *equivalent* to the
conclusion modulo the (easy) Abelian direction; all the depth sits in it.
-/
import RamanujanTau.EisensteinReal.Karamata
import RamanujanTau.RankinSelberg.Main

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal

open Real MeasureTheory Filter Topology Set Finset Complex
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I

/-! ### Abel summation with a Cesàro mean -/

lemma abel_identity (b : ℕ → ℝ) (k : ℕ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ k = (∑ n ∈ Icc 1 N, b n) / (N : ℝ) ^ k +
      ∑ n ∈ range N, (∑ m ∈ Icc 1 n, b m) * (1 / (n : ℝ) ^ k - 1 / ((n : ℝ) + 1) ^ k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ, sum_Icc_succ_top (by omega)]
    push_cast
    ring

/-- `n^{k+1}(n^{-k} - (n+1)^{-k}) → k`. -/
lemma tendsto_v (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (k + 1) * (1 / (n : ℝ) ^ k - 1 / ((n : ℝ) + 1) ^ k))
      atTop (𝓝 (k : ℝ)) := by
  have hlow : Tendsto (fun n : ℕ => (k : ℝ) * ((n : ℝ) / (n + 1)) ^ (k + 1)) atTop
      (𝓝 (k : ℝ)) := by
    have := ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow (k + 1)).const_mul (k : ℝ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < n + 1 := by linarith
    -- Bernoulli: `n^{k+1} + (k+1) n^k ≤ (n+1)^{k+1}`
    have hb := one_add_mul_le_pow (a := 1 / (n : ℝ)) (by
      have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith) (k + 1)
    have e : (1 + 1 / (n : ℝ)) = (n + 1) / n := by field_simp
    rw [e, div_pow] at hb
    rw [le_div_iff₀ (by positivity)] at hb
    have hnk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    have key : (k : ℝ) * (n : ℝ) ^ k ≤ ((n : ℝ) + 1) ^ k * (n + 1) - (n : ℝ) ^ k * (n + 1) := by
      have h1 : (1 + ((k + 1 : ℕ) : ℝ) * (1 / (n : ℝ))) * (n : ℝ) ^ (k + 1) =
          (n : ℝ) ^ (k + 1) + (k + 1) * (n : ℝ) ^ k := by
        push_cast; rw [pow_succ]; field_simp
      rw [h1] at hb
      have e1 : (n : ℝ) ^ (k + 1) = (n : ℝ) ^ k * n := pow_succ _ _
      have e2 : ((n : ℝ) + 1) ^ (k + 1) = ((n : ℝ) + 1) ^ k * ((n : ℝ) + 1) := pow_succ _ _
      rw [e1, e2] at hb
      linarith
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    have e2 : (n : ℝ) ^ (k + 1) * (1 / (n : ℝ) ^ k - 1 / ((n : ℝ) + 1) ^ k) * ((n : ℝ) + 1) ^ (k + 1)
        = (n : ℝ) * (((n : ℝ) + 1) ^ k * (n + 1) - (n : ℝ) ^ k * (n + 1)) := by
      field_simp; ring
    rw [e2, pow_succ]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := inv_pow_sub_inv_pow_le k hn1
    have hpos : (0 : ℝ) < (n : ℝ) ^ (k + 1) := by positivity
    calc (n : ℝ) ^ (k + 1) * (1 / (n : ℝ) ^ k - 1 / ((n : ℝ) + 1) ^ k)
        ≤ (n : ℝ) ^ (k + 1) * (k / (n : ℝ) ^ (k + 1)) := mul_le_mul_of_nonneg_left this hpos.le
      _ = k := by field_simp

/-- **Abel summation.** If `(∑_{n ≤ N} bₙ)/N^{k+1} → α` then `(∑_{n ≤ N} bₙ/nᵏ)/N → (k+1)α`. -/
theorem tendsto_sum_div_pow {b : ℕ → ℝ} (k : ℕ) {α : ℝ}
    (hA : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, b n) / (N : ℝ) ^ (k + 1)) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ k) / N) atTop
      (𝓝 (((k : ℝ) + 1) * α)) := by
  set A : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N, b n
  set u : ℕ → ℝ := fun n => A n * (1 / (n : ℝ) ^ k - 1 / ((n : ℝ) + 1) ^ k)
  have hu : Tendsto u atTop (𝓝 (α * k)) := by
    refine (hA.mul (tendsto_v k)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [u, A]
    field_simp
  have hc := hu.cesaro
  have := hA.add hc
  rw [show α + α * k = ((k : ℝ) + 1) * α by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abel_identity b k N]
  simp only [u, A]
  rw [pow_succ]
  field_simp

/-! ### The analytic input -/

/-- **Named hypothesis (horocycle equidistribution for `G`).** The mean of
`G(z) = |Δ(z)|²(Im z)¹²` over the closed horocycle `Im z = y` tends to `L` as `y → 0⁺`.
Classical (Zagier 1979, via `E(z,s)`; Sarnak 1981) with `L = (3/π)‖Δ‖²`. -/
def HorocycleLimit (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ y₀ > 0, ∀ (y : ℝ) (hy : 0 < y), y < y₀ →
    |(∫ x in (0 : ℝ)..1, G (hp hy x)) - L| < ε

/-- The Petersson norm `‖Δ‖² = ∫_{𝓕} |Δ|² y¹² dx dy / y²` over the standard fundamental domain
`|x| ≤ 1/2, x² + y² ≥ 1`. -/
noncomputable def petNormSq : ℝ :=
  ∫ p : ℝ × ℝ in {p : ℝ × ℝ | 0 < p.2 ∧ |p.1| ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2},
    G (UpperHalfPlane.ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) / p.2 ^ 2

lemma exp_pow_eq {t : ℝ} (n : ℕ) :
    Real.exp (-2 * π * (t / (4 * π))) ^ (2 * n) = Real.exp (-((n : ℝ) * t)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

lemma tau_sq_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => ((tau n : ℝ)) ^ 2 * Real.exp (-((n : ℝ) * t)))
      (∫ x in (0 : ℝ)..1, ‖Δf (hp (show 0 < t / (4 * π) by positivity) x)‖ ^ 2) := by
  have h := hasSum_tau_sq (show 0 < t / (4 * π) by positivity)
  simpa only [exp_pow_eq] using h

lemma integral_G {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, G (hp hy x) = y ^ 12 * ∫ x in (0 : ℝ)..1, ‖Δf (hp hy x)‖ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x
  unfold G; rw [hp_im]; ring

/-- Karamata's hypotheses for `aₙ = τ(n)²`, `ρ = 12`. -/
lemma karHyp_tau {L : ℝ} (hL : HorocycleLimit L) :
    KarHyp (fun n => ((tau n : ℝ)) ^ 2) 12 ((4 * π) ^ 12 * L) where
  nonneg n := sq_nonneg _
  summ t ht := (tau_sq_hasSum ht).summable
  lim := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have h4 : (0 : ℝ) < (4 * π) ^ 12 := by positivity
    obtain ⟨y₀, hy₀, hy⟩ := hL (ε / (4 * π) ^ 12) (by positivity)
    refine ⟨4 * π * y₀, by positivity, fun t ht hdist => ?_⟩
    have ht0 : (0 : ℝ) < t := ht
    have hyt : 0 < t / (4 * π) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdist
    have hlt : t / (4 * π) < y₀ := by rw [div_lt_iff₀ (by positivity)]; linarith
    have hb := hy (t / (4 * π)) hyt hlt
    rw [(tau_sq_hasSum ht0).tsum_eq, Real.dist_eq]
    rw [integral_G hyt] at hb
    have e : t ^ (12 : ℝ) = (4 * π) ^ 12 * (t / (4 * π)) ^ 12 := by
      rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [e, mul_assoc, ← mul_sub, abs_mul, abs_of_pos h4]
    calc (4 * π) ^ 12 * |(t / (4 * π)) ^ 12 *
          (∫ x in (0 : ℝ)..1, ‖Δf (hp hyt x)‖ ^ 2) - L|
        < (4 * π) ^ 12 * (ε / (4 * π) ^ 12) := mul_lt_mul_of_pos_left hb h4
      _ = ε := by field_simp

lemma sum_range_eq_Icc (N : ℕ) :
    ∑ n ∈ range (N + 1), ((tau n : ℝ)) ^ 2 = ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 := by
  induction N with
  | zero => simp [tau_zero]
  | succ N ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- **Mean square of `τ`, conditional on `HorocycleLimit L`:**
`∑_{n ≤ N} τ(n)² / N¹² → (4π)¹² L / 12!`. -/
theorem tendsto_sum_tau_sq_of_horocycle {L : ℝ} (hL : HorocycleLimit L) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2) / (N : ℝ) ^ 12) atTop
      (𝓝 ((4 * π) ^ 12 * L / (Nat.factorial 12 : ℝ))) := by
  have h := karamata (karHyp_tau hL) (by norm_num)
  have hΓ : Real.Gamma ((12 : ℝ) + 1) = (Nat.factorial 12 : ℝ) := by
    have := Real.Gamma_nat_eq_factorial 12
    push_cast at this
    exact this
  rw [hΓ] at h
  refine h.congr fun N => ?_
  rw [sum_range_eq_Icc, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **Rankin–Selberg asymptotic, conditional on `HorocycleLimit L`:**
`(1/N) ∑_{n ≤ N} τ(n)²/n¹¹ → (4π)¹² L / 11!`. -/
theorem rankinSelberg_asymptotic_of_horocycle {L : ℝ} (hL : HorocycleLimit L) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) / N) atTop
      (𝓝 ((4 * π) ^ 12 * L / (Nat.factorial 11 : ℝ))) := by
  have h := tendsto_sum_div_pow (b := fun n => ((tau n : ℝ)) ^ 2) 11
    (tendsto_sum_tau_sq_of_horocycle hL)
  convert h using 2
  rw [show (Nat.factorial 12 : ℝ) = 12 * (Nat.factorial 11 : ℝ) by
    rw [Nat.factorial_succ]; push_cast; ring]
  push_cast
  field_simp
  ring

/-- The constant is positive (from the unconditional two-sided bound). -/
theorem horocycleLimit_pos {L : ℝ} (hL : HorocycleLimit L) : 0 < L := by
  obtain ⟨c₁, c₂, hc₁, -, hb⟩ := rankinSelberg_two_sided
  have h := rankinSelberg_asymptotic_of_horocycle hL
  have hge : c₁ ≤ (4 * π) ^ 12 * L / (Nat.factorial 11 : ℝ) := by
    refine ge_of_tendsto h ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN0]
    exact (hb N hN).1
  have : 0 < (4 * π) ^ 12 * L / (Nat.factorial 11 : ℝ) := hc₁.trans_le hge
  have h4 : (0 : ℝ) < (4 * π) ^ 12 := by positivity
  have hf : (0 : ℝ) < (Nat.factorial 11 : ℝ) := by positivity
  by_contra hneg
  replace hneg := not_lt.1 hneg
  have : (4 * π) ^ 12 * L / (Nat.factorial 11 : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h4.le hneg) hf.le
  linarith

/-- **Rankin–Selberg with Zagier's constant**, conditional on horocycle equidistribution with
`L = (3/π)‖Δ‖²`: `(1/N) ∑_{n ≤ N} τ(n)²/n¹¹ → (3/π)(4π)¹²‖Δ‖²/11! = 0.384084…`. -/
theorem rankinSelberg_asymptotic_of_zagier (hZ : HorocycleLimit (3 / π * petNormSq)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) / N) atTop
      (𝓝 (3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ))) := by
  have h := rankinSelberg_asymptotic_of_horocycle hZ
  convert h using 2
  ring

end RamanujanTau.EisensteinReal

#print axioms RamanujanTau.EisensteinReal.karamata
#print axioms RamanujanTau.EisensteinReal.tendsto_sum_div_pow
#print axioms RamanujanTau.EisensteinReal.tendsto_sum_tau_sq_of_horocycle
#print axioms RamanujanTau.EisensteinReal.rankinSelberg_asymptotic_of_horocycle
#print axioms RamanujanTau.EisensteinReal.horocycleLimit_pos
#print axioms RamanujanTau.EisensteinReal.rankinSelberg_asymptotic_of_zagier
