/-
# Rankin–Selberg, first milestone: `∑_{n ≤ N} τ(n)²/n¹¹ ≍ N`

Headline (`rankinSelberg_two_sided`): there are `0 < c₁ ≤ c₂` with

  `c₁ N ≤ ∑_{n=1}^{N} τ(n)² / n¹¹ ≤ c₂ N`   for every `N ≥ 1`,

i.e. the Rankin–Selberg mean square has the true order of magnitude (`rankinSelberg_isTheta`).
No Eisenstein series, no Tauberian theorem.

* Upper bound: Hecke–Parseval (`Upper.lean`).
* Lower bound: the Farey/horocycle bound `∫₀¹ |Δ(x+i/C²)|² dx ≥ (m/32) C²⁴` (`Lower.lean`), and the
  tail of `∑ τ(n)² e^{-4πn/C²}` beyond `n > λC²` is at most `e^{-2πλ}` times the same sum at
  height `y/2`, which is `O(C²⁴)` by the upper bound. So `∑_{n ≤ λC²} τ(n)² ≫ C²⁴`.
-/
import RamanujanTau.RankinSelberg.Lower

set_option autoImplicit false

namespace RamanujanTau.RankinSelberg

open Complex ModularForm MeasureTheory Finset Filter Asymptotics
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

/-- **Truncation**: `∑_{n ≤ L} τ(n)² ≥ (m/32) C²⁴ − e^{-2πL/C²} · K 2¹² C²⁴`. -/
theorem exists_sum_tau_sq_ge_trunc : ∃ m K : ℝ, 0 < m ∧ 0 ≤ K ∧ ∀ C L : ℕ, 1 ≤ C →
    m / 32 * (C : ℝ) ^ 24 - Real.exp (-2 * π * (1 / (C : ℝ) ^ 2)) ^ L * (K * 2 ^ 12 * (C : ℝ) ^ 24)
      ≤ ∑ n ∈ Icc 1 L, ((tau n : ℝ)) ^ 2 := by
  obtain ⟨m, hm0, hm⟩ := integral_lower
  obtain ⟨K, hK0, hK⟩ := exists_integral_le
  refine ⟨m, K, hm0, hK0, fun C L hC => ?_⟩
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  set y : ℝ := 1 / (C : ℝ) ^ 2 with hydef
  have hy : 0 < y := by positivity
  have hy2 : 0 < y / 2 := by positivity
  set b : ℕ → ℝ := fun n => ((tau n : ℝ)) ^ 2
  set r := Real.exp (-2 * π * y)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Real.pi_pos; nlinarith)
  have hS := hasSum_tau_sq hy
  have hS2 := hasSum_tau_sq hy2
  have hr2 : ∀ n : ℕ, Real.exp (-2 * π * (y / 2)) ^ (2 * n) = r ^ n := by
    intro n
    rw [pow_mul, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  simp_rw [hr2] at hS2
  have hI1 := hm C hC hy
  have hI2 : ∫ x in (0 : ℝ)..1, ‖Δf (hp hy2 x)‖ ^ 2 ≤ K * 2 ^ 12 * (C : ℝ) ^ 24 := by
    refine (hK hy2).trans (le_of_eq ?_)
    rw [hydef]; field_simp
  -- termwise comparison
  have hb0 : ∀ n, 0 ≤ b n := fun n => sq_nonneg _
  have hterm : ∀ n : ℕ, b n * r ^ (2 * n) ≤
      (if n ∈ Icc 1 L then b n else 0) + r ^ L * (b n * r ^ n) := by
    intro n
    have hpos : 0 ≤ r ^ L * (b n * r ^ n) := by have := hb0 n; positivity
    split_ifs with hn
    · have : b n * r ^ (2 * n) ≤ b n := by
        have := pow_le_one₀ hr0 hr1 (n := 2 * n)
        nlinarith [hb0 n]
      linarith
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [b, tau_zero]
      · have hLn : L ≤ n := by
          by_contra h; exact hn (mem_Icc.mpr ⟨hn0, by omega⟩)
        have : r ^ n ≤ r ^ L := pow_le_pow_of_le_one hr0 hr1 hLn
        have e : b n * r ^ (2 * n) = b n * r ^ n * r ^ n := by rw [two_mul, pow_add]; ring
        rw [e, zero_add]
        have : b n * r ^ n * r ^ n ≤ b n * r ^ n * r ^ L :=
          mul_le_mul_of_nonneg_left this (by have := hb0 n; positivity)
        linarith
  have hfin : HasSum (fun n : ℕ => if n ∈ Icc 1 L then b n else 0) (∑ n ∈ Icc 1 L, b n) := by
    have h : HasSum (fun n : ℕ => if n ∈ Icc 1 L then b n else 0)
        (∑ n ∈ Icc 1 L, if n ∈ Icc 1 L then b n else 0) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    rwa [sum_congr rfl (fun _ hn => if_pos hn)] at h
  have hle := hasSum_le hterm hS (hfin.add (hS2.mul_left (r ^ L)))
  have h3 := mul_le_mul_of_nonneg_left hI2 (pow_nonneg hr0 L)
  linarith

lemma sum_tau_sq_mono {M N : ℕ} (h : M ≤ N) :
    ∑ n ∈ Icc 1 M, ((tau n : ℝ)) ^ 2 ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h) (fun _ _ _ => sq_nonneg _)

lemma one_le_sum_tau_sq {N : ℕ} (hN : 1 ≤ N) : 1 ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 := by
  have h := sum_tau_sq_mono (M := 1) hN
  simpa [tau_one] using h

/-- **Lower bound**: `∑_{n ≤ N} τ(n)² ≥ k N¹²`. -/
theorem exists_sum_tau_sq_ge : ∃ k : ℝ, 0 < k ∧ ∀ N : ℕ, 1 ≤ N →
    k * (N : ℝ) ^ 12 ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 := by
  obtain ⟨m, K, hm0, hK0, htr⟩ := exists_sum_tau_sq_ge_trunc
  set lam : ℕ := ⌈64 * 2 ^ 12 * K / m⌉₊ + 1 with hlam
  have hlam1 : 1 ≤ lam := by omega
  have hlamr : (1 : ℝ) ≤ lam := by exact_mod_cast hlam1
  -- `∑_{n ≤ λC²} τ(n)² ≥ (m/64) C²⁴`
  have hmain : ∀ C : ℕ, 1 ≤ C → m / 64 * (C : ℝ) ^ 24 ≤ ∑ n ∈ Icc 1 (lam * C ^ 2), ((tau n : ℝ)) ^ 2 := by
    intro C hC
    have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
    have h := htr C (lam * C ^ 2) hC
    have hexp : Real.exp (-2 * π * (1 / (C : ℝ) ^ 2)) ^ (lam * C ^ 2) = Real.exp (-(2 * π * lam)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    rw [hexp] at h
    have he1 : Real.exp (-(2 * π * lam)) ≤ 1 / (1 + lam) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have := Real.add_one_le_exp (2 * π * lam)
      have : (lam : ℝ) ≤ 2 * π * lam := by nlinarith [Real.pi_gt_three]
      linarith
    have hceil : 64 * 2 ^ 12 * K / m ≤ (1 + lam : ℝ) := by
      have := Nat.le_ceil (64 * 2 ^ 12 * K / m)
      rw [hlam]; push_cast; linarith
    have he2 : Real.exp (-(2 * π * lam)) * (K * 2 ^ 12) ≤ m / 64 := by
      calc Real.exp (-(2 * π * lam)) * (K * 2 ^ 12) ≤ 1 / (1 + lam) * (K * 2 ^ 12) := by gcongr
        _ ≤ m / 64 := by
          rw [div_le_iff₀ hm0] at hceil
          rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
          nlinarith
    have hC24 : (0 : ℝ) ≤ (C : ℝ) ^ 24 := by positivity
    have : Real.exp (-(2 * π * lam)) * (K * 2 ^ 12 * (C : ℝ) ^ 24) ≤ m / 64 * (C : ℝ) ^ 24 := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right he2 hC24
    linarith
  refine ⟨min (1 / (lam : ℝ) ^ 12) (m / 64 / (4 * lam : ℝ) ^ 12), by positivity, fun N hN => ?_⟩
  rcases lt_or_ge N lam with hNl | hNl
  · -- small `N`: the term `τ(1)² = 1`
    have hNr : (N : ℝ) ≤ lam := by exact_mod_cast hNl.le
    calc min (1 / (lam : ℝ) ^ 12) (m / 64 / (4 * lam : ℝ) ^ 12) * (N : ℝ) ^ 12
        ≤ 1 / (lam : ℝ) ^ 12 * (N : ℝ) ^ 12 := by gcongr; exact min_le_left _ _
      _ ≤ 1 / (lam : ℝ) ^ 12 * (lam : ℝ) ^ 12 := by gcongr
      _ = 1 := by field_simp
      _ ≤ _ := one_le_sum_tau_sq hN
  · -- large `N`: `C = ⌊√(N/λ)⌋`
    set q := N / lam
    have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    set C := Nat.sqrt q
    have hC1 : 1 ≤ C := Nat.le_sqrt.mpr (by omega)
    have hCq : C ^ 2 ≤ q := by rw [sq]; exact Nat.sqrt_le q
    have hqC : q < (C + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt q
    have hle : lam * C ^ 2 ≤ N :=
      (Nat.mul_le_mul_left _ hCq).trans (by rw [mul_comm]; exact Nat.div_mul_le_self N lam)
    have hNlt : N < lam * (4 * C ^ 2) := by
      have h1 : N < lam * (q + 1) := Nat.lt_mul_div_succ N (by omega : 0 < lam)
      have h2 : q + 1 ≤ 4 * C ^ 2 := by nlinarith
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ h2)
    have hNr : (N : ℝ) ≤ 4 * lam * (C : ℝ) ^ 2 := by
      have : (N : ℝ) < ((lam * (4 * C ^ 2) : ℕ) : ℝ) := by exact_mod_cast hNlt
      push_cast at this; linarith
    have hN12 : (N : ℝ) ^ 12 ≤ (4 * lam : ℝ) ^ 12 * (C : ℝ) ^ 24 := by
      calc (N : ℝ) ^ 12 ≤ (4 * lam * (C : ℝ) ^ 2) ^ 12 := by gcongr
        _ = (4 * lam : ℝ) ^ 12 * (C : ℝ) ^ 24 := by ring
    calc min (1 / (lam : ℝ) ^ 12) (m / 64 / (4 * lam : ℝ) ^ 12) * (N : ℝ) ^ 12
        ≤ m / 64 / (4 * lam : ℝ) ^ 12 * (N : ℝ) ^ 12 := by gcongr; exact min_le_right _ _
      _ ≤ m / 64 / (4 * lam : ℝ) ^ 12 * ((4 * lam : ℝ) ^ 12 * (C : ℝ) ^ 24) := by gcongr
      _ = m / 64 * (C : ℝ) ^ 24 := by field_simp
      _ ≤ ∑ n ∈ Icc 1 (lam * C ^ 2), ((tau n : ℝ)) ^ 2 := hmain C hC1
      _ ≤ _ := sum_tau_sq_mono hle

/-- **Rankin–Selberg, order of magnitude** (Rankin 1939 / Selberg 1940, weak form):
there are constants `0 < c₁, c₂` with `c₁ N ≤ ∑_{n=1}^{N} τ(n)²/n¹¹ ≤ c₂ N` for all `N ≥ 1`. -/
theorem rankinSelberg_two_sided : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 1 ≤ N →
    c₁ * N ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ∧
      ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ c₂ * N := by
  obtain ⟨k, hk0, hk⟩ := exists_sum_tau_sq_ge
  obtain ⟨K, hK0, hK⟩ := exists_sum_tau_sq_div_le
  refine ⟨k, K + 1, hk0, by positivity, fun N hN => ⟨?_, ?_⟩⟩
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2) / (N : ℝ) ^ 11 ≤
        ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 := by
      rw [sum_div]
      refine sum_le_sum fun n hn => ?_
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      gcongr
    have h2 : k * N ≤ (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2) / (N : ℝ) ^ 11 := by
      rw [le_div_iff₀ (by positivity)]
      calc k * N * (N : ℝ) ^ 11 = k * (N : ℝ) ^ 12 := by ring
        _ ≤ _ := hk N hN
    linarith
  · have := hK N
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith

/-- **Rankin–Selberg, order of magnitude**, asymptotic form:
`∑_{n ≤ N} τ(n)²/n¹¹ = Θ(N)`. -/
theorem rankinSelberg_isTheta :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) =Θ[atTop] fun N => (N : ℝ) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := rankinSelberg_two_sided
  have hnn : ∀ N : ℕ, 0 ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 :=
    fun N => sum_nonneg fun n _ => by positivity
  refine ⟨IsBigO.of_bound c₂ ?_, IsBigO.of_bound (1 / c₁) ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_of_nonneg (hnn N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
    exact (h N hN).2
  · filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_of_nonneg (hnn N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc₁, mul_comm]
    exact (h N hN).1

end RamanujanTau.RankinSelberg

#print axioms RamanujanTau.RankinSelberg.hasSum_normSq_coeff
#print axioms RamanujanTau.RankinSelberg.hasSum_tau_sq
#print axioms RamanujanTau.RankinSelberg.exists_sum_tau_sq_le
#print axioms RamanujanTau.RankinSelberg.exists_sum_tau_sq_div_le
#print axioms RamanujanTau.RankinSelberg.exists_band_lower
#print axioms RamanujanTau.RankinSelberg.card_fareyPairs_ge
#print axioms RamanujanTau.RankinSelberg.integral_lower
#print axioms RamanujanTau.RankinSelberg.exists_sum_tau_sq_ge
#print axioms RamanujanTau.RankinSelberg.rankinSelberg_two_sided
#print axioms RamanujanTau.RankinSelberg.rankinSelberg_isTheta
