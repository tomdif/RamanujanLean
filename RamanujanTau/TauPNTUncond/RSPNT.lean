/-
# Prime number theorem for the Rankin–Selberg / symmetric-square L-function, unconditional

* `rs_PNT`: `∑_{n<N} Λ_{Δ×Δ}(n) ~ N`, where `Λ_{Δ×Δ}(p^k) = A_k(p)² log p` (`vR`), the von Mangoldt
  function of `ζ(2s)R(s)`.  Wiener–Ikehara (`WienerIkehara.wienerIkehara`, proved) applied to
  `vR ≥ 0` with `G = −KK'/KK`, continuous on `Re s ≥ 1` by the edge non-vanishing (`Edge`).
* `rs_prime_PNT`: `∑_{p<N} λ(p)² log p ~ N` (the prime powers contribute `o(N)` by Weil, Kronecker).
* `theta_PNT`: `∑_{p<N} log p ~ N`.
* `sym2_prime_PNT`: `∑_{p<N} λ(p²) log p = o(N)` (`λ(p²) = λ(p)² − 1`), the PNT for `L(Sym²Δ, s)`.

No Deligne.
-/
import RamanujanTau.TauPNTUncond.Signs
import RamanujanTau.WienerIkehara.Main

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT
open ArithmeticFunction (vonMangoldt)

/-- Kronecker: `c ≥ 0`, `∑ c(n)/n < ∞` ⇒ `∑_{n<N} c(n) = o(N)`. -/
lemma cesaro_zero_of_summable_div {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0)
    (hs : Summable fun n => c n / n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, c n) / N) atTop (𝓝 0) := by
  have key : ∀ N : ℕ, (∑ n ∈ Finset.range N, c n) / N =
      ∑' n, (if n < N then c n / N else 0) := by
    intro N
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => if_neg (by simpa using hn)),
      Finset.sum_div]
    exact Finset.sum_congr rfl fun n hn => (if_pos (Finset.mem_range.mp hn)).symm
  simp_rw [key]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N n : ℕ) => if n < N then c n / N else 0) (g := fun _ => (0 : ℝ))
    (bound := fun n => c n / n) hs ?_ ?_
  · simpa using h
  · intro n
    refine (tendsto_const_div_atTop_nhds_zero_nat (c n)).congr' ?_
    filter_upwards [eventually_gt_atTop n] with N hN
    rw [if_pos hN]
  · refine Eventually.of_forall fun N n => ?_
    show ‖(if n < N then c n / (N : ℝ) else 0)‖ ≤ c n / n
    split_ifs with h
    · rw [Real.norm_of_nonneg (div_nonneg (hc n) (Nat.cast_nonneg _))]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hc0]
      · exact div_le_div_of_nonneg_left (hc n) (by exact_mod_cast Nat.pos_of_ne_zero hn)
          (by exact_mod_cast h.le)
    · rw [norm_zero]; exact div_nonneg (hc n) (Nat.cast_nonneg _)

lemma nonprime_zero_off (f : ℕ → ℝ) (hf : ∀ n, ¬ IsPrimePow n → f n = 0) {n : ℕ}
    (h : n ∉ Set.range ppow2) : (if n.Prime then 0 else f n) = 0 := by
  split_ifs with hp
  · rfl
  by_cases hpp : IsPrimePow n
  · exfalso
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
    · exact hp (by simpa using hp')
    · exact h ⟨(⟨p, hp'⟩, k - 2), by simp only [ppow2]; congr 1; omega⟩
  · exact hf n hpp

lemma summable_div_of_ppow2 {c : ℕ → ℝ} (hc : ∀ n, n ∉ Set.range ppow2 → c n = 0)
    {M : Nat.Primes × ℕ → ℝ} (hM : Summable M) (hb : ∀ q, |c (ppow2 q)| / (ppow2 q : ℝ) ≤ M q) :
    Summable fun n => c n / n := by
  have hs : Summable fun q => c (ppow2 q) / (ppow2 q : ℝ) := by
    refine Summable.of_norm_bounded hM fun q => ?_
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]; exact hb q
  exact (ppow2_injective.summable_iff (fun n hn => by simp [hc n hn])).mp hs

lemma log_le_40 {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 40 * x ^ (1 / 40 : ℝ) := by
  have := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 40)
  linarith [show x ^ (1 / 40 : ℝ) / (1 / 40) = 40 * x ^ (1 / 40 : ℝ) by ring]

lemma ppow2_cast (q : Nat.Primes × ℕ) : ((ppow2 q : ℕ) : ℝ) = ((q.1 : ℝ)) ^ (q.2 + 2) := by
  simp [ppow2]

/-- The prime powers `p^k`, `k ≥ 2`, of `vR`: `∑ vR(p^k)/p^k < ∞` (Rankin + Weil). -/
theorem summable_vR_nonprime :
    Summable fun n : ℕ => (if n.Prime then 0 else vR n) / n := by
  obtain ⟨C, hC1, hC⟩ := weil_AA
  set r0 : ℝ := (2 : ℝ) ^ (-(9 / 20 : ℝ))
  have hr0 : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  have hr01 : r0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine summable_div_of_ppow2 (fun n hn => nonprime_zero_off vR (fun n h => vR_of_not h) hn)
    (M := fun q => (if q.2 = 0 then 320 * C ^ 2 * (lam q.1 ^ 2 * (q.1 : ℝ) ^ (-(57 / 40 : ℝ))) +
        320 * (q.1 : ℝ) ^ (-(79 / 40 : ℝ)) else 0) +
      (160 * C ^ 2 / r0) * (q.1 : ℝ) ^ (-(53 / 40 : ℝ)) * r0 ^ q.2) ?_ ?_
  · refine Summable.add (summable_single_slot (fun p : Nat.Primes =>
      320 * C ^ 2 * (lam p ^ 2 * (p : ℝ) ^ (-(57 / 40 : ℝ))) + 320 * (p : ℝ) ^ (-(79 / 40 : ℝ)))
      (((summable_lam_sq (a := 57 / 40) (by norm_num)).mul_left _).add
        ((summable_primes_rpow (a := 79 / 40) (by norm_num)).mul_left _)) 0) ?_
    refine Summable.mul_of_nonneg
      (f := fun p : Nat.Primes => (160 * C ^ 2 / r0) * (p : ℝ) ^ (-(53 / 40 : ℝ)))
      (g := fun k : ℕ => r0 ^ k) ((summable_primes_rpow (a := 53 / 40) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one hr0.le hr01) ?_ ?_
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  rintro ⟨p, j⟩
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog := log_le_40 hp0.le
  have hnp : ¬ (ppow2 (p, j)).Prime := by
    simp only [ppow2]; exact Nat.Prime.not_prime_pow' (by omega)
  rw [if_neg hnp, ppow2_cast]
  simp only [ppow2]
  rw [show j + 2 = (j + 1) + 1 by ring, vR_pow hp, abs_of_nonneg (by positivity),
    div_eq_mul_inv, ← inv_pow]
  have hM3 : 0 ≤ (160 * C ^ 2 / r0) * (p : ℝ) ^ (-(53 / 40 : ℝ)) * r0 ^ j := by positivity
  have hT : rho p ^ 2 * (p : ℝ)⁻¹ ≤ r0 := by
    rw [rho_sq_div hp]; exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
  have hT0 : 0 ≤ rho p ^ 2 * (p : ℝ)⁻¹ := by have := rho_pos hp; positivity
  have hip : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  rcases j with _ | j
  · rw [if_pos rfl, show 0 + 1 + 1 = 2 by rfl, AA_two]
    have hl := hC hp 1
    rw [AA_one, pow_one] at hl
    have hl2 : lam p ^ 2 ≤ 4 * C ^ 2 * rho p ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hl 2
      rw [sq_abs] at this; nlinarith
    have e57 : rho p ^ 2 * (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2 = (p : ℝ) ^ (-(57 / 40 : ℝ)) := by
      rw [show rho p ^ 2 * (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2 =
        (rho p ^ 2 * (p : ℝ)⁻¹) * (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ by ring, rho_sq_div hp,
        ← Real.rpow_neg_one, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
      norm_num
    have e79 : (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2 = (p : ℝ) ^ (-(79 / 40 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
      norm_num
    have h4 : (lam p ^ 2 - 2) ^ 2 ≤ 2 * lam p ^ 2 * lam p ^ 2 + 8 := by
      nlinarith [sq_nonneg (lam p)]
    have hq : 0 ≤ (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2 := by positivity
    calc (lam p ^ 2 - 2) ^ 2 * Real.log p * (p : ℝ)⁻¹ ^ 2
        ≤ (2 * lam p ^ 2 * (4 * C ^ 2 * rho p ^ 2) + 8) * (40 * (p : ℝ) ^ (1 / 40 : ℝ)) *
            (p : ℝ)⁻¹ ^ 2 := by
          gcongr
          calc (lam p ^ 2 - 2) ^ 2 ≤ 2 * lam p ^ 2 * lam p ^ 2 + 8 := h4
            _ ≤ _ := by gcongr
      _ = 320 * C ^ 2 * (lam p ^ 2 * (rho p ^ 2 * (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2)) +
            320 * ((p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2) := by ring
      _ = 320 * C ^ 2 * (lam p ^ 2 * (p : ℝ) ^ (-(57 / 40 : ℝ))) +
            320 * (p : ℝ) ^ (-(79 / 40 : ℝ)) := by rw [e57, e79]
      _ ≤ _ := by linarith
  · rw [if_neg (by omega), zero_add]
    have hA := hC hp (j + 1 + 1 + 1)
    have hA2 : AA p (j + 1 + 1 + 1) ^ 2 ≤ 4 * C ^ 2 * (rho p ^ 2) ^ (j + 3) := by
      have := pow_le_pow_left₀ (abs_nonneg _) hA 2
      rw [sq_abs] at this
      calc AA p (j + 1 + 1 + 1) ^ 2 ≤ (2 * C * rho p ^ (j + 1 + 1 + 1)) ^ 2 := this
        _ = 4 * C ^ 2 * (rho p ^ 2) ^ (j + 3) := by ring
    set T := rho p ^ 2 * (p : ℝ)⁻¹
    have hT3 : (p : ℝ) ^ (1 / 40 : ℝ) * T ^ 3 = (p : ℝ) ^ (-(53 / 40 : ℝ)) := by
      simp only [T]
      rw [rho_sq_div hp, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
      norm_num
    have hTj : T ^ j ≤ r0 ^ j := pow_le_pow_left₀ hT0 hT j
    calc AA p (j + 1 + 1 + 1) ^ 2 * Real.log p * (p : ℝ)⁻¹ ^ (j + 1 + 1 + 1)
        ≤ 4 * C ^ 2 * (rho p ^ 2) ^ (j + 3) * (40 * (p : ℝ) ^ (1 / 40 : ℝ)) *
            (p : ℝ)⁻¹ ^ (j + 3) := by gcongr
      _ = 160 * C ^ 2 * ((p : ℝ) ^ (1 / 40 : ℝ) * T ^ 3) * T ^ j := by
          simp only [T]; rw [mul_pow, mul_pow]; ring
      _ ≤ 160 * C ^ 2 * ((p : ℝ) ^ (1 / 40 : ℝ) * T ^ 3) * r0 ^ j := by
          have : 0 ≤ (p : ℝ) ^ (1 / 40 : ℝ) * T ^ 3 := by positivity
          gcongr
      _ = (160 * C ^ 2 / r0) * (p : ℝ) ^ (-(53 / 40 : ℝ)) * r0 ^ (j + 1) := by
          rw [hT3, pow_succ]; field_simp; ring

/-- The prime powers `p^k`, `k ≥ 2`, of `Λ`: `∑ Λ(p^k)/p^k < ∞`. -/
theorem summable_vonMangoldt_nonprime :
    Summable fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n := by
  refine summable_div_of_ppow2 (fun n hn => nonprime_zero_off (fun n => vonMangoldt n)
      (fun n h => by simp [ArithmeticFunction.vonMangoldt_apply, h]) hn)
    (M := fun q => (40 * (q.1 : ℝ) ^ (-(79 / 40 : ℝ))) * (1 / 2 : ℝ) ^ q.2) ?_ ?_
  · exact Summable.mul_of_nonneg
      (f := fun p : Nat.Primes => 40 * (p : ℝ) ^ (-(79 / 40 : ℝ)))
      (g := fun k : ℕ => (1 / 2 : ℝ) ^ k) ((summable_primes_rpow (a := 79 / 40) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun p => by simp only [Pi.zero_apply]; positivity) (fun k => by simp only [Pi.zero_apply]; positivity)
  rintro ⟨p, j⟩
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hnp : ¬ (ppow2 (p, j)).Prime := by
    simp only [ppow2]; exact Nat.Prime.not_prime_pow' (by omega)
  rw [if_neg hnp, ppow2_cast]
  simp only [ppow2]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp, abs_of_nonneg hlog0, div_eq_mul_inv, ← inv_pow]
  have hip : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
  have e79 : (p : ℝ) ^ (1 / 40 : ℝ) * (p : ℝ)⁻¹ ^ 2 = (p : ℝ) ^ (-(79 / 40 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    norm_num
  calc Real.log p * (p : ℝ)⁻¹ ^ (j + 2) = Real.log p * (p : ℝ)⁻¹ ^ 2 * (p : ℝ)⁻¹ ^ j := by ring
    _ ≤ (40 * (p : ℝ) ^ (1 / 40 : ℝ)) * (p : ℝ)⁻¹ ^ 2 * (1 / 2) ^ j := by
        gcongr
        · exact log_le_40 hp0.le
    _ = 40 * (p : ℝ) ^ (-(79 / 40 : ℝ)) * (1 / 2) ^ j := by rw [← e79]; ring

/-- Splitting a sum over `n < N` into primes and non-primes. -/
lemma sum_prime_split (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Finset.range N with p.Prime, f p =
      ∑ n ∈ Finset.range N, f n - ∑ n ∈ Finset.range N, (if n.Prime then 0 else f n) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) Nat.Prime f, Finset.sum_ite,
    Finset.sum_const_zero, zero_add]
  ring

/-- **Rankin–Selberg PNT**: `∑_{n<N} Λ_{Δ×Δ}(n) ~ N` (unconditional). -/
theorem rs_PNT :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, vR n) / N) atTop (𝓝 1) :=
  RamanujanTau.WienerIkehara.wienerIkehara vR 1 negLogDerivK vR_nonneg
    (fun σ' hσ' => LSeriesSummable_vR (by simpa using hσ')) continuousOn_negLogDerivK
    (fun s hs => by simp only; rw [negLogDerivK_eq hs]; push_cast; ring)

lemma nonprime_littleO {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (hs : Summable fun n : ℕ => (if n.Prime then 0 else f n) / n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (if n.Prime then 0 else f n)) / N) atTop (𝓝 0) :=
  cesaro_zero_of_summable_div (fun n => by split_ifs; exacts [le_rfl, hf n])
    (by simp [Nat.not_prime_zero, hf0]) hs

/-- **`∑_{p<N} λ(p)² log p ~ N`** (unconditional). -/
theorem rs_prime_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, lam p ^ 2 * Real.log p) / N)
      atTop (𝓝 1) := by
  have h := rs_PNT.sub (nonprime_littleO vR_nonneg (vR_of_not (by simp [IsPrimePow]))
    summable_vR_nonprime)
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [← sub_div, ← sum_prime_split vR N]
  congr 1
  exact Finset.sum_congr rfl fun p hp => vR_prime (Finset.mem_filter.mp hp).2

/-- **`∑_{p<N} log p ~ N`** (Chebyshev `θ`, from the PNT). -/
theorem theta_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, Real.log p) / N) atTop (𝓝 1) := by
  have h := RamanujanTau.WienerIkehara.PNT_cumsum.sub (nonprime_littleO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) (by simp) summable_vonMangoldt_nonprime)
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [← sub_div, ← sum_prime_split (fun n => vonMangoldt n) N]
  congr 1
  exact Finset.sum_congr rfl fun p hp =>
    ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2

/-- **PNT for `L(Sym²Δ, s)`**: `∑_{p<N} λ(p²) log p = o(N)`, `λ(p²) = τ(p²)/p¹¹ = λ(p)² − 1`. -/
theorem sym2_prime_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, uu p 2 * Real.log p) / N)
      atTop (𝓝 0) := by
  have h := rs_prime_PNT.sub theta_PNT
  rw [sub_self] at h
  refine h.congr fun N => ?_
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).2
  have h2 := uu_rec hp' 0
  simp only [uu_zero, zero_add] at h2
  have h1 : uu p 1 = lam p := rfl
  rw [h2, h1]; ring

end RamanujanTau.TauPNTUncond
