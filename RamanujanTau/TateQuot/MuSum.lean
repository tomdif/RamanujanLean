/-
# Sums over the nonzero points of `μ_p ⊂ Tate(q)`

`S_m = Σ_{k=1}^{p−1} θ^m x(ζ^k)` for `m = 0, 2, 4` in terms of `σ`-series:
`S_m = κ_m + 2 p^{m+2} σ_{m+1}(q^p) − c_m σ_{m+1}(q)` with `c₀ = 2p`, `c₂ = c₄ = 2`.
-/
import RamanujanTau.TateQuot.MuSeries

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset
open scoped ArithmeticFunction.sigma

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}

/-- `σ_j(q) = Σ σ_j(n) qⁿ` over `K`. -/
def sigK (K : Type*) [Field K] (j : ℕ) : PowerSeries K :=
  PowerSeries.map (Int.castRingHom K) (TateCurve.s j)

omit [CharZero K] in
lemma coeff_sigK (j N : ℕ) : coeff N (sigK K j) = (σ j N : K) := by
  simp [sigK, TateCurve.coeff_s]

omit [CharZero K] in
lemma sigma_cast (j N : ℕ) : (σ j N : K) = ∑ d ∈ N.divisors, (d : K) ^ j := by
  rw [ArithmeticFunction.sigma_apply]; push_cast; rfl

omit [CharZero K] in
/-- `Σ_{d ∣ N, p ∣ d} d^j = [p ∣ N] p^j σ_j(N/p)`. -/
lemma divsum_dvd (j N : ℕ) :
    ∑ d ∈ N.divisors, (if p ∣ d then (d : K) ^ j else 0) =
      if p ∣ N then (p : K) ^ j * (σ j (N / p) : K) else 0 := by
  split_ifs with hN
  · obtain ⟨M, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left _ hp.out.pos, sigma_cast, mul_sum, ← sum_filter]
    have hset : (p * M).divisors.filter (p ∣ ·) = M.divisors.image (p * ·) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, e, rfl⟩
        exact ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hp.out.pos).mp h1, by rintro rfl; simp at h2⟩, rfl⟩
      · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨mul_dvd_mul_left p h1, mul_ne_zero hp.out.ne_zero h2⟩, dvd_mul_right _ _⟩
    rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.out.pos h)]
    refine sum_congr rfl fun e _ => ?_
    push_cast; ring
  · refine sum_eq_zero fun d hd => ?_
    rw [if_neg]
    intro hpd
    exact hN (hpd.trans (Nat.dvd_of_mem_divisors hd))

omit [CharZero K] in
lemma mk_divsum (j : ℕ) (α β : K) :
    mk (fun N => ∑ d ∈ N.divisors, (d : K) ^ j * ((if p ∣ d then α else 0) + β)) =
      C (α * (p : K) ^ j) * expand p hp.out.ne_zero (sigK K j) + C β * sigK K j := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_mk, map_add, coeff_C_mul, coeff_C_mul, coeff_expand, coeff_sigK, sigma_cast]
  have h := divsum_dvd (K := K) (p := p) j N
  have e : ∑ d ∈ N.divisors, (d : K) ^ j * ((if p ∣ d then α else 0) + β) =
      α * ∑ d ∈ N.divisors, (if p ∣ d then (d : K) ^ j else 0) + β * ∑ d ∈ N.divisors, (d : K) ^ j := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  rw [e, h]
  split_ifs with h1
  · simp only [coeff_sigK, sigma_cast]; ring
  · simp only [coeff_sigK, sigma_cast]; ring

lemma sum_Ico_inv_pow (hζ : IsPrimitiveRoot ζ p) (d : ℕ) :
    ∑ k ∈ Ico 1 p, (ζ ^ k)⁻¹ ^ d = (if p ∣ d then (p : K) else 0) - 1 := by
  rw [← sum_Ico_pow_prim hζ.inv d]
  refine sum_congr rfl fun k _ => ?_
  rw [inv_pow, inv_pow, inv_pow]

lemma sum_txc (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : Even m) (N : ℕ) :
    ∑ k ∈ Ico 1 p, txc m (ζ ^ k) N = ∑ d ∈ N.divisors, (d : K) ^ (m + 1) *
      ((if p ∣ d then 2 * (p : K) else 0) + (-2 - ((p : K) - 1) * if m = 0 then 2 else 0)) := by
  simp only [txc]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum, sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_Ico_pow_prim hζ,
    sum_Ico_inv_pow hζ, hm.neg_one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub hp.out.one_le]
  congr 1
  split_ifs <;> push_cast <;> ring

variable (K) in
/-- `S_m = Σ_{k=1}^{p−1} θ^m x(ζ^k)`. -/
def Ssum (ζ : K) (p m : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tx m (ζ ^ k)

omit [CharZero K] in
lemma zeta_pow_ne_zero (hζ : IsPrimitiveRoot ζ p) (k : ℕ) : ζ ^ k ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero hp.out.ne_zero)

lemma Ssum_eq (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : Even m) :
    Ssum K ζ p m = C (∑ k ∈ Ico 1 p, cK m (ζ ^ k)) +
      (C (2 * (p : K) * (p : K) ^ (m + 1)) * expand p hp.out.ne_zero (sigK K (m + 1)) +
        C (-2 - ((p : K) - 1) * if m = 0 then 2 else 0) * sigK K (m + 1)) := by
  rw [Ssum, sum_congr rfl fun k hk => tx_eq (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk) m,
    sum_add_distrib, ← map_sum, ← mk_divsum]
  congr 1
  refine PowerSeries.ext fun N => ?_
  rw [map_sum, coeff_mk]
  simp only [coeff_mk]
  exact sum_txc hζ hm N

theorem S0_eq (hζ : IsPrimitiveRoot ζ p) :
    Ssum K ζ p 0 = C (-((p : K) ^ 2 - 1) / 12) +
      (C (2 * (p : K) ^ 2) * expand p hp.out.ne_zero (sigK K 1) + C (-2 * (p : K)) * sigK K 1) := by
  rw [Ssum_eq hζ (by decide), kappa0 hζ]
  simp only [↓reduceIte]; ring_nf

theorem S2_eq (hζ : IsPrimitiveRoot ζ p) :
    Ssum K ζ p 2 = C (((p : K) ^ 4 - 1) / 120) +
      (C (2 * (p : K) ^ 4) * expand p hp.out.ne_zero (sigK K 3) + C (-2) * sigK K 3) := by
  rw [Ssum_eq hζ (by decide), kappa2 hζ]
  simp only [OfNat.ofNat_ne_zero, if_false]; ring_nf

theorem S4_eq (hζ : IsPrimitiveRoot ζ p) :
    Ssum K ζ p 4 = C (-((p : K) ^ 6 - 1) / 252) +
      (C (2 * (p : K) ^ 6) * expand p hp.out.ne_zero (sigK K 5) + C (-2) * sigK K 5) := by
  rw [Ssum_eq hζ (by decide), kappa4 hζ]
  simp only [OfNat.ofNat_ne_zero, if_false]; ring_nf

end TateQuot
