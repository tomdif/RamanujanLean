/-
# From `DeligneBound` (primes) to `|τ(n)| ≤ C_δ n^{11/2+δ}` (all `n`)

The repo's `DeligneBound` only states `τ(p)² ≤ 4p^{11}` at primes. Here:

* `cheb_bound`: a real sequence with `a₀ = 1`, `a₁ = t`, `a_{k+2} = t a_{k+1} − a_k`, `t² ≤ 4`,
  satisfies `|a_k| ≤ k + 1` (Chebyshev `U_k`: `a_k = Σ_{j≤k} z^j w^{k−j}` with `z, w = e^{±iθ}`);
* `abs_tau_prime_pow_le` (`[DeligneBound]`): `|τ(p^k)| ≤ (k+1) p^{11k/2}` (Hecke recurrence);
* `abs_tau_le_divisors` (`[DeligneBound]`): `|τ(n)| ≤ d(n) n^{11/2}` (Mordell multiplicativity);
* `card_divisors_le_rpow'`: `d(n) ≤ C_δ n^δ` (unconditional);
* `abs_tau_le_rpow` (`[DeligneBound]`): `|τ(n)| ≤ C_δ n^{11/2+δ}`.
-/
import RamanujanTau.Deligne
import RamanujanTau.HeckeQExp

set_option autoImplicit false

namespace RamanujanTau.VoronoiPointwise

open Finset

/-! ### Chebyshev -/

/-- `s_k(z,w) = Σ_{j≤k} z^j w^{k−j}`. -/
def csum {R : Type*} [CommRing R] (z w : R) (k : ℕ) : R :=
  ∑ j ∈ range (k + 1), z ^ j * w ^ (k - j)

lemma csum_succ {R : Type*} [CommRing R] (z w : R) (k : ℕ) :
    csum z w (k + 1) = z * csum z w k + w ^ (k + 1) := by
  unfold csum
  rw [sum_range_succ', mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have : k + 1 - (j + 1) = k - j := by omega
    rw [this, pow_succ]; ring
  · simp

lemma csum_rec {R : Type*} [CommRing R] (z w : R) (k : ℕ) :
    csum z w (k + 2) = (z + w) * csum z w (k + 1) - z * w * csum z w k := by
  have h1 := csum_succ z w (k + 1)
  have h2 := csum_succ z w k
  rw [h1, h2]; ring

/-- **Chebyshev bound**: `|U_k(t/2)| ≤ k + 1` for `t² ≤ 4`, in recurrence form. -/
theorem cheb_bound (a : ℕ → ℝ) (t : ℝ) (ht : t ^ 2 ≤ 4) (h0 : a 0 = 1) (h1 : a 1 = t)
    (hrec : ∀ k, a (k + 2) = t * a (k + 1) - a k) : ∀ k, |a k| ≤ k + 1 := by
  set c : ℝ := t / 2 with hc
  have hc1 : c ^ 2 ≤ 1 := by rw [hc]; nlinarith
  set r : ℝ := Real.sqrt (1 - c ^ 2) with hr
  have hr2 : r ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
  set z : ℂ := ⟨c, r⟩ with hz
  set w : ℂ := ⟨c, -r⟩ with hw
  have hzw : z * w = 1 := by
    apply Complex.ext
    · simp only [hz, hw, Complex.mul_re, Complex.one_re]; nlinarith
    · simp only [hz, hw, Complex.mul_im, Complex.one_im]; ring
  have hzpw : z + w = (t : ℂ) := by
    apply Complex.ext
    · simp only [hz, hw, Complex.add_re, Complex.ofReal_re, hc]; ring
    · simp only [hz, hw, Complex.add_im, Complex.ofReal_im]; ring
  have hnz : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith
    have h0' := norm_nonneg z
    nlinarith
  have hnw : ‖w‖ = 1 := by
    have : ‖w‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith
    have h0' := norm_nonneg w
    nlinarith
  have key : ∀ k, ((a k : ℝ) : ℂ) = csum z w k ∧ ((a (k + 1) : ℝ) : ℂ) = csum z w (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [csum, h0]
      · simp only [csum, zero_add, sum_range_succ, sum_range_zero, h1]
        simp only [pow_zero, pow_one, one_mul, mul_one, Nat.sub_zero, Nat.sub_self]
        rw [← hzpw]; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, hrec k, csum_rec, hzpw, hzw, ← ih.1, ← ih.2]
      push_cast; ring
  intro k
  have hk : |a k| = ‖((a k : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hk, (key k).1]
  unfold csum
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_pow, hnz, hnw, one_pow, mul_one, sum_const, card_range, nsmul_eq_mul]
  push_cast; linarith

/-! ### Prime powers and multiplicativity -/

variable [DeligneBound]

/-- `|τ(p^k)| ≤ (k+1) p^{11k/2}` (`[DeligneBound]`). -/
theorem abs_tau_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |((tau (p ^ k) : ℤ) : ℝ)| ≤ (k + 1) * ((p : ℝ) ^ (11 / 2 : ℝ)) ^ k := by
  set s : ℝ := (p : ℝ) ^ (11 / 2 : ℝ) with hs
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _
  have hs2 : s ^ 2 = (p : ℝ) ^ 11 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  set a : ℕ → ℝ := fun k => ((tau (p ^ k) : ℤ) : ℝ) / s ^ k with ha
  set t : ℝ := ((tau p : ℤ) : ℝ) / s with htdef
  have ht : t ^ 2 ≤ 4 := by
    have hD := DeligneBound.bound p hp
    have hD' : (((tau p : ℤ) : ℝ)) ^ 2 ≤ 4 * (p : ℝ) ^ 11 := by exact_mod_cast hD
    rw [htdef, div_pow, div_le_iff₀ (by positivity), hs2]; exact hD'
  have h0 : a 0 = 1 := by simp [ha, tau_one]
  have h1 : a 1 = t := by simp [ha, htdef]
  have hrec : ∀ k, a (k + 2) = t * a (k + 1) - a k := by
    intro k
    have hH := tau_hecke_recurrence hp (r := k + 1) (by omega)
    rw [show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by omega] at hH
    have hH' : ((tau (p ^ (k + 2)) : ℤ) : ℝ) = ((tau p : ℤ) : ℝ) * ((tau (p ^ (k + 1)) : ℤ) : ℝ) -
        (p : ℝ) ^ 11 * ((tau (p ^ k) : ℤ) : ℝ) := by exact_mod_cast hH
    simp only [ha, htdef]
    rw [hH', ← hs2]
    field_simp
    ring
  have hb := cheb_bound a t ht h0 h1 hrec k
  have e : |((tau (p ^ k) : ℤ) : ℝ)| = |a k| * s ^ k := by
    simp only [ha]
    rw [abs_div, abs_of_pos (pow_pos hs0 k), div_mul_cancel₀ _ (pow_pos hs0 k).ne']
  rw [e]
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg hs0.le k)

/-- `|τ(n)| ≤ d(n) n^{11/2}` (`[DeligneBound]`). -/
theorem abs_tau_le_divisors (n : ℕ) :
    |((tau n : ℤ) : ℝ)| ≤ (#n.divisors : ℝ) * (n : ℝ) ^ (11 / 2 : ℝ) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.divisors_prime_pow hp, card_map, card_range]
    have := abs_tau_prime_pow_le hp k
    have e : ((p ^ k : ℕ) : ℝ) ^ (11 / 2 : ℝ) = ((p : ℝ) ^ (11 / 2 : ℝ)) ^ k := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity), mul_comm]
    rw [e]; push_cast; exact this
  | zero => simp [tau_zero]
  | one => simp [tau_one]
  | coprime a b _ _ hab iha ihb =>
    rw [tau_mul_coprime hab, Nat.Coprime.card_divisors_mul hab]
    push_cast
    rw [abs_mul, Real.mul_rpow (by positivity) (by positivity)]
    calc |((tau a : ℤ) : ℝ)| * |((tau b : ℤ) : ℝ)|
        ≤ ((#a.divisors : ℝ) * (a : ℝ) ^ (11 / 2 : ℝ)) * ((#b.divisors : ℝ) * (b : ℝ) ^ (11 / 2 : ℝ)) :=
          mul_le_mul iha ihb (abs_nonneg _) (by positivity)
      _ = _ := by ring

omit [DeligneBound]

/-! ### The divisor bound (adapted from the standard prime-by-prime argument) -/

lemma succ_le_C1_rpow' (β : ℝ) (hβ : 0 < β) (p e : ℕ) (hp : 2 ≤ p) :
    ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (((p : ℝ) ^ e) ^ β) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : ((2 : ℝ) ^ e) ^ β ≤ ((p : ℝ) ^ e) ^ β := by gcongr
  have h2 : ((2 : ℝ) ^ e) ^ β = Real.exp (e * β * Real.log 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have h3 : 1 + e * β * Real.log 2 ≤ Real.exp (e * β * Real.log 2) := by
    have := Real.add_one_le_exp (e * β * Real.log 2); linarith
  have hbl : 0 < β * Real.log 2 := by positivity
  have h4 : ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) := by
    have e1 : (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) =
        1 + e * (β * Real.log 2) + 1 / (β * Real.log 2) + e := by
      field_simp; ring
    rw [e1]
    have : 0 ≤ (e : ℝ) * (β * Real.log 2) := by positivity
    have : 0 ≤ 1 / (β * Real.log 2) := by positivity
    linarith
  calc ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) := h4
    _ ≤ (1 + 1 / (β * Real.log 2)) * (((p : ℝ) ^ e) ^ β) := by
        gcongr; rw [← h2] at h3; linarith

lemma succ_le_rpow_of_large' (β : ℝ) (hβ : 0 < β) (p e : ℕ) (hp : (2 : ℝ) ^ (1 / β) ≤ p) :
    ((e : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ β := by
  have hp0 : (0 : ℝ) ≤ p := le_trans (by positivity) hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ β := by
    have := Real.rpow_le_rpow (by positivity) hp hβ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hβ.ne', Real.rpow_one] at this
  have h3 : ((p : ℝ) ^ e) ^ β = ((p : ℝ) ^ β) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm]
  rw [h3]
  have h4 : ((e : ℝ) + 1) ≤ 2 ^ e := by
    have : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
    exact_mod_cast this
  exact h4.trans (pow_le_pow_left₀ (by norm_num) h2 e)

/-- **Divisor bound** `d(n) ≤ C_β n^β` (unconditional). -/
theorem card_divisors_le_rpow' (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ β := by
  classical
  set C₁ : ℝ := 1 + 1 / (β * Real.log 2) with hC₁
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁1 : 1 ≤ C₁ := by
    have : 0 ≤ 1 / (β * Real.log 2) := by positivity
    rw [hC₁]; linarith
  set P0 : ℕ := ⌈(2 : ℝ) ^ (1 / β)⌉₊
  refine ⟨C₁ ^ P0, one_le_pow₀ hC₁1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hpt : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      (if p < P0 then C₁ else 1) * (((p : ℝ) ^ n.factorization p) ^ β) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact succ_le_C1_rpow' β hβ p _ hp2
    · push Not at h
      rw [one_mul]
      exact succ_le_rpow_of_large' β hβ p _ ((Nat.le_ceil _).trans (by exact_mod_cast h))
  have hcard : (#n.divisors : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]; push_cast; rfl
  have h1 : (#n.divisors : ℝ) ≤
      ∏ p ∈ n.primeFactors, ((if p < P0 then C₁ else 1) * (((p : ℝ) ^ n.factorization p) ^ β)) := by
    rw [hcard]
    exact Finset.prod_le_prod (fun _ _ => by positivity) hpt
  rw [Finset.prod_mul_distrib] at h1
  have h2 : ∏ p ∈ n.primeFactors, (if p < P0 then C₁ else 1) ≤ C₁ ^ P0 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hC₁1 ?_
    calc (n.primeFactors.filter (fun p => p < P0)).card
        ≤ (Finset.range P0).card := Finset.card_le_card (fun p hp => by
          simp only [Finset.mem_filter] at hp; simpa using hp.2)
      _ = P0 := Finset.card_range _
  have h3 : ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p) ^ β) = (n : ℝ) ^ β := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    congr 1
    have := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at this
    conv_rhs => rw [← this]
    push_cast; rfl
  rw [h3] at h1
  calc (#n.divisors : ℝ) ≤ (∏ p ∈ n.primeFactors, (if p < P0 then C₁ else 1)) * (n : ℝ) ^ β := h1
    _ ≤ C₁ ^ P0 * (n : ℝ) ^ β := by gcongr

/-- **`|τ(n)| ≤ C_δ n^{11/2+δ}`** (`[DeligneBound]`). -/
theorem abs_tau_le_rpow [DeligneBound] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, |((tau n : ℤ) : ℝ)| ≤ C * (n : ℝ) ^ (11 / 2 + δ) := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_le_rpow' δ hδ
  refine ⟨C, hC1, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [tau_zero, Int.cast_zero, abs_zero, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc |((tau n : ℤ) : ℝ)| ≤ (#n.divisors : ℝ) * (n : ℝ) ^ (11 / 2 : ℝ) := abs_tau_le_divisors n
    _ ≤ (C * (n : ℝ) ^ δ) * (n : ℝ) ^ (11 / 2 : ℝ) := by gcongr; exact hC n hn
    _ = C * (n : ℝ) ^ (11 / 2 + δ) := by rw [Real.rpow_add hn0]; ring

end RamanujanTau.VoronoiPointwise
