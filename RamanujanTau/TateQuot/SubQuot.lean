/-
# Vélu's quotient of `Tate(s^p)` by `⟨s⟩` is `Tate(s)`

Over `K⟦s⟧`, `Tate(q)` with `q = s^p` has the order-`p` subgroup `⟨s⟩` with nonzero points
`P_k = (X_k, Y_k)`, `X_k = x(s^k) + 1/12`, `Y_k = θx(s^k)/2` (`1 ≤ k < p`), representatives
`S = {1, …, (p−1)/2}` of `(⟨s⟩ ∖ 0)/±`. Short model of `Tate(s^p)`: `A = a₄(s^p) − 1/48`,
`B = 1/864 − a₄(s^p)/12 + a₆(s^p)`. Vélu's `A'`, `B'` satisfy (`velu_sub_A`, `velu_sub_B`)
  `−48 A' = E₄(s)`, `864 B' = E₆(s)`,
i.e. the quotient is `Tate(s)` with its canonical differential.
-/
import RamanujanTau.TateQuot.SubSum

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]

/-- Short-model `A` of `Tate(s^p)`. -/
def AshS (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] : PowerSeries K := a4s K p - C (1 / 48)
/-- Short-model `B` of `Tate(s^p)`. -/
def BshS (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] : PowerSeries K :=
  C (1 / 864) - C (1 / 12) * a4s K p + a6s K p

/-- `X_k = x(s^k) + 1/12`. -/
def XB (K : Type*) [Field K] (p k : ℕ) : PowerSeries K := tB K p 0 k + C (1 / 12)
/-- `Y_k = θx(s^k)/2`. -/
def YB (K : Type*) [Field K] (p k : ℕ) : PowerSeries K := C (1 / 2) * tB K p 1 k

/-- **The points of `⟨s⟩` lie on the short model of `Tate(s^p)`.** -/
theorem sub_on_curve {k : ℕ} (hk : k ∈ Ico 1 p) :
    YB K p k ^ 2 = XB K p k ^ 3 + AshS K p * XB K p k + BshS K p := by
  have hk' := mem_Ico.mp hk
  have h := congrArg (ιL K) (tB_weier (K := K) (p := p) hk'.1 hk'.2)
  apply ιL_inj
  simp only [YB, XB, AshS, BshS, map_add, map_mul, map_pow, map_sub, map_ofNat, ιL_C, map_div₀,
    map_one] at h ⊢
  linear_combination (1 / 4 : LaurentSeries K) * h

lemma XB_sym {k : ℕ} (hk : k ∈ Ico 1 p) : XB K p (p - k) = XB K p k := by
  rw [XB, XB, tB0_sym hk]

/-- `Σ_{k=1}^{p−1} x(s^k)²`. -/
def T2B (K : Type*) [Field K] (p : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tB K p 0 k ^ 2
/-- `Σ_{k=1}^{p−1} x(s^k)³`. -/
def T3B (K : Type*) [Field K] (p : ℕ) : PowerSeries K := ∑ k ∈ Ico 1 p, tB K p 0 k ^ 3

lemma hsum2B : SB K p 2 = 6 * T2B K p + SB K p 0 + ((p - 1 : ℕ) : PowerSeries K) * (2 * a4s K p) := by
  rw [SB, sum_congr rfl fun k hk => tB_two (mem_Ico.mp hk).1 (mem_Ico.mp hk).2]
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2B, SB]
  ring

lemma hsum4B : SB K p 4 = 120 * T3B K p + 30 * T2B K p + (72 * a4s K p + 1) * SB K p 0 +
    ((p - 1 : ℕ) : PowerSeries K) * (48 * a6s K p + 2 * a4s K p) := by
  rw [SB, sum_congr rfl fun k hk => tB_four (mem_Ico.mp hk).1 (mem_Ico.mp hk).2]
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2B, T3B, SB]
  ring

lemma sumIcoB_A (A : PowerSeries K) :
    ∑ k ∈ Ico 1 p, (6 * XB K p k ^ 2 + 2 * A) = 6 * T2B K p + 12 * C (1 / 12) * SB K p 0 +
      ((p - 1 : ℕ) : PowerSeries K) * (6 * C (1 / 12) ^ 2 + 2 * A) := by
  have e : ∀ k, 6 * XB K p k ^ 2 + 2 * A = 6 * tB K p 0 k ^ 2 + 12 * C (1 / 12) * tB K p 0 k +
      (6 * C (1 / 12) ^ 2 + 2 * A) := fun k => by rw [XB]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2B, SB]
  ring

lemma sumIcoB_B (A B : PowerSeries K) :
    ∑ k ∈ Ico 1 p, (10 * XB K p k ^ 3 + 6 * A * XB K p k + 4 * B) =
      10 * T3B K p + 30 * C (1 / 12) * T2B K p + (30 * C (1 / 12) ^ 2 + 6 * A) * SB K p 0 +
      ((p - 1 : ℕ) : PowerSeries K) * (10 * C (1 / 12) ^ 3 + 6 * A * C (1 / 12) + 4 * B) := by
  have e : ∀ k, 10 * XB K p k ^ 3 + 6 * A * XB K p k + 4 * B = 10 * tB K p 0 k ^ 3 +
      30 * C (1 / 12) * tB K p 0 k ^ 2 + (30 * C (1 / 12) ^ 2 + 6 * A) * tB K p 0 k +
      (10 * C (1 / 12) ^ 3 + 6 * A * C (1 / 12) + 4 * B) := fun k => by rw [XB]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul, T2B, T3B, SB]
  ring

lemma a4s_eq : a4s K p = -5 * PowerSeries.expand p hp.out.ne_zero (sigK K 3) := by
  rw [a4s, a4K_eq, map_mul, map_neg, map_ofNat]

lemma a6s_eq : 12 * a6s K p = -(5 * PowerSeries.expand p hp.out.ne_zero (sigK K 3) +
    7 * PowerSeries.expand p hp.out.ne_zero (sigK K 5)) := by
  have h := congrArg (PowerSeries.expand p hp.out.ne_zero) (a6K_eq (K := K))
  simp only [map_mul, map_neg, map_add, map_ofNat] at h
  rw [a6s]; exact h

/-- **Vélu's `A'` for `⟨s⟩`**: `−48 A' = E₄(s)`. -/
theorem velu_sub_A (hp2 : p ≠ 2) :
    -48 * veluA (AshS K p) (Icc 1 (p / 2)) (XB K p) = ModP.E4 K := by
  have hh := half_sum hp2 (fun k => 6 * XB K p k ^ 2 + 2 * AshS K p)
    (fun k hk => by simp only [XB_sym hk])
  simp only [] at hh
  set J := ∑ k ∈ Icc 1 (p / 2), (6 * XB K p k ^ 2 + 2 * AshS K p) with hJ
  have hv : veluA (AshS K p) (Icc 1 (p / 2)) (XB K p) = AshS K p - 5 * J := rfl
  rw [hv]
  have hI := sumIcoB_A (K := K) (p := p) (AshS K p)
  have h2 := hsum2B (K := K) (p := p)
  have hS2 := SB_eq (K := K) (p := p) (m := 2) (Or.inr (Or.inl rfl))
  have ha4 := a4s_eq (K := K) (p := p)
  have hp1 : ((p - 1 : ℕ) : PowerSeries K) = (p : PowerSeries K) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [hp1] at hI h2
  rw [hI] at hh
  apply ιL_inj
  have hh' := congrArg (ιL K) hh
  have h2' := congrArg (ιL K) h2
  have hS2' := congrArg (ιL K) hS2
  have ha4' := congrArg (ιL K) ha4
  simp only [AshS, E4_eq, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat, map_one,
    map_natCast, ιL_C, map_div₀, OfNat.ofNat_ne_zero, if_false, zero_mul, add_zero,
    Nat.reduceAdd] at hh' h2' hS2' ha4' ⊢
  linear_combination -120 * hh' - 120 * h2' + 120 * hS2' - 48 * ha4'

/-- **Vélu's `B'` for `⟨s⟩`**: `864 B' = E₆(s)`. -/
theorem velu_sub_B (hp2 : p ≠ 2) :
    864 * veluB (AshS K p) (BshS K p) (Icc 1 (p / 2)) (XB K p) (YB K p) = ModP.E6 K := by
  have hsub : ∀ k ∈ Icc 1 (p / 2), k ∈ Ico 1 p := fun k hk => by
    have := hp.out.two_le
    simp only [mem_Icc, mem_Ico] at hk ⊢; omega
  have hcurve : ∑ k ∈ Icc 1 (p / 2), (4 * YB K p k ^ 2 + XB K p k * (6 * XB K p k ^ 2 + 2 * AshS K p)) =
      ∑ k ∈ Icc 1 (p / 2), (10 * XB K p k ^ 3 + 6 * AshS K p * XB K p k + 4 * BshS K p) :=
    sum_congr rfl fun k hk => by rw [sub_on_curve (hsub k hk)]; ring
  have hv : veluB (AshS K p) (BshS K p) (Icc 1 (p / 2)) (XB K p) (YB K p) =
      BshS K p - 7 * ∑ k ∈ Icc 1 (p / 2),
        (10 * XB K p k ^ 3 + 6 * AshS K p * XB K p k + 4 * BshS K p) := by
    rw [veluB, hcurve]
  rw [hv]
  have hh := half_sum hp2 (fun k => 10 * XB K p k ^ 3 + 6 * AshS K p * XB K p k + 4 * BshS K p)
    (fun k hk => by simp only [XB_sym hk])
  simp only [] at hh
  set J := ∑ k ∈ Icc 1 (p / 2), (10 * XB K p k ^ 3 + 6 * AshS K p * XB K p k + 4 * BshS K p)
    with hJ
  have hI := sumIcoB_B (K := K) (p := p) (AshS K p) (BshS K p)
  have h4 := hsum4B (K := K) (p := p)
  have hS4 := SB_eq (K := K) (p := p) (m := 4) (Or.inr (Or.inr rfl))
  have ha4 := a4s_eq (K := K) (p := p)
  have ha6 := a6s_eq (K := K) (p := p)
  have hp1 : ((p - 1 : ℕ) : PowerSeries K) = (p : PowerSeries K) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [hp1] at hI h4
  rw [hI] at hh
  apply ιL_inj
  have hh' := congrArg (ιL K) hh
  have h4' := congrArg (ιL K) h4
  have hS4' := congrArg (ιL K) hS4
  have ha4' := congrArg (ιL K) ha4
  have ha6' := congrArg (ιL K) ha6
  simp only [AshS, BshS, E6_eq, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat, map_one,
    map_natCast, ιL_C, map_div₀, OfNat.ofNat_ne_zero, if_false, zero_mul, add_zero,
    Nat.reduceAdd] at hh' h4' hS4' ha4' ha6' ⊢
  linear_combination 3024 * hh' + 252 * h4' - 252 * hS4' + 72 * ha6' - 72 * ha4'

end TateQuot
