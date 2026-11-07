/-
# Item 4 (part 4): Abel summation and the two-sided shifted-convolution bound

**`shiftSum2_bound_pos`**: for all `a, b ≥ 1`, `ℓ ≥ 1`, `N`,

    |Σ_{m,n ≤ N, am − bn = ℓ} λ(m)λ(n)| ≤ C N^{1−1/21} ℓ^{1/21} (ab)¹².

Abel summation of `Σ_{n ≤ N₁} wAB(n) cR(n)` (`shiftSum2_eq`), with the partial sums bounded by
`AsumAB_bound` for `t ≥ ℓ` (saving `t^{1/21}`) and by Cauchy–Schwarz (`sum_cR_cs`) for `t < ℓ`.
For `ℓ > N` the trivial bound `SCS2.abs_shiftSum2_le` suffices.
-/
import RamanujanTau.SCS2Coprime.AbelAB
import RamanujanTau.SCS2.Basic

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Finset MeasureTheory
open RamanujanTau.SubconvexityCond RamanujanTau.HeckeAFE RamanujanTau.SCSProof
  RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped Real

variable (a b : ℕ+) (ℓ : ℕ)

lemma mfun_ge {t : ℝ} (ht : 0 ≤ t) : t / a ≤ mfun a b ℓ t := by
  unfold mfun
  have hb : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  gcongr
  have := Nat.cast_nonneg (α := ℝ) ℓ; nlinarith

lemma mfun_le {t : ℝ} (ht : 0 ≤ t) (htl : t ≤ ℓ) : mfun a b ℓ t ≤ ((b : ℝ) + 1) * ℓ := by
  unfold mfun
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h0 : 0 ≤ (b : ℝ) * t + ℓ := by positivity
  calc ((b : ℝ) * t + ℓ) / a ≤ (b : ℝ) * t + ℓ := div_le_self h0 ha
    _ ≤ (b : ℝ) * ℓ + ℓ := by gcongr
    _ = _ := by ring

lemma mfun_mono {s t : ℝ} (hst : s ≤ t) : mfun a b ℓ s ≤ mfun a b ℓ t := by
  unfold mfun
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  gcongr

/-- `m(t)^{−11/2} ≤ a^{11/2} t^{−11/2}`. -/
lemma mfun_rpow_le {t : ℝ} (ht : 0 < t) :
    mfun a b ℓ t ^ (-(11 / 2 : ℝ)) ≤ (a : ℝ) ^ (11 / 2 : ℝ) * t ^ (-(11 / 2 : ℝ)) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  refine (Real.rpow_le_rpow_of_nonpos (by positivity) (mfun_ge a b ℓ ht.le) (by norm_num)).trans
    (le_of_eq ?_)
  rw [Real.div_rpow ht.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]

lemma rpow_split_half {ℓr N : ℝ} (hl : 1 ≤ ℓr) (hlN : ℓr ≤ N) :
    ℓr ^ (1 / 2 : ℝ) ≤ ℓr ^ ηt * N ^ (1 / 2 - ηt) := by
  have hl0 : 0 < ℓr := by linarith
  have e : ℓr ^ (1 / 2 : ℝ) = ℓr ^ ηt * ℓr ^ (1 / 2 - ηt) := by
    rw [← Real.rpow_add hl0]; ring_nf
  rw [e]
  gcongr
  unfold ηt; norm_num

lemma rpow_split_one {ℓr N : ℝ} (hl : 1 ≤ ℓr) (hlN : ℓr ≤ N) :
    ℓr ≤ ℓr ^ ηt * N ^ (1 - ηt) := by
  have hl0 : 0 < ℓr := by linarith
  have e : ℓr = ℓr ^ ηt * ℓr ^ (1 - ηt) := by
    rw [← Real.rpow_add hl0]; ring_nf; rw [Real.rpow_one]
  conv_lhs => rw [e]
  gcongr
  unfold ηt; norm_num

set_option maxHeartbeats 4000000 in
/-- **The integrand / boundary bound** `|w'(t)| |A(⌊t⌋)| ≤ K₁ t^{−η} + K₂ t^{−1/2}` and
`|w(n)| |A(n)| ≤ (K₁ + K₂') N^{1−η}`-type estimates, packaged for `t ≥ 1`. -/
lemma integrand_le (K Acs : ℝ) (hK0 : 0 ≤ K) (hAcs0 : 0 ≤ Acs) (N : ℕ) (hℓ : 1 ≤ ℓ)
    (hℓN : (ℓ : ℝ) ≤ N)
    (hL : ∀ k : ℕ, (ℓ : ℝ) ≤ (k : ℝ) + 1 → |AsumC (cR a b ℓ) k| ≤
      K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((b : ℝ) + 1) ^ 12 * ((k : ℝ) + 1) ^ (12 - ηt))
    (hC : ∀ k : ℕ, |AsumC (cR a b ℓ) k| ≤ Acs * (k : ℝ) ^ 6 * mfun a b ℓ k ^ 6)
    {t : ℝ} (ht : 1 ≤ t) :
    |wAB' a b ℓ t| * |AsumC (cR a b ℓ) ⌊t⌋₊| ≤
      11 * 2 ^ 12 * K * (ℓ : ℝ) ^ ηt * (a : ℝ) ^ (11 / 2 : ℝ) * ((b : ℝ) + 1) ^ 12 * t ^ (-ηt) +
        11 * Acs * ((b : ℝ) + 1) ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt) *
          t ^ (-(1 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hη := ηt_pos; have hη2 := ηt_le
  have hηe : ηt = 1 / 21 := rfl
  have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hm := mfun_pos a b ℓ ht0
  have hw := abs_wAB'_le a b ℓ ht0
  set B : ℝ := (b : ℝ) + 1
  have hB1 : 1 ≤ B := by have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; simp only [B]; linarith
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have p1 : 0 ≤ 11 * 2 ^ 12 * K * (ℓ : ℝ) ^ ηt * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * t ^ (-ηt) := by
    positivity
  have p2 : 0 ≤ 11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt) *
      t ^ (-(1 / 2 : ℝ)) := by positivity
  have hp13 : 0 < t ^ (-(13 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  rcases le_or_gt (ℓ : ℝ) t with hlt | hlt
  · -- large `t`: the saving
    have hA := hL ⌊t⌋₊ (by linarith)
    have hk2 : ((⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * t := by linarith
    have hpow : (((⌊t⌋₊ : ℕ) : ℝ) + 1) ^ (12 - ηt) ≤ 2 ^ 12 * t ^ (12 - ηt) := by
      calc (((⌊t⌋₊ : ℕ) : ℝ) + 1) ^ (12 - ηt) ≤ (2 * t) ^ (12 - ηt) :=
            Real.rpow_le_rpow (by positivity) hk2 (by linarith)
        _ = 2 ^ (12 - ηt) * t ^ (12 - ηt) := Real.mul_rpow (by norm_num) ht0.le
        _ ≤ 2 ^ 12 * t ^ (12 - ηt) := by
            gcongr
            calc (2 : ℝ) ^ (12 - ηt) ≤ 2 ^ (12 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 ^ 12 := by norm_num
    have hmr := mfun_rpow_le a b ℓ ht0
    have e : t ^ (-(13 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ)) * t ^ (12 - ηt) = t ^ (-ηt) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; ring_nf
    have hl21 : (ℓ : ℝ) ^ (1 / 21 : ℝ) = (ℓ : ℝ) ^ ηt := by rw [hηe]
    rw [hl21] at hA
    calc |wAB' a b ℓ t| * |AsumC (cR a b ℓ) ⌊t⌋₊|
        ≤ (11 * t ^ (-(13 / 2 : ℝ)) * ((a : ℝ) ^ (11 / 2 : ℝ) * t ^ (-(11 / 2 : ℝ)))) *
            (K * (ℓ : ℝ) ^ ηt * B ^ 12 * (2 ^ 12 * t ^ (12 - ηt))) := by
          gcongr
          · exact hw.trans (by gcongr)
          · exact hA.trans (by gcongr)
      _ = 11 * 2 ^ 12 * K * (ℓ : ℝ) ^ ηt * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 *
            (t ^ (-(13 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ)) * t ^ (12 - ηt)) := by ring
      _ = 11 * 2 ^ 12 * K * (ℓ : ℝ) ^ ηt * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * t ^ (-ηt) := by
          rw [e]
      _ ≤ _ := le_add_of_nonneg_right p2
  · -- small `t`: Cauchy–Schwarz
    have hA := hC ⌊t⌋₊
    have hmk : mfun a b ℓ ⌊t⌋₊ ≤ mfun a b ℓ t := mfun_mono a b ℓ hfl
    have hmk0 : 0 ≤ mfun a b ℓ ⌊t⌋₊ := by
      unfold mfun; have : (0 : ℝ) < a := by exact_mod_cast a.pos
      positivity
    have hA' : |AsumC (cR a b ℓ) ⌊t⌋₊| ≤ Acs * t ^ 6 * mfun a b ℓ t ^ 6 :=
      hA.trans (by gcongr)
    have e1 : t ^ (-(13 / 2 : ℝ)) * t ^ 6 = t ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
    have e2 : mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ 6 = mfun a b ℓ t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hm]; norm_num
    have hmB : mfun a b ℓ t ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) * ((ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt)) := by
      have h1 : mfun a b ℓ t ≤ B * ℓ := mfun_le a b ℓ ht0.le hlt.le
      calc mfun a b ℓ t ^ (1 / 2 : ℝ) ≤ (B * ℓ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hm.le h1 (by norm_num)
        _ = B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 2 : ℝ) := Real.mul_rpow (by linarith) (by linarith)
        _ ≤ _ := by gcongr; exact rpow_split_half hℓ1 hℓN
    calc |wAB' a b ℓ t| * |AsumC (cR a b ℓ) ⌊t⌋₊|
        ≤ (11 * t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ))) *
            (Acs * t ^ 6 * mfun a b ℓ t ^ 6) := by gcongr
      _ = 11 * Acs * (t ^ (-(13 / 2 : ℝ)) * t ^ 6) *
            (mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ 6) := by ring
      _ = 11 * Acs * t ^ (-(1 / 2 : ℝ)) * mfun a b ℓ t ^ (1 / 2 : ℝ) := by rw [e1, e2]
      _ ≤ 11 * Acs * t ^ (-(1 / 2 : ℝ)) *
            (B ^ (1 / 2 : ℝ) * ((ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt))) := by gcongr
      _ = 11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt) *
            t ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ _ := le_add_of_nonneg_left p1

set_option maxHeartbeats 4000000 in
/-- The boundary term. -/
lemma boundary_le (K Acs : ℝ) (hK0 : 0 ≤ K) (hAcs0 : 0 ≤ Acs) (N n₁ : ℕ) (hℓ : 1 ≤ ℓ)
    (hℓN : (ℓ : ℝ) ≤ N) (hn₁ : 1 ≤ n₁) (hn₁N : n₁ ≤ N)
    (hL : ∀ k : ℕ, (ℓ : ℝ) ≤ (k : ℝ) + 1 → |AsumC (cR a b ℓ) k| ≤
      K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((b : ℝ) + 1) ^ 12 * ((k : ℝ) + 1) ^ (12 - ηt))
    (hC : ∀ k : ℕ, |AsumC (cR a b ℓ) k| ≤ Acs * (k : ℝ) ^ 6 * mfun a b ℓ k ^ 6) :
    |wAB a b ℓ n₁| * |AsumC (cR a b ℓ) n₁| ≤
      (2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * ((b : ℝ) + 1) ^ 12 +
        Acs * ((b : ℝ) + 1) ^ (1 / 2 : ℝ)) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt) := by
  have hη := ηt_pos; have hη2 := ηt_le
  have hηe : ηt = 1 / 21 := rfl
  have ht1 : (1 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast hn₁
  have htN : (n₁ : ℝ) ≤ N := by exact_mod_cast hn₁N
  set t : ℝ := (n₁ : ℝ)
  have ht0 : 0 < t := by linarith
  have hm := mfun_pos a b ℓ ht0
  set B : ℝ := (b : ℝ) + 1
  have hB1 : 1 ≤ B := by have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; simp only [B]; linarith
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hw : |wAB a b ℓ t| = t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) := by
    unfold wAB; rw [abs_of_pos (by positivity)]
  rw [hw]
  have p1 : 0 ≤ 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt) := by
    positivity
  have p2 : 0 ≤ Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt) := by positivity
  rcases le_or_gt (ℓ : ℝ) (t + 1) with hlt | hlt
  · have hA := hL n₁ hlt
    have hpow : (t + 1) ^ (12 - ηt) ≤ 2 ^ 12 * t ^ (12 - ηt) := by
      calc (t + 1) ^ (12 - ηt) ≤ (2 * t) ^ (12 - ηt) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        _ = 2 ^ (12 - ηt) * t ^ (12 - ηt) := Real.mul_rpow (by norm_num) ht0.le
        _ ≤ 2 ^ 12 * t ^ (12 - ηt) := by
            gcongr
            calc (2 : ℝ) ^ (12 - ηt) ≤ 2 ^ (12 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 ^ 12 := by norm_num
    have hmr := mfun_rpow_le a b ℓ ht0
    have e : t ^ (-(11 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ)) * t ^ (12 - ηt) = t ^ (1 - ηt) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; ring_nf
    have hl21 : (ℓ : ℝ) ^ (1 / 21 : ℝ) = (ℓ : ℝ) ^ ηt := by rw [hηe]
    rw [hl21] at hA
    have htN' : t ^ (1 - ηt) ≤ (N : ℝ) ^ (1 - ηt) := Real.rpow_le_rpow ht0.le htN (by linarith)
    calc t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * |AsumC (cR a b ℓ) n₁|
        ≤ t ^ (-(11 / 2 : ℝ)) * ((a : ℝ) ^ (11 / 2 : ℝ) * t ^ (-(11 / 2 : ℝ))) *
            (K * (ℓ : ℝ) ^ ηt * B ^ 12 * (2 ^ 12 * t ^ (12 - ηt))) := by
          gcongr
          exact hA.trans (by gcongr)
      _ = 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt *
            (t ^ (-(11 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ)) * t ^ (12 - ηt)) := by ring
      _ = 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt * t ^ (1 - ηt) := by rw [e]
      _ ≤ 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt) := by
          gcongr
      _ ≤ _ := by nlinarith
  · have hA := hC n₁
    have e1 : t ^ (-(11 / 2 : ℝ)) * t ^ 6 = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
    have e2 : mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ 6 = mfun a b ℓ t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hm]; norm_num
    have htl : t ≤ ℓ := by linarith
    have hm1 : mfun a b ℓ t ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow hm.le (mfun_le a b ℓ ht0.le htl) (by norm_num)
    have ht2 : t ^ (1 / 2 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow ht0.le htl (by norm_num)
    have hll : (ℓ : ℝ) ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 2 : ℝ) = ℓ := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    calc t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * |AsumC (cR a b ℓ) n₁|
        ≤ t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) *
            (Acs * t ^ 6 * mfun a b ℓ t ^ 6) := by gcongr
      _ = Acs * (t ^ (-(11 / 2 : ℝ)) * t ^ 6) *
            (mfun a b ℓ t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ 6) := by ring
      _ = Acs * t ^ (1 / 2 : ℝ) * mfun a b ℓ t ^ (1 / 2 : ℝ) := by rw [e1, e2]
      _ ≤ Acs * (ℓ : ℝ) ^ (1 / 2 : ℝ) * (B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = Acs * B ^ (1 / 2 : ℝ) * ((ℓ : ℝ) ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = Acs * B ^ (1 / 2 : ℝ) * ℓ := by rw [hll]
      _ ≤ Acs * B ^ (1 / 2 : ℝ) * ((ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt)) := by
          gcongr; exact rpow_split_one hℓ1 hℓN
      _ ≤ _ := by nlinarith

set_option maxHeartbeats 8000000 in
/-- **Two-sided shifted-convolution bound, `ℓ ≥ 1`.** -/
theorem shiftSum2_bound_pos : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ+) (ℓ N : ℕ), 1 ≤ ℓ →
    |shiftSum2 a b ℓ N| ≤
      C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) * b) ^ 12 := by
  obtain ⟨K, hK0, hK⟩ := AsumAB_bound
  obtain ⟨Acs, hAcs0, hcs⟩ := sum_cR_cs
  obtain ⟨At, hAt0, hAt⟩ := RamanujanTau.SCS2.abs_shiftSum2_le
  set C : ℝ := 23 * (2 ^ 12 * K + Acs) * 2 ^ 12 + At
  refine ⟨C, by positivity, fun a b ℓ N hℓ => ?_⟩
  have hη := ηt_pos; have hη2 := ηt_le
  have hηe : ηt = 1 / 21 := rfl
  have hηh : ηt ≤ 1 / 2 := by rw [hηe]; norm_num
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hab1 : 1 ≤ ((a : ℝ) * b) ^ 12 := one_le_pow₀ (by nlinarith)
  have hR0 : 0 ≤ (N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) := by positivity
  rcases lt_or_ge (N : ℝ) ℓ with hNl | hlN
  · -- trivial range
    have h := hAt a b ℓ N a.one_le b.one_le
    refine h.trans ?_
    have hN : (N : ℝ) ≤ (N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) := by
      rcases Nat.eq_zero_or_pos N with h0 | hN0
      · rw [h0]; simp only [Nat.cast_zero]; positivity
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have e : (N : ℝ) = (N : ℝ) ^ (1 - 1 / 21 : ℝ) * (N : ℝ) ^ (1 / 21 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; norm_num
      conv_lhs => rw [e]
      gcongr
    have hAtC : At ≤ C := by simp only [C]; have : 0 ≤ 23 * (2 ^ 12 * K + Acs) * 2 ^ 12 := by positivity
                             linarith
    calc At * (N : ℝ) ≤ C * ((N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ)) := by
          gcongr
      _ ≤ C * ((N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ)) * ((a : ℝ) * b) ^ 12 := by
          have : 0 ≤ C * ((N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ)) := by positivity
          nlinarith
      _ = _ := by ring
  -- the main range `ℓ ≤ N`
  have hN1 : (1 : ℝ) ≤ N := hℓ1.trans hlN
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  rw [shiftSum2_eq a b ℓ N]
  set N₁ := N1 a b ℓ N
  have hN₁N : N₁ ≤ N := N1_le a b ℓ N
  rcases Nat.eq_zero_or_pos N₁ with h0 | hN₁
  · rw [h0]; simp [cR_zero]; positivity
  set c := cR a b ℓ
  have hL : ∀ k : ℕ, (ℓ : ℝ) ≤ (k : ℝ) + 1 → |AsumC c k| ≤
      K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((b : ℝ) + 1) ^ 12 * ((k : ℝ) + 1) ^ (12 - ηt) :=
    fun k hk => hK a b ℓ k hℓ hk
  have hC : ∀ k : ℕ, |AsumC c k| ≤ Acs * (k : ℝ) ^ 6 * mfun a b ℓ k ^ 6 := by
    intro k
    refine (abs_sum_le_sum_abs _ _).trans ((hcs a b ℓ k).trans (le_of_eq ?_))
    unfold mfun; ring
  -- Abel summation
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N₁, DifferentiableAt ℝ (wAB a b ℓ) t := fun t ht =>
    (hasDerivAt_wAB a b ℓ (by linarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv (wAB a b ℓ)) (Set.Icc (1 : ℝ) N₁) := by
    refine ((continuousOn_wAB' a b ℓ).mono fun t ht =>
      (show (0 : ℝ) < t by linarith [ht.1])).integrableOn_Icc
      |>.congr_fun (fun t ht => (deriv_wAB a b ℓ (by linarith [ht.1])).symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₀' c (cR_zero a b ℓ) N₁ hdiff hint
  have hAs : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, c k = AsumC c m := fun m => by
    rw [Icc_zero_eq_range]; rfl
  simp_rw [hAs] at hAbel
  rw [hAbel]
  set B : ℝ := (b : ℝ) + 1
  set K₁ : ℝ := 11 * 2 ^ 12 * K * (ℓ : ℝ) ^ ηt * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12
  set K₂ : ℝ := 11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 / 2 - ηt)
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hB : ∀ t ∈ Set.Ioc (1 : ℝ) N₁, ‖deriv (wAB a b ℓ) t * AsumC c ⌊t⌋₊‖ ≤
      K₁ * t ^ (-ηt) + K₂ * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    rw [deriv_wAB a b ℓ (by linarith [ht.1]), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact integrand_le a b ℓ K Acs hK0 hAcs0 N hℓ hlN hL hC ht.1.le
  have hint1 : IntegrableOn (fun t : ℝ => t ^ (-ηt)) (Set.Ioc (1 : ℝ) N₁) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Ioc (1 : ℝ) N₁) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by
      have := ht.1; show (t : ℝ) ≠ 0; linarith)
  have hBint : IntegrableOn (fun t : ℝ => K₁ * t ^ (-ηt) + K₂ * t ^ (-(1 / 2 : ℝ)))
      (Set.Ioc (1 : ℝ) N₁) := (hint1.const_mul _).add (hint2.const_mul _)
  have hN₁R : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hN₁NR : (N₁ : ℝ) ≤ N := by exact_mod_cast hN₁N
  have hI : ‖∫ t in Set.Ioc (1 : ℝ) N₁, deriv (wAB a b ℓ) t * AsumC c ⌊t⌋₊‖ ≤
      K₁ * (2 * (N₁ : ℝ) ^ (1 - ηt)) + K₂ * (2 * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ)) := by
    refine (norm_integral_le_of_norm_le hBint ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall hB))).trans ?_
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
    gcongr
    · exact integral_rpow_neg_le ηt hη.le hηh N₁ hN₁
    · exact integral_rpow_neg_le (1 / 2) (by norm_num) le_rfl N₁ hN₁
  have hbd := boundary_le a b ℓ K Acs hK0 hAcs0 N N₁ hℓ hlN hN₁ hN₁N hL hC
  -- numerics
  have h1 : (N₁ : ℝ) ^ (1 - ηt) ≤ (N : ℝ) ^ (1 - ηt) :=
    Real.rpow_le_rpow (by linarith) hN₁NR (by linarith)
  have h2 : (N : ℝ) ^ (1 / 2 - ηt) * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - ηt) := by
    have : (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
      exact Real.rpow_le_rpow (by linarith) hN₁NR (by norm_num)
    calc (N : ℝ) ^ (1 / 2 - ηt) * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ)
        ≤ (N : ℝ) ^ (1 / 2 - ηt) * (N : ℝ) ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add (by linarith)]; ring_nf
  have hX : (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 ≤ 2 ^ 12 * ((a : ℝ) * b) ^ 12 := by
    have ha' : (a : ℝ) ^ (11 / 2 : ℝ) ≤ (a : ℝ) ^ 12 := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
    have hB' : B ^ 12 ≤ (2 * b) ^ 12 := by gcongr; simp only [B]; linarith
    calc (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 ≤ (a : ℝ) ^ 12 * (2 * b) ^ 12 := by gcongr
      _ = _ := by ring
  have hY : B ^ (1 / 2 : ℝ) ≤ 2 ^ 12 * ((a : ℝ) * b) ^ 12 := by
    have hB1 : 1 ≤ B := by simp only [B]; linarith
    have : B ^ (1 / 2 : ℝ) ≤ B := by
      calc B ^ (1 / 2 : ℝ) ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
        _ = B := Real.rpow_one B
    have hB2 : B ≤ 2 * b := by simp only [B]; linarith
    have : (2 : ℝ) * b ≤ 2 ^ 12 * ((a : ℝ) * b) ^ 12 := by
      have hb12 : (b : ℝ) ≤ ((a : ℝ) * b) ^ 12 := by
        calc (b : ℝ) ≤ (a : ℝ) * b := by nlinarith
          _ ≤ ((a : ℝ) * b) ^ 12 := by
              have : 1 ≤ (a : ℝ) * b := by nlinarith
              calc (a : ℝ) * b = ((a : ℝ) * b) ^ 1 := (pow_one _).symm
                _ ≤ ((a : ℝ) * b) ^ 12 := pow_le_pow_right₀ this (by norm_num)
      nlinarith
    linarith
  have hl : (ℓ : ℝ) ^ ηt = (ℓ : ℝ) ^ (1 / 21 : ℝ) := by rw [hηe]
  have hNe : (N : ℝ) ^ (1 - ηt) = (N : ℝ) ^ (1 - 1 / 21 : ℝ) := by rw [hηe]
  have hLp : 0 ≤ (ℓ : ℝ) ^ ηt := by positivity
  have hNp : 0 ≤ (N : ℝ) ^ (1 - ηt) := by positivity
  have hK₂N : K₂ * (2 * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ)) ≤
      2 * (11 * Acs * B ^ (1 / 2 : ℝ)) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt) := by
    have h0 : 0 ≤ 11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt := by positivity
    calc K₂ * (2 * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ))
        = 2 * (11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt) *
            ((N : ℝ) ^ (1 / 2 - ηt) * (N₁ : ℝ) ^ (1 - 1 / 2 : ℝ)) := by simp only [K₂]; ring
      _ ≤ 2 * (11 * Acs * B ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ ηt) * (N : ℝ) ^ (1 - ηt) := by gcongr
      _ = _ := by ring
  have hK₁N : K₁ * (2 * (N₁ : ℝ) ^ (1 - ηt)) ≤
      2 * (11 * 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12) * (ℓ : ℝ) ^ ηt *
        (N : ℝ) ^ (1 - ηt) := by
    have h0 : 0 ≤ 11 * 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt := by
      positivity
    calc K₁ * (2 * (N₁ : ℝ) ^ (1 - ηt))
        = 2 * (11 * 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt) *
            (N₁ : ℝ) ^ (1 - ηt) := by simp only [K₁]; ring
      _ ≤ 2 * (11 * 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 * (ℓ : ℝ) ^ ηt) *
            (N : ℝ) ^ (1 - ηt) := by gcongr
      _ = _ := by ring
  have hbd' : |wAB a b ℓ N₁ * AsumC c N₁| ≤
      (2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 + Acs * B ^ (1 / 2 : ℝ)) * (ℓ : ℝ) ^ ηt *
        (N : ℝ) ^ (1 - ηt) := by
    rw [abs_mul]; exact hbd
  calc |wAB a b ℓ N₁ * AsumC c N₁ - ∫ t in Set.Ioc (1 : ℝ) N₁, deriv (wAB a b ℓ) t * AsumC c ⌊t⌋₊|
      ≤ |wAB a b ℓ N₁ * AsumC c N₁| +
          ‖∫ t in Set.Ioc (1 : ℝ) N₁, deriv (wAB a b ℓ) t * AsumC c ⌊t⌋₊‖ := by
        rw [Real.norm_eq_abs]; exact abs_sub _ _
    _ ≤ (2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12 + Acs * B ^ (1 / 2 : ℝ)) * (ℓ : ℝ) ^ ηt *
          (N : ℝ) ^ (1 - ηt) +
          (2 * (11 * 2 ^ 12 * K * (a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12) * (ℓ : ℝ) ^ ηt *
            (N : ℝ) ^ (1 - ηt) +
            2 * (11 * Acs * B ^ (1 / 2 : ℝ)) * (ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt)) :=
        add_le_add hbd' (hI.trans (add_le_add hK₁N hK₂N))
    _ = (23 * 2 ^ 12 * K * ((a : ℝ) ^ (11 / 2 : ℝ) * B ^ 12) + 23 * Acs * B ^ (1 / 2 : ℝ)) *
          ((ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt)) := by ring
    _ ≤ (23 * 2 ^ 12 * K * (2 ^ 12 * ((a : ℝ) * b) ^ 12) +
          23 * Acs * (2 ^ 12 * ((a : ℝ) * b) ^ 12)) * ((ℓ : ℝ) ^ ηt * (N : ℝ) ^ (1 - ηt)) := by
        gcongr
    _ = (23 * (2 ^ 12 * K + Acs) * 2 ^ 12) * (N : ℝ) ^ (1 - ηt) * (ℓ : ℝ) ^ ηt *
          ((a : ℝ) * b) ^ 12 := by ring
    _ ≤ C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) * b) ^ 12 := by
        rw [hl, hNe]
        gcongr
        simp only [C]; linarith

end RamanujanTau.SCS2Coprime
