import RamanujanTau.FiniteArithmetic.PartitionPrefix
import RamanujanTau.FiniteArithmetic.Rank607Identities
import RamanujanTau.FiniteArithmetic.PrecisionSquare
import RamanujanTau.BoylanWebb.Series
import RamanujanTau.PartitionCongruenceMod11

/-! # Packed modular series modulo `p²`, for any prime

A kernel program computing packed prefixes (`Packed.Rep`) modulo `p²` of
`(q;q)⁻¹`, `Δ`, `E₄`, `E₆`, the reduction of `E_{p-1}⁻¹`, and `Φ_p`, from the
pentagonal series alone, as in `Rank607Program`, but for every prime `p` and
prefix length `N ≤ min(2^13, 5p²)`.

`E₂ = 1 + θW/W` with `W = (q;q)^24`, `E₄ = E₂² − 12θE₂`, `E₆ = E₂E₄ − 3θE₄`,
`E_{p-1}⁻¹ ≡ 1 + 2p Σ σ_{p-2}(n) qⁿ (mod p²)`, and `σ_{p-2}(n) ≡ σ₁(n) m^{p-2}`
with `m` the prime-to-`p` part of `n < p³`.
The program only computes; `prelude_spec` proves what it computes.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.PackedPrime

open Packed PowerSeries
open MockTheta5.JTP (qfacInf partitionGF)

/-! ### The program -/

def mulP (p N a b : ℕ) : Option ℕ := mulR (p ^ 2) N (2 ^ 40 / p ^ 2) a b
def addP (p N a b : ℕ) : Option ℕ := addR (p ^ 2) N (2 ^ 40 / p ^ 2) a b
def redP (p N a : ℕ) : Option ℕ := reduceR (p ^ 2) N (2 ^ 40 / p ^ 2) a
/-- A lane map over `2^lv` lanes. -/
def mapN (lv N : ℕ) (h : ℕ → ℕ → ℕ) (a : ℕ) : ℕ := laneMap h lv 0 a % x ^ N

/-- Multiply by the lane index. -/
def thetaLane (p i v : ℕ) : ℕ := i * v % p ^ 2

/-- The prime-to-`p` part of `i`, for `i < p³`. -/
def ppart (p i : ℕ) : ℕ := if i % p = 0 then (if i / p % p = 0 then i / p / p else i / p) else i

/-- `2p (σ_{p-2}(i) mod p)` from the `E₂` lane `v`, with `c = (-24)⁻¹ mod p`. -/
def sigLane (p c i v : ℕ) : ℕ := 2 * p * ((v * c * ppart p i ^ (p - 2)) % p) % p ^ 2

def pow24 (p N a : ℕ) : Option ℕ := do
  let a2 ← mulP p N a a
  let a3 ← mulP p N a2 a
  let a6 ← mulP p N a3 a3
  let a12 ← mulP p N a6 a6
  mulP p N a12 a12

structure Prelude where
  pgf : ℕ
  dq : ℕ
  e4 : ℕ
  e6 : ℕ
  einv : ℕ
  phi : ℕ

def prelude (lv p N c R d k n ku kb kc : ℕ) : Option Prelude := do
  let Pi0 ← PartitionPrefix.pgfPrefixG (p ^ 2) R N d k n ku kb kc
  let Pi ← redP p N Pi0
  let P ← redP p N (PartitionPrefix.pentFast (p ^ 2) N d k)
  let W ← pow24 p N P
  let Wi ← pow24 p N Pi
  let e2a ← mulP p N (mapN lv N (thetaLane p) W) Wi
  let E2 ← addP p N e2a 1
  let sq ← mulP p N E2 E2
  let sc ← mulP p N (mapN lv N (thetaLane p) E2) (p ^ 2 - 12)
  let E4 ← addP p N sq sc
  let m24 ← mulP p N E2 E4
  let t3 ← mulP p N (mapN lv N (thetaLane p) E4) (p ^ 2 - 3)
  let E6 ← addP p N m24 t3
  let Ei ← addP p N 1 (mapN lv N (sigLane p c) E2)
  let e1 ← addP p N 1 (shiftR N (p ^ 2) (p ^ 2 - 1))
  let ec ← addP p N e1 (shiftR N (2 * p ^ 2) (p ^ 2 - 1))
  let ec5 ← addP p N ec (shiftR N (5 * p ^ 2) 1)
  let ec7 ← addP p N ec5 (shiftR N (7 * p ^ 2) 1)
  let ph ← mulP p N Pi ec7
  return ⟨Pi, shiftR N 1 W, E4, E6, Ei, shiftR N ((p ^ 2 - 1) / 24) ph⟩

/-! ### Divisor sums below `p³` -/

section Sigma
open ArithmeticFunction Rank607Identities
variable {p : ℕ} [hp : Fact p.Prime]

theorem sigma_sq_mul {k m : ℕ} (hk : 0 < k) (hpm : ¬ p ∣ m) :
    (sigma k (p ^ 2 * m) : ZMod p) = (sigma k m : ZMod p) := by
  have hco : Nat.Coprime (p ^ 2) m :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
  rw [(isMultiplicative_sigma (k := k)).map_mul_of_coprime hco]
  have hsp : (sigma k (p ^ 2) : ZMod p) = 1 := by
    rw [sigma_apply_prime_pow hp.out]
    push_cast
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hk.ne']
  push_cast
  rw [hsp, one_mul]

/-- `σ_{p-2}(n) ≡ σ₁(n) m^{p-2} (mod p)` for `0 < n < p³`, `m` the prime-to-`p` part. -/
theorem sigma_pred_eq3 (hp3 : 3 ≤ p) {n : ℕ} (hn : 0 < n) (hlt : n < p ^ 3) :
    (sigma (p - 2) n : ZMod p) = (sigma 1 n : ZMod p) * ((ppart p n : ℕ) : ZMod p) ^ (p - 2) := by
  have hp0 := hp.out.pos
  by_cases hd : n % p = 0
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hd
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    by_cases hd2 : m % p = 0
    · obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero hd2
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
      have hrlt : r < p := by
        have : p ^ 2 * r < p ^ 2 * p := by
          calc p ^ 2 * r = p * (p * r) := by ring
            _ < p ^ 3 := hlt
            _ = p ^ 2 * p := by ring
        exact Nat.lt_of_mul_lt_mul_left this
      have hpr : ¬ p ∣ r := fun h => absurd (Nat.le_of_dvd hr0 h) (by omega)
      have hpp : ppart p (p * (p * r)) = r := by
        simp [ppart, Nat.mul_div_cancel_left _ hp0, hp.out.ne_zero]
      rw [hpp, show p * (p * r) = p ^ 2 * r by ring, sigma_sq_mul (by omega) hpr,
        sigma_sq_mul one_pos hpr]
      exact sigma_pred_coprime hr0 hpr
    · have hpm : ¬ p ∣ m := fun h => hd2 (Nat.mod_eq_zero_of_dvd h)
      have hpp : ppart p (p * m) = m := by
        simp [ppart, Nat.mul_div_cancel_left _ hp0, hd2]
      rw [hpp, sigma_prime_mul (by omega) hpm, sigma_prime_mul one_pos hpm]
      exact sigma_pred_coprime hm0 hpm
  · have hpp : ppart p n = n := by simp [ppart, hd]
    rw [hpp]
    exact sigma_pred_coprime hn (fun h => hd (Nat.mod_eq_zero_of_dvd h))

end Sigma

/-! ### Correctness -/

section Spec
variable {p : ℕ} [hp : Fact p.Prime]

abbrev Rr (p : ℕ) : Type := ZMod (p ^ 2)

noncomputable abbrev rd (p : ℕ) : PowerSeries ℤ →+* PowerSeries (Rr p) :=
  PowerSeries.map (Int.castRingHom (Rr p))

variable {N lv : ℕ} {f g : PowerSeries (Rr p)}

lemma bind_some {α β : Type} {e : Option α} {f : α → Option β} {r : β}
    (h : (e >>= f) = some r) : ∃ a, e = some a ∧ f a = some r := by
  cases e with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

lemma rmul (hQ : p ^ 2 ≤ 2 ^ 21) (hlv : lv < 20) (hN : N ≤ 2 ^ lv) {a b r : ℕ} (ha : Rep N 22 a f)
    (hb : Rep N 22 b g) (h : mulP p N a b = some r) : Rep N 22 r (f * g) :=
  Rep.mulR hQ ha hb hN hlv h

lemma radd (hQ : p ^ 2 ≤ 2 ^ 21) {a b r : ℕ} (ha : Rep N 22 a f) (hb : Rep N 22 b g)
    (h : addP p N a b = some r) : Rep N 22 r (f + g) := Rep.addR hQ ha hb h

lemma rred (hQ : p ^ 2 ≤ 2 ^ 21) {k a r : ℕ} (ha : Rep N k a f) (h : redP p N a = some r) :
    Rep N 22 r f :=
  Rep.reduceR hQ ha h

lemma rep_nat (hN0 : 0 < N) {c : ℕ} (hc : c < 2 ^ 22) :
    Rep N 22 c (PowerSeries.C (c : Rr p)) := rep_C hN0 hc (by norm_num)

lemma rep_one (hN0 : 0 < N) : Rep N 22 1 (1 : PowerSeries (Rr p)) := by
  have h := rep_nat (p := p) hN0 (c := 1) (by norm_num)
  simpa using h

lemma rpow24 (hQ : p ^ 2 ≤ 2 ^ 21) (hlv : lv < 20) (hN : N ≤ 2 ^ lv) {a r : ℕ} (ha : Rep N 22 a f)
    (h : pow24 p N a = some r) : Rep N 22 r (f ^ 24) := by
  unfold pow24 at h
  obtain ⟨a2, h2, h⟩ := bind_some h
  obtain ⟨a3, h3, h⟩ := bind_some h
  obtain ⟨a6, h6, h⟩ := bind_some h
  obtain ⟨a12, h12, h⟩ := bind_some h
  have r2 := rmul hQ hlv hN ha ha h2
  have r3 := rmul hQ hlv hN r2 ha h3
  have r6 := rmul hQ hlv hN r3 r3 h6
  have r12 := rmul hQ hlv hN r6 r6 h12
  have r24 := rmul hQ hlv hN r12 r12 h
  convert r24 using 1
  ring

lemma rep_theta (hQ : p ^ 2 ≤ 2 ^ 21) (hN : N ≤ 2 ^ lv) {a : ℕ} (ha : Rep N 22 a f) :
    Rep N 22 (mapN lv N (thetaLane p) a) (Igusa.theta f) := by
  have hQ0 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  refine ha.laneMap (thetaLane p) hN (by norm_num) (fun i v _ => ?_) fun i hi v hv => ?_
  · exact lt_of_lt_of_le (Nat.mod_lt _ hQ0) (by omega)
  · rw [Igusa.coeff_theta, ← hv, thetaLane, ZMod.natCast_mod]
    push_cast
    ring


/-! ### Series facts -/

lemma qfac_small : coeff 0 qfacInf = 1 ∧ coeff 1 qfacInf = -1 ∧ coeff 2 qfacInf = -1 ∧
    coeff 3 qfacInf = 0 ∧ coeff 4 qfacInf = 0 ∧ coeff 5 qfacInf = 1 ∧ coeff 6 qfacInf = 0 ∧
    coeff 7 qfacInf = 1 ∧ coeff 8 qfacInf = 0 ∧ coeff 9 qfacInf = 0 ∧ coeff 10 qfacInf = 0 ∧
    coeff 11 qfacInf = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [MockTheta5.JTP.coeff_qfacInf_box _ 11 (by norm_num)]
    decide

/-- `E_{p-1}⁻¹ ≡ 1 + 2p Σ σ_{p-2}(n) qⁿ (mod p²)`. -/
theorem map_Einv_two (hp5 : 5 ≤ p) :
    PowerSeries.map (PadicInt.toZModPow (p := p) 2) (AtkinOBrienFinal.Einv p hp5) =
      1 + C (2 * (p : Rr p)) * sigmaSeriesSquare p := by
  set I := PowerSeries.map (PadicInt.toZModPow (p := p) 2) (AtkinOBrienFinal.Einv p hp5)
  set S := sigmaSeriesSquare p
  have hE := map_E_square_general (p := p) hp5
  have hEI : (1 - C (2 * (p : Rr p)) * S) * I = 1 := by
    rw [← hE, ← map_mul, AtkinOBrienFinal.E_mul_Einv, map_one]
  have hp2 : (p : Rr p) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsq : (1 - C (2 * (p : Rr p)) * S) * (1 + C (2 * (p : Rr p)) * S) = 1 := by
    have : C (2 * (p : Rr p)) * C (2 * (p : Rr p)) = 0 := by
      rw [← map_mul, show 2 * (p : Rr p) * (2 * p) = 4 * p ^ 2 by ring, hp2, mul_zero, map_zero]
    linear_combination (-S ^ 2) * this
  calc I = I * ((1 - C (2 * (p : Rr p)) * S) * (1 + C (2 * (p : Rr p)) * S)) := by rw [hsq, mul_one]
    _ = ((1 - C (2 * (p : Rr p)) * S) * I) * (1 + C (2 * (p : Rr p)) * S) := by ring
    _ = _ := by rw [hEI, one_mul]

lemma coeff_E2_pos {i : ℕ} (hi : 0 < i) :
    coeff i (Igusa.E2 (Rr p)) = -24 * (ArithmeticFunction.sigma 1 i : Rr p) := by
  rw [Igusa.E2, PowerSeries.coeff_map, Igusa.e2Z, map_sub, PowerSeries.coeff_one, if_neg hi.ne',
    show (24 : PowerSeries ℤ) = PowerSeries.C (24 : ℤ) by simp, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk]
  simp

/-- The arithmetic of the denominator lane. -/
theorem sigLane_cast (hp5 : 5 ≤ p) {c i v : ℕ} (hc : (24 * c + 1) % p = 0) (hi : i < p ^ 3)
    (hv : (v : Rr p) = coeff i (Igusa.E2 (Rr p))) :
    (sigLane p c i v : Rr p) = coeff i (C (2 * (p : Rr p)) * sigmaSeriesSquare p) := by
  rw [PowerSeries.coeff_C_mul, sigmaSeriesSquare, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h0 : ppart p 0 = 0 := by simp [ppart]
    simp [sigLane, h0, show p - 2 ≠ 0 by omega]
  · set y : ℕ := (v * c * ppart p i ^ (p - 2)) % p
    have hy : sigLane p c i v = 2 * p * y % p ^ 2 := rfl
    have hsig := sigma_pred_eq3 (p := p) (by omega) hpos hi
    have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    have hv' : (v : ZMod p) = -24 * (ArithmeticFunction.sigma 1 i : ZMod p) := by
      have h := hv
      rw [coeff_E2_pos hpos] at h
      have hm := congrArg (ZMod.castHom hdvd (ZMod p)) h
      simp only [map_mul, map_neg, map_natCast, map_ofNat] at hm
      exact hm
    have hcu : (-24 * (c : ZMod p)) = 1 := by
      have h0 : ((24 * c + 1 : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc
      push_cast at h0
      linear_combination -h0
    have hyc : (y : ZMod p) = (ArithmeticFunction.sigma (p - 2) i : ZMod p) := by
      rw [hsig]
      simp only [y, ZMod.natCast_mod]
      push_cast
      rw [hv']
      linear_combination
        ((ArithmeticFunction.sigma 1 i : ZMod p) * (ppart p i : ZMod p) ^ (p - 2)) * hcu
    have hmod : y ≡ ArithmeticFunction.sigma (p - 2) i [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hyc
    have hmod2 : p * y ≡ p * ArithmeticFunction.sigma (p - 2) i [MOD p * p] :=
      Nat.ModEq.mul_left' p hmod
    have hcast : ((p * y : ℕ) : Rr p) = ((p * ArithmeticFunction.sigma (p - 2) i : ℕ) : Rr p) := by
      rw [ZMod.natCast_eq_natCast_iff, pow_two]; exact hmod2
    rw [hy, ZMod.natCast_mod]
    push_cast at hcast ⊢
    linear_combination 2 * hcast

/-- What `prelude` certifies. -/
structure PreludeSpec (p N : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (pr : Prelude) : Prop where
  pgf : Rep N 22 pr.pgf (rd p partitionGF)
  dq : Rep N 22 pr.dq (ModP.Dq (Rr p))
  e4 : Rep N 22 pr.e4 (ModP.E4 (Rr p))
  e6 : Rep N 22 pr.e6 (ModP.E6 (Rr p))
  einv : Rep N 22 pr.einv
    (PowerSeries.map (PadicInt.toZModPow (p := p) 2) (AtkinOBrienFinal.Einv p hp5))
  phi : Rep N 22 pr.phi (rd p (BoylanWebb.Φ p))


/-- `(q^{p²}; q^{p²}) ≡ 1 - q^{p²} - q^{2p²} + q^{5p²} + q^{7p²}` below `q^{12p²}`. -/
lemma ea_trunc {N : ℕ} (hN7 : N ≤ 12 * p ^ 2) :
    (X : PowerSeries (Rr p)) ^ N ∣
      rd p (RankProof.Ea (p ^ 2) (TauCong.ppow_ne p 2) qfacInf) -
        (1 - X ^ (p ^ 2 * 1) - X ^ (p ^ 2 * 2) + X ^ (p ^ 2 * 5) + X ^ (p ^ 2 * 7)) := by
  refine PowerSeries.X_pow_dvd_iff.mpr fun j hj => ?_
  have hj7 : j < 12 * p ^ 2 := lt_of_lt_of_le hj hN7
  have hQ0 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  rw [map_sub, PowerSeries.coeff_map, RankProof.coeff_Ea]
  simp only [map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := qfac_small
  by_cases hd : p ^ 2 ∣ j
  · obtain ⟨t, rfl⟩ := hd
    have ht : t < 12 := by
      by_contra hc; push Not at hc
      have : p ^ 2 * 12 ≤ p ^ 2 * t := Nat.mul_le_mul_left _ hc
      omega
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hQ0]
    have hc : ∀ c, (p ^ 2 * t = p ^ 2 * c ↔ t = c) := fun c => Nat.mul_left_cancel_iff hQ0
    have h0 : (p ^ 2 * t = 0 ↔ t = 0) := by
      rw [show (0 : ℕ) = p ^ 2 * 0 by ring]; exact hc 0
    simp only [hc, h0]
    interval_cases t <;> simp [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11]
  · rw [if_neg hd]
    have hne : ∀ c, j ≠ p ^ 2 * c := fun c h => hd (h ▸ dvd_mul_right _ _)
    have h0 : j ≠ 0 := fun h => hd (h ▸ dvd_zero _)
    have h1 : j ≠ p ^ 2 := by simpa using hne 1
    simp [hne, h0, h1]

lemma alg_E4' {S : Type*} [CommRing S] (a b : PowerSeries S) :
    a * a + b * PowerSeries.C (-(12 : S)) = a ^ 2 - 12 * b := by
  rw [map_neg, map_ofNat]; ring

lemma cast_sub_nat (c : ℕ) (hc : c ≤ p ^ 2) : (((p ^ 2 - c : ℕ)) : Rr p) = -(c : Rr p) := by
  rw [Nat.cast_sub hc, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_sub]

theorem prelude_spec (hp5 : 5 ≤ p) (hQ : p ^ 2 ≤ 2 ^ 21) (hN0 : 0 < N) (hlv : lv < 20) (hN : N ≤ 2 ^ lv)
    (hN5 : N ≤ 12 * p ^ 2) (hp3 : N < p ^ 3) {c R d k n ku kb kc : ℕ} (hc : (24 * c + 1) % p = 0)
    (hk : ku + kb + lv < 64) (hno : 2 ^ 22 + p ^ 2 * 2 ^ kc ≤ x)
    (hn : k * 2 ^ d ≤ 2 ^ 20) (hJ : N ≤ PartitionPrefix.pentLow (k * 2 ^ d))
    {pr : Prelude} (h : prelude lv p N c R d k n ku kb kc = some pr) : PreludeSpec p N hp5 pr := by
  have hQ1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  unfold prelude at h
  obtain ⟨Pi0, hPi0, h⟩ := bind_some h
  obtain ⟨Pi, hPi, h⟩ := bind_some h
  obtain ⟨P, hP, h⟩ := bind_some h
  obtain ⟨Wa, hW, h⟩ := bind_some h
  obtain ⟨Wi, hWi, h⟩ := bind_some h
  obtain ⟨e2a, he2a, h⟩ := bind_some h
  obtain ⟨E2a, hE2, h⟩ := bind_some h
  obtain ⟨sq, hsq, h⟩ := bind_some h
  obtain ⟨sc, hsc, h⟩ := bind_some h
  obtain ⟨E4a, hE4, h⟩ := bind_some h
  obtain ⟨m24, hm24, h⟩ := bind_some h
  obtain ⟨t3, ht3, h⟩ := bind_some h
  obtain ⟨E6a, hE6, h⟩ := bind_some h
  obtain ⟨Ei, hEi, h⟩ := bind_some h
  obtain ⟨e1, he1, h⟩ := bind_some h
  obtain ⟨ec, hec, h⟩ := bind_some h
  obtain ⟨ec5, hec5, h⟩ := bind_some h
  obtain ⟨ec7, hec7, h⟩ := bind_some h
  obtain ⟨ph, hph, h⟩ := bind_some h
  obtain rfl := Option.some.inj h
  have rPi : Rep N 22 Pi (rd p partitionGF) :=
    rred hQ (PartitionPrefix.rep_pgfPrefixG hQ1 hQ hk hno hN0 hN hn hJ hPi0) hPi
  have rP : Rep N 22 P (rd p qfacInf) :=
    rred hQ (PartitionPrefix.rep_pentFast hQ1 hQ hn hJ) hP
  have hinv : rd p qfacInf * rd p partitionGF = 1 := by
    rw [← map_mul, BoylanWebb.qfac_mul_pgf, map_one]
  have rW : Rep N 22 Wa (Rank607Identities.W (Rr p)) := by
    have h24 := rpow24 hQ hlv hN rP hW
    rwa [Rank607Identities.W, map_pow]
  have rWi : Rep N 22 Wi (rd p partitionGF ^ 24) := rpow24 hQ hlv hN rPi hWi
  have hWinv : Rank607Identities.W (Rr p) * rd p partitionGF ^ 24 = 1 := by
    rw [Rank607Identities.W, map_pow, ← mul_pow, hinv, one_pow]
  have rE2 : Rep N 22 E2a (Igusa.E2 (Rr p)) := by
    have h := radd hQ (rmul hQ hlv hN (rep_theta hQ hN rW) rWi he2a) (rep_one hN0) hE2
    rwa [← Rank607Identities.E2_eq_of_inv (Rr p) hWinv] at h
  have rE4 : Rep N 22 E4a (ModP.E4 (Rr p)) := by
    have hc12 := rep_nat (p := p) hN0 (c := p ^ 2 - 12) (by omega)
    rw [cast_sub_nat 12 (by nlinarith [hp5]), Nat.cast_ofNat] at hc12
    have h := radd hQ (rmul hQ hlv hN rE2 rE2 hsq) (rmul hQ hlv hN (rep_theta hQ hN rE2) hc12 hsc) hE4
    rwa [alg_E4', ← Rank607Identities.E4_eq (Rr p)] at h
  have rE6 : Rep N 22 E6a (ModP.E6 (Rr p)) := by
    have hc3 := rep_nat (p := p) hN0 (c := p ^ 2 - 3) (by omega)
    rw [cast_sub_nat 3 (by nlinarith [hp5]), Nat.cast_ofNat] at hc3
    have h := radd hQ (rmul hQ hlv hN rE2 rE4 hm24) (rmul hQ hlv hN (rep_theta hQ hN rE4) hc3 ht3) hE6
    obtain ⟨h4, -, -⟩ := RamanujanODEProof.ramanujanODE
    have h4' := congrArg (PowerSeries.map (Int.castRingHom (Rr p))) h4
    simp only [map_mul, map_sub, Igusa.map_theta, Rank607Identities.map_E2, ModP.map_E4,
      ModP.map_E6, map_ofNat] at h4'
    have he6 : ModP.E6 (Rr p) = Igusa.E2 (Rr p) * ModP.E4 (Rr p) +
        Igusa.theta (ModP.E4 (Rr p)) * PowerSeries.C (-(3 : Rr p)) := by
      rw [map_neg]
      have : PowerSeries.C (3 : Rr p) = 3 := map_ofNat _ 3
      rw [this]; linear_combination h4'
    rw [he6]; exact h
  have rEi : Rep N 22 Ei
      (PowerSeries.map (PadicInt.toZModPow (p := p) 2) (AtkinOBrienFinal.Einv p hp5)) := by
    rw [map_Einv_two hp5]
    refine radd hQ (rep_one hN0) ?_ hEi
    refine rE2.laneMap (sigLane p c) hN (by norm_num) (fun i v _ => ?_) fun i hi v hv => ?_
    · exact lt_of_lt_of_le (Nat.mod_lt _ (pow_pos hp.out.pos 2)) (by omega)
    · exact sigLane_cast hp5 hc (lt_trans hi hp3) hv
  have rD : Rep N 22 (shiftR N 1 Wa) (ModP.Dq (Rr p)) := by
    have h := Rep.shiftR (d := 1) rW (by norm_num : 22 ≤ 64)
    rwa [pow_one, ← Rank607Identities.Dq_eq] at h
  -- `Φ`: the factor `(q^{p²}; q^{p²})` is `1 - q^{p²} - q^{2p²}` below `q^{5p²}`.
  have hm1 := rep_nat (p := p) hN0 (c := p ^ 2 - 1) (by omega)
  rw [cast_sub_nat 1 hQ1, Nat.cast_one] at hm1
  have r1 := radd hQ (rep_one hN0) (Rep.shiftR (d := p ^ 2) hm1 (by norm_num)) he1
  have r2 := radd hQ r1 (Rep.shiftR (d := 2 * p ^ 2) hm1 (by norm_num)) hec
  have r5 := radd hQ r2 (Rep.shiftR (d := 5 * p ^ 2) (rep_one hN0) (by norm_num)) hec5
  have r7 := radd hQ r5 (Rep.shiftR (d := 7 * p ^ 2) (rep_one hN0) (by norm_num)) hec7
  have r3 := Rep.shiftR (d := (p ^ 2 - 1) / 24) (rmul hQ hlv hN rPi r7 hph) (by norm_num)
  refine ⟨rPi, rD, rE4, rE6, rEi, r3.congr fun i hi => ?_⟩
  set ecS : PowerSeries (Rr p) := 1 + X ^ (p ^ 2) * C (-1) + X ^ (2 * p ^ 2) * C (-1) +
    X ^ (5 * p ^ 2) * 1 + X ^ (7 * p ^ 2) * 1
  have hecS : ecS = 1 - X ^ (p ^ 2 * 1) - X ^ (p ^ 2 * 2) + X ^ (p ^ 2 * 5) + X ^ (p ^ 2 * 7) := by
    simp only [ecS, map_neg, map_one, mul_one]; ring_nf
  let E := RankProof.Ea (p ^ 2) (TauCong.ppow_ne p 2) qfacInf
  have hdvd := ea_trunc (p := p) hN5
  rw [← hecS] at hdvd
  have hexp : rd p (BoylanWebb.Φ p) = X ^ ((p ^ 2 - 1) / 24) * (rd p partitionGF * ecS) +
      (rd p E - ecS) * (X ^ ((p ^ 2 - 1) / 24) * rd p partitionGF) := by
    rw [BoylanWebb.Φ, map_mul, map_mul, map_pow, PowerSeries.map_X]
    change X ^ ((p ^ 2 - 1) / 24) * rd p E * rd p partitionGF = _
    ring
  rw [hexp, map_add]
  have hz : PowerSeries.coeff i ((rd p E - ecS) * (X ^ ((p ^ 2 - 1) / 24) * rd p partitionGF)) = 0 :=
    PowerSeries.X_pow_dvd_iff.mp (Dvd.dvd.mul_right hdvd _) i hi
  rw [hz, add_zero]

end Spec

end RamanujanTau.FiniteArithmetic.PackedPrime
