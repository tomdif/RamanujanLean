import RamanujanTau.FiniteArithmetic.Rank607Program
import RamanujanTau.FiniteArithmetic.Rank607Identities
import RamanujanTau.FiniteArithmetic.PrecisionSquare
import RamanujanTau.BoylanWebb.Series
import RamanujanTau.MockTheta5PentagonalRecurrence

/-! # Correctness of the prime-607 prelude

Each step of `Rank607Program.prelude` is matched with the actual series it
packs. The proofs unroll the program as hypotheses and never evaluate it. -/
set_option autoImplicit false
set_option linter.unusedVariables false

namespace RamanujanTau.FiniteArithmetic.Rank607Series

open PowerSeries Packed Rank607Program Rank607Identities
open MockTheta5.JTP (qfacInf partitionGF pentSeries euler_pentagonal coeff_pentSeries_lt
  map_evm1_pentFiniteP sgn sgn_natCast sgn_neg sgn_succ isUnit_qfacInf)

/-- The coefficient ring. -/
abbrev R : Type := ZMod Q

/-- Reduction modulo `607²`. -/
noncomputable abbrev rd : PowerSeries ℤ →+* PowerSeries R :=
  PowerSeries.map (Int.castRingHom R)

instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

lemma hQ : Q ≤ 2 ^ 21 := by norm_num

lemma hN : N ≤ 2 ^ 16 := by norm_num

lemma bind_some {α β : Type} {e : Option α} {f : α → Option β} {r : β}
    (h : (e >>= f) = some r) : ∃ a, e = some a ∧ f a = some r := by
  cases e with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

variable {f g : PowerSeries R}

lemma rmul {a b r : ℕ} (ha : Rep N 22 a f) (hb : Rep N 22 b g) (h : mulQ a b = some r) :
    Rep N 22 r (f * g) :=
  Rep.mulR hQ ha hb hN (by norm_num) h

lemma radd {a b r : ℕ} (ha : Rep N 22 a f) (hb : Rep N 22 b g) (h : addQ a b = some r) :
    Rep N 22 r (f + g) :=
  Rep.addR hQ ha hb h

lemma rep_nat {c : ℕ} (hc : c < 2 ^ 22) : Rep N 22 c (PowerSeries.C (c : R)) :=
  rep_C (by norm_num) hc (by norm_num)

lemma rep_one : Rep N 22 1 (1 : PowerSeries R) := by
  have h := rep_nat (c := 1) (by norm_num)
  simpa using h

/-! ### The pentagonal prefix -/

/-- The partial pentagonal sum computed by `pentFold`. -/
noncomputable def pentPartial : ℕ → PowerSeries R
  | 0 => 1
  | j + 1 => pentPartial j +
      X ^ pentLow j * PowerSeries.C (pentSign j : R) +
      X ^ pentHigh j * PowerSeries.C (pentSign j : R)

lemma pentSign_lt (j : ℕ) : pentSign j < 2 ^ 22 := by
  unfold pentSign
  split_ifs <;> norm_num

theorem pentFold_rep (J : ℕ) {a : ℕ} (h : pentFold J = some a) :
    Rep N 22 a (pentPartial J) := by
  induction J generalizing a with
  | zero =>
    obtain rfl : 1 = a := Option.some.inj h
    exact rep_one
  | succ j ih =>
    obtain ⟨a0, h0, h1⟩ := bind_some h
    obtain ⟨b, h2, h3⟩ := bind_some h1
    have hs := fun d => Rep.shiftR (d := d) (rep_nat (pentSign_lt j)) (by norm_num : 22 ≤ 64)
    exact radd (radd (ih h0) (hs _) h2) (hs _) h3

lemma cast_pentSign (j : ℕ) : (pentSign j : R) = ((-1 : ℤ) ^ (j + 1) : ℤ) := by
  unfold pentSign
  have hQ1 : ((Q - 1 : ℕ) : R) = -1 := by
    rw [Nat.cast_sub (by norm_num), ZMod.natCast_self]
    simp
  split_ifs with h
  · have he : Even j := Nat.even_iff.mpr h
    rw [hQ1, pow_succ, he.neg_one_pow]
    simp
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    rw [pow_succ, ho.neg_one_pow]
    simp

lemma sgn_pos (m : ℕ) : sgn ((m : ℤ) + 1) = (-1 : ℤ) ^ (m + 1) := by
  rw [sgn_succ, sgn_natCast, pow_succ]; ring

lemma pentLow_eq (m : ℕ) : pentLow m = (m + 1) * (3 * m + 2) / 2 := by
  unfold pentLow; congr 2

lemma pentHigh_eq (m : ℕ) : pentHigh m = (m + 1) * (3 * m + 4) / 2 := by
  unfold pentHigh; congr 2

/-- The reduced truncation of the pentagonal series agrees with `pentPartial`. -/
lemma rd_truncation (M : ℕ) :
    rd (1 + ∑ m ∈ Finset.range M,
        (X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (sgn ((m : ℤ) + 1))
          + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (sgn (-((m : ℤ) + 1))))) =
      pentPartial M := by
  induction M with
  | zero => simp [pentPartial]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, pentPartial, map_add, map_mul, map_mul,
      map_pow, map_pow, PowerSeries.map_X, PowerSeries.map_C, PowerSeries.map_C, sgn_neg, sgn_pos,
      ← pentLow_eq, ← pentHigh_eq, cast_pentSign]
    simp only [eq_intCast]
    ring

lemma pentLow_mono {m n : ℕ} (h : m ≤ n) : pentLow m ≤ pentLow n := by
  rw [pentLow_eq, pentLow_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

lemma pentHigh_mono {m n : ℕ} (h : m ≤ n) : pentHigh m ≤ pentHigh n := by
  rw [pentHigh_eq, pentHigh_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

/-- Pentagonal pairs beyond `pentCount` do not meet the prefix. -/
lemma coeff_pentPartial_stable (i : ℕ) (hi : i < N) (k : ℕ) :
    PowerSeries.coeff i (pentPartial (pentCount + k)) =
      PowerSeries.coeff i (pentPartial pentCount) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, pentPartial, map_add, map_add, ih, mul_comm (X ^ pentLow _),
      mul_comm (X ^ pentHigh _), PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    have h1 : N ≤ pentLow (pentCount + k) :=
      le_trans (by norm_num [pentLow, pentCount]) (pentLow_mono (Nat.le_add_right _ k))
    have h2 : N ≤ pentHigh (pentCount + k) :=
      le_trans (by norm_num [pentHigh, pentCount]) (pentHigh_mono (Nat.le_add_right _ k))
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem coeff_rd_qfacInf (i : ℕ) (hi : i < N) :
    PowerSeries.coeff i (rd qfacInf) = PowerSeries.coeff i (pentPartial pentCount) := by
  rw [← coeff_pentPartial_stable i hi (i + 1), ← rd_truncation, euler_pentagonal,
    PowerSeries.coeff_map, PowerSeries.coeff_map,
    coeff_pentSeries_lt (M := pentCount + (i + 1)) (by omega), map_evm1_pentFiniteP]

theorem pent_rep {P : ℕ} (h : pentFold pentCount = some P) : Rep N 22 P (rd qfacInf) :=
  (pentFold_rep _ h).congr fun i hi => (coeff_rd_qfacInf i hi).symm

lemma invert_rep {u b : ℕ} {v : PowerSeries R} (hu : Rep N 22 u f) (hfv : f * v = 1)
    (h : invert u = some b) : Rep N 22 b v := by
  unfold invert at h
  split_ifs at h with hok
  obtain rfl : inverse u = b := Option.some.inj h
  exact Rep.inv_of_ok hQ (by norm_num) hu hfv hN (by norm_num) hok

lemma rd_qfac_mul_pgf : rd qfacInf * rd partitionGF = 1 := by
  rw [← map_mul, BoylanWebb.qfac_mul_pgf, map_one]

/-! ### Lane maps -/

lemma thetaLane_lt (i v : ℕ) : thetaLane i v < 2 ^ 22 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

lemma rep_theta {a : ℕ} (ha : Rep N 22 a f) : Rep N 22 (mapQ thetaLane a) (Igusa.theta f) :=
  ha.laneMap thetaLane hN (by norm_num) (fun i v _ => thetaLane_lt i v) fun i hi v hv => by
    rw [Igusa.coeff_theta, ← hv, thetaLane, ZMod.natCast_mod]
    push_cast
    ring

/-- The denominator series `1 + 4 p S`. -/
noncomputable def sigmaPart : PowerSeries R :=
  PowerSeries.C ((4 * 607 : ℕ) : R) * sigmaSeriesSquare 607

lemma sigmaLane_lt (i v : ℕ) : sigmaLane i v < 2 ^ 22 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

lemma coeff_E2_pos {i : ℕ} (hi : 0 < i) :
    PowerSeries.coeff i (Igusa.E2 R) = -24 * (ArithmeticFunction.sigma 1 i : R) := by
  rw [Igusa.E2, PowerSeries.coeff_map, Igusa.e2Z, map_sub, PowerSeries.coeff_one, if_neg hi.ne',
    show (24 : PowerSeries ℤ) = PowerSeries.C (24 : ℤ) by simp, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk]
  simp

/-- The arithmetic heart of the denominator. -/
theorem sigmaLane_cast {i v : ℕ} (hi : i < N) (hv : (v : R) = PowerSeries.coeff i (Igusa.E2 R)) :
    (sigmaLane i v : R) = PowerSeries.coeff i sigmaPart := by
  have hcoeff : PowerSeries.coeff i sigmaPart =
      ((4 * 607 : ℕ) : R) * (ArithmeticFunction.sigma (607 - 2) i : R) := by
    rw [sigmaPart, PowerSeries.coeff_C_mul, sigmaSeriesSquare, PowerSeries.coeff_mk]
  rw [hcoeff]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [sigmaLane, p]
  · let m : ℕ := if i % p = 0 then i / p else i
    let y : ℕ := (v * cInv * m ^ (p - 2)) % p
    have hy : sigmaLane i v = 4 * 607 * y % Q := rfl
    have hlt : i < 607 ^ 2 := lt_trans hi (by norm_num)
    have hsig := sigma_pred_eq (p := 607) (by norm_num) hpos hlt
    have hv' : (v : ZMod 607) = -24 * (ArithmeticFunction.sigma 1 i : ZMod 607) := by
      have h := hv
      rw [coeff_E2_pos hpos] at h
      have hdvd : (607 : ℕ) ∣ Q := by norm_num
      have hm := congrArg (ZMod.castHom hdvd (ZMod 607)) h
      simpa using hm
    have hyc : (y : ZMod 607) = (ArithmeticFunction.sigma (607 - 2) i : ZMod 607) := by
      have hunit : (-24 * (177 : ZMod 607)) = 1 := by decide +kernel
      have hmd : ((m : ℕ) : ZMod 607) = ((if i % 607 = 0 then i / 607 else i : ℕ) : ZMod 607) := rfl
      rw [hsig, ← hmd]
      simp only [y, ZMod.natCast_mod, p, cInv]
      push_cast
      rw [hv']
      linear_combination
        ((ArithmeticFunction.sigma 1 i : ZMod 607) * (m : ZMod 607) ^ (607 - 2)) * hunit
    have hmod : y ≡ ArithmeticFunction.sigma (607 - 2) i [MOD 607] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hyc
    have hmod2 : 607 * y ≡ 607 * ArithmeticFunction.sigma (607 - 2) i [MOD 607 * 607] :=
      Nat.ModEq.mul_left' 607 hmod
    have hcast : ((607 * y : ℕ) : R) = ((607 * ArithmeticFunction.sigma (607 - 2) i : ℕ) : R) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod2
    rw [hy, ZMod.natCast_mod]
    push_cast at hcast ⊢
    linear_combination 4 * hcast

lemma rep_sigmaPart {a : ℕ} (ha : Rep N 22 a (Igusa.E2 R)) :
    Rep N 22 (mapQ sigmaLane a) sigmaPart :=
  ha.laneMap sigmaLane hN (by norm_num) (fun i v _ => sigmaLane_lt i v)
    fun i hi v hv => sigmaLane_cast hi hv

/-! ### Powers -/

lemma powQ_rep {a : ℕ} (ha : Rep N 22 a f) (n : ℕ) {r : ℕ} (h : powQ a n = some r) :
    Rep N 22 r (f ^ n) := by
  induction n generalizing r with
  | zero =>
    obtain rfl : 1 = r := Option.some.inj h
    simpa using rep_one
  | succ n ih =>
    obtain ⟨b, h0, h1⟩ := bind_some h
    rw [pow_succ]
    exact rmul (ih h0) ha h1

/-! ### Φ -/

theorem phi_rep {a : ℕ} (ha : Rep N 22 a (rd partitionGF)) :
    Rep N 22 (shiftR N delta a) (rd (BoylanWebb.Φ 607)) := by
  have h0 : Rep N 22 (shiftR N delta a) (X ^ delta * rd partitionGF) :=
    Rep.shiftR ha (by norm_num)
  refine h0.congr fun i hi => ?_
  have hδ : BoylanWebb.δ 607 = delta := by norm_num [BoylanWebb.δ, delta]
  let E := RankProof.Ea (607 ^ 2) (TauCong.ppow_ne 607 2) qfacInf
  have hdvd : (X : PowerSeries R) ^ N ∣ rd E - 1 := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun k hk => ?_
    rw [map_sub, PowerSeries.coeff_map, RankProof.coeff_Ea, PowerSeries.coeff_one]
    have hk2 : k < 607 ^ 2 := lt_trans hk (by norm_num)
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · rw [if_neg (fun h => absurd (Nat.le_of_dvd hpos h) (by omega)), if_neg hpos.ne']
      simp
  have hexp : rd (BoylanWebb.Φ 607) = X ^ delta * rd partitionGF +
      (rd E - 1) * (X ^ delta * rd partitionGF) := by
    rw [BoylanWebb.Φ, map_mul, map_mul, map_pow, PowerSeries.map_X, hδ]
    ring
  rw [hexp, map_add]
  have hz : PowerSeries.coeff i ((rd E - 1) * (X ^ delta * rd partitionGF)) = 0 :=
    PowerSeries.X_pow_dvd_iff.mp (Dvd.dvd.mul_right hdvd _) i hi
  rw [hz, add_zero]

/-! ### Algebra over a generic ring

Stated generically so that `ring` never has to unfold `ZMod (607^2)`. -/

lemma alg_pow24 {S : Type*} [CommRing S] (f : S) :
    f * f * f * (f * f * f) * (f * f * f * (f * f * f)) *
      (f * f * f * (f * f * f) * (f * f * f * (f * f * f))) = f ^ 24 := by ring

lemma alg_cube {S : Type*} [CommRing S] (f : S) : f * (f * f) = f ^ 3 := by ring

lemma alg_E4 {S : Type*} [CommRing S] (a b : S) : a * a + b * (-12) = a ^ 2 - 12 * b := by ring

/-! ### The prelude -/

/-- What `prelude` certifies. -/
structure PreludeSpec (pr : Prelude) : Prop where
  pgf : Rep N 22 pr.pgf (rd partitionGF)
  e4 : Rep N 22 pr.e4 (ModP.E4 R)
  b0 : Rep N 22 pr.b0 ((ModP.E4 R ^ 3) ^ 101 * (1 + sigmaPart))
  g : ∃ v : PowerSeries R, ModP.E4 R ^ 3 * v = 1 ∧ Rep N 22 pr.g (ModP.Dq R * v)

/-- `E₄³` is a unit. -/
lemma exists_E4_cube_inv : ∃ v : PowerSeries R, ModP.E4 R ^ 3 * v = 1 := by
  have hu : IsUnit (ModP.E4 R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ModP.constantCoeff_E4]
    exact isUnit_one
  obtain ⟨w, hw⟩ := (hu.pow 3).exists_right_inv
  exact ⟨w, hw⟩

theorem prelude_spec {pr : Prelude} (h : prelude = some pr) : PreludeSpec pr := by
  unfold prelude at h
  obtain ⟨P, hP, h⟩ := bind_some h
  obtain ⟨Pi, hPi, h⟩ := bind_some h
  obtain ⟨P2, hP2, h⟩ := bind_some h
  obtain ⟨P3, hP3, h⟩ := bind_some h
  obtain ⟨P6, hP6, h⟩ := bind_some h
  obtain ⟨P12, hP12, h⟩ := bind_some h
  obtain ⟨Wa, hW, h⟩ := bind_some h
  obtain ⟨Pi2, hPi2, h⟩ := bind_some h
  obtain ⟨Pi3, hPi3, h⟩ := bind_some h
  obtain ⟨Pi6, hPi6, h⟩ := bind_some h
  obtain ⟨Pi12, hPi12, h⟩ := bind_some h
  obtain ⟨Wi, hWi, h⟩ := bind_some h
  obtain ⟨e2a, he2a, h⟩ := bind_some h
  obtain ⟨E2a, hE2, h⟩ := bind_some h
  obtain ⟨sq, hsq, h⟩ := bind_some h
  obtain ⟨sc, hsc, h⟩ := bind_some h
  obtain ⟨E4a, hE4, h⟩ := bind_some h
  obtain ⟨Eis, hEis, h⟩ := bind_some h
  obtain ⟨E4s, hE4s, h⟩ := bind_some h
  obtain ⟨E4c, hE4c, h⟩ := bind_some h
  obtain ⟨E303, hE303, h⟩ := bind_some h
  obtain ⟨E4ci, hE4ci, h⟩ := bind_some h
  obtain ⟨ga, hg, h⟩ := bind_some h
  obtain ⟨B0, hB0, h⟩ := bind_some h
  obtain rfl : (⟨Pi, E4a, B0, ga⟩ : Prelude) = pr := Option.some.inj h
  -- `(q;q)` and its inverse.
  have rP := pent_rep hP
  have rPi := invert_rep rP rd_qfac_mul_pgf hPi
  -- `W = (q;q)²⁴` and its inverse.
  have rW : Rep N 22 Wa (W R) := by
    have h3 := rmul (rmul rP rP hP2) rP hP3
    have h6 := rmul h3 h3 hP6
    have h24 := rmul (rmul h6 h6 hP12) (rmul h6 h6 hP12) hW
    rw [alg_pow24] at h24
    rwa [W, map_pow]
  have rWi : Rep N 22 Wi (rd partitionGF ^ 24) := by
    have h3 := rmul (rmul rPi rPi hPi2) rPi hPi3
    have h6 := rmul h3 h3 hPi6
    have h24 := rmul (rmul h6 h6 hPi12) (rmul h6 h6 hPi12) hWi
    rwa [alg_pow24] at h24
  have hWinv : W R * rd partitionGF ^ 24 = 1 := by
    rw [W, map_pow, ← mul_pow, rd_qfac_mul_pgf, one_pow]
  -- `E₂` and `E₄`, from the discriminant alone.
  have rE2 : Rep N 22 E2a (Igusa.E2 R) := by
    have h := radd (rmul (rep_theta rW) rWi he2a) rep_one hE2
    rwa [← E2_eq_of_inv R hWinv] at h
  have rE4 : Rep N 22 E4a (ModP.E4 R) := by
    have hc := rep_nat (c := Q - 12) (by norm_num)
    have h12 : PowerSeries.C (((Q - 12 : ℕ)) : R) = -12 := by
      have hcast : ((Q - 12 : ℕ) : R) = -12 := by
        rw [Nat.cast_sub (by norm_num), ZMod.natCast_self, zero_sub]
        norm_num
      rw [hcast, map_neg]
      congr 1
    rw [h12] at hc
    have h := radd (rmul rE2 rE2 hsq) (rmul (rep_theta rE2) hc hsc) hE4
    rwa [alg_E4, ← E4_eq] at h
  have rEis : Rep N 22 Eis (1 + sigmaPart) := radd rep_one (rep_sigmaPart rE2) hEis
  have rE4c : Rep N 22 E4c (ModP.E4 R ^ 3) := by
    have h := rmul rE4 (rmul rE4 rE4 hE4s) hE4c
    rwa [alg_cube] at h
  have rE303 := powQ_rep rE4c 101 hE303
  obtain ⟨v, hv⟩ := exists_E4_cube_inv
  have rv := invert_rep rE4c hv hE4ci
  have rD : Rep N 22 (shiftR N 1 Wa) (ModP.Dq R) := by
    have h := Rep.shiftR (d := 1) rW (by norm_num : 22 ≤ 64)
    rwa [pow_one, ← Dq_eq] at h
  exact ⟨rPi, rE4, rmul rE303 rEis hB0, v, hv, rmul rD rv hg⟩

end RamanujanTau.FiniteArithmetic.Rank607Series
