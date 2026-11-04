import RamanujanTau.HalfHecke.Main
import RamanujanTau.HalfHecke.GaussSign

/-!
# `EtaHecke Q k 1`, unconditionally, for `Q = 11, 37`

`etaHecke_of_sign`: for a prime `Q ≥ 5` and an even weight `k ≥ 2`, if the Gauss sum has the sign
`cMd k Q · gQ Q = s·Q^{k−2}` (`s = heckeSign Q (k−1)`), then `T(Q²)` maps `η^{−1} S_k(SL₂ℤ)` (integral)
into itself: the hypothesis `AtkinSporadic.EtaHecke Q k 1`. The sign condition is the classical
evaluation of the quadratic Gauss sum (`gQ_11`, `gQ_37`), checked here for `Q = 11, 37`, `k = 168`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex ModularForm Finset PowerSeries
open UpperHalfPlane hiding I
open RamanujanTau.ThetaLift RamanujanTau.AtkinSporadic
open MockTheta5.JTP (qfacInf partitionGF)
open scoped Real MatrixGroups

noncomputable section

/-- The sign condition on the Gauss sum. -/
def GaussSign (Q : ℕ) [Fact Q.Prime] (k : ℕ) : Prop :=
  cMd (k : ℤ) Q * gQ Q = ((heckeSign Q (k - 1) * (Q : ℤ) ^ (k - 2) : ℤ) : ℂ)

lemma hshift_one (Q : ℕ) : hshift Q 1 = dQ Q := by simp [hshift, dQ]

/-- **`T(Q²)` preserves `η^{−1} S_k`** (given the Gauss-sum sign). -/
theorem etaHecke_of_sign (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q) (k : ℕ) (hk : 2 ≤ k)
    (hs : GaussSign Q k) : EtaHecke Q k 1 := by
  intro a ha ha0
  obtain ⟨F, hF⟩ := ha
  have ha0' : a.coeff 0 = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact ha0
  have hF0 : (qExpansion 1 F).coeff 0 = 0 := by rw [hF, PowerSeries.coeff_map, ha0', map_zero]
  set G : CuspForm 𝒮ℒ (k : ℤ) := ModularForm.toCuspForm F hF0
  have hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G := hF.symm
  have hcA : ∀ n, cA G 1 n = (((a * partitionGF).coeff n : ℤ) : ℂ) := by
    intro n
    have := qExp_hP G 1 hG
    rw [cA, this, pow_one, PowerSeries.coeff_map]; rfl
  have hc0 : cA G 1 0 = 0 := by
    rw [hcA, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, ha0, zero_mul, Int.cast_zero]
  rw [show k - (1 + 1) / 2 = k - 1 by norm_num, pow_one]
  set T := heckeHalf Q 1 (k - 1) (heckeSign Q (k - 1)) (a * partitionGF) with hT
  -- the coefficients agree
  have hB : PowerSeries.mk (Bc G Q (cMd (k : ℤ) Q)) = PowerSeries.map (Int.castRingHom ℂ) T := by
    ext N
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, hT, coeff_heckeHalf, hshift_one]
    unfold Bc
    rw [hs, chiQ_intCast]; simp only [hcA]
    have hpow : (Q : ℂ) ^ (2 * (k : ℤ) - 3) = ((Q : ℤ) ^ (2 * (k - 1) - 1) : ℤ) := by
      have : 2 * (k : ℤ) - 3 = ((2 * (k - 1) - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (k - 1)), Nat.cast_sub (by omega : 1 ≤ k)]; ring
      rw [this, zpow_natCast]; push_cast; rfl
    rw [hpow]
    have hk2 : k - 2 = k - 1 - 1 := by omega
    rw [hk2]
    simp only [eq_intCast, map_add, map_mul, apply_ite (Int.castRingHom ℂ), map_zero, map_intCast]
    push_cast
    ring
  set a' : PowerSeries ℤ := qfacInf * T
  have hqP : qfacInf * partitionGF = 1 := by
    rw [partitionGF]; exact Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf
  refine ⟨a', ⟨Hform G hQ5 hc0, ?_⟩, ?_, ?_⟩
  · rw [qExp_Hform, hB, ← map_mul]
  · -- constant term
    simp only [a', map_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (φ := T), hT, coeff_heckeHalf, hshift_one]
    have hd0 := dQ_pos hQ5
    have hdl := dQ_lt hQ5
    rw [if_neg (by simp; omega), if_neg (by simpa using Nat.not_dvd_of_pos_of_lt hd0 hdl)]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, ha0]; simp
  · simp only [a']; rw [mul_comm qfacInf, mul_assoc, hqP, mul_one]

/-! ### The two primes -/

lemma e24_six : e24 6 = I := by
  rw [e24, show (2 * π * I * ((6 : ℤ) : ℂ) / 24 : ℂ) = π / 2 * I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

theorem gaussSign_11 : GaussSign 11 168 := by
  unfold GaussSign cMd
  have h1 : chiQ 11 (-24) = 1 := by
    rw [chiQ_apply, show quadraticChar (ZMod 11) (-24) = 1 by decide]; norm_num
  have h2 : e24 (3 * ((11 : ℕ) : ℤ) - 3) = I := by
    rw [← e24_six]; apply e24_eq_of_dvd; norm_num
  have h3 : heckeSign 11 (168 - 1) = -1 := by
    rw [heckeSign, legendreSym_val 11 (by norm_num), legendreSym_val 11 (by norm_num)]; decide
  have hs : ((Real.sqrt 11 : ℝ) : ℂ) * ((Real.sqrt 11 : ℝ) : ℂ) = 11 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [h1, h2, h3, gQ_11]
  have hz : ((11 : ℕ) : ℂ) ^ (((168 : ℕ) : ℤ) - 3) = (11 : ℂ) ^ 165 := by
    rw [show (((168 : ℕ) : ℤ) - 3) = ((165 : ℕ) : ℤ) by norm_num, zpow_natCast]; norm_num
  rw [hz]
  push_cast
  linear_combination ((11 : ℂ) ^ 165 * I ^ 2) * hs + (11 : ℂ) ^ 166 * I_sq

theorem gaussSign_37 : GaussSign 37 168 := by
  unfold GaussSign cMd
  have h1 : chiQ 37 (-24) = -1 := by
    rw [chiQ_apply, show quadraticChar (ZMod 37) (-24) = -1 by decide]; norm_num
  have h2 : e24 (3 * ((37 : ℕ) : ℤ) - 3) = -1 := by
    rw [← e24_twelve]; apply e24_eq_of_dvd; norm_num
  have h3 : heckeSign 37 (168 - 1) = 1 := by
    rw [heckeSign, legendreSym_val 37 (by norm_num), legendreSym_val 37 (by norm_num)]; decide
  have hs : ((Real.sqrt 37 : ℝ) : ℂ) * ((Real.sqrt 37 : ℝ) : ℂ) = 37 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [h1, h2, h3, gQ_37]
  have hz : ((37 : ℕ) : ℂ) ^ (((168 : ℕ) : ℤ) - 3) = (37 : ℂ) ^ 165 := by
    rw [show (((168 : ℕ) : ℤ) - 3) = ((165 : ℕ) : ℤ) by norm_num, zpow_natCast]; norm_num
  rw [hz]
  push_cast
  linear_combination ((37 : ℂ) ^ 165) * hs

/-- **`EtaHecke 11 168 1`**, unconditionally. -/
theorem etaHecke_11_168 : EtaHecke 11 168 1 :=
  etaHecke_of_sign 11 (by norm_num) 168 (by norm_num) gaussSign_11

/-- **`EtaHecke 37 168 1`**, unconditionally. -/
theorem etaHecke_37_168 : EtaHecke 37 168 1 :=
  etaHecke_of_sign 37 (by norm_num) 168 (by norm_num) gaussSign_37

theorem etaHeckeMod_13_11 : EtaHeckeMod 13 11 168 1 := etaHecke_11_168.toMod 13
theorem etaHeckeMod_13_37 : EtaHeckeMod 13 37 168 1 := etaHecke_37_168.toMod 13

end

end RamanujanTau.HalfHecke
