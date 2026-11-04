import RamanujanTau.AtkinSporadic.EigenLift
import RamanujanTau.AtkinSporadic.DimOneData

/-!
# `EtaHeckeMod ℓ Q (ℓ−1) ℓ`, unconditionally, for ℓ = 13, 17, 19, 23 and every prime `Q ≥ 5`

From the characteristic-zero relation `a(1)·T(Q²)(a·P^ℓ) = ν·(a·P^ℓ)` (`EigenLift.eigen_char0`):
if `a(1) ≢ 0 (mod ℓ)` divide by `a(1)` modulo `ℓ`; otherwise `a ≡ 0 (mod ℓ)` by Sturm's bound
(`S_{ℓ−1}` has Sturm bound 2), and both sides vanish.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.EigenLift
open PowerSeries BoylanWebb
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open MockTheta5.JTP (partitionGF)
open DimOne

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma map_castInt_partitionGF : PowerSeries.map (Int.castRingHom ℤ) partitionGF = partitionGF := by
  ext n; simp

lemma heckeHalf_zero {R : Type*} [CommRing R] (Q : ℕ) [Fact Q.Prime] (j lam : ℕ) (s : ℤ) :
    heckeHalf (R := R) Q j lam s 0 = 0 := by
  ext N; simp [coeff_heckeHalf]

/-- **`EtaHeckeMod` from the dimension-one property.** -/
theorem etaHeckeMod_of_dimOne (h13 : 13 ≤ ℓ) (h24 : ℓ < 24) {Q : ℕ} [hQ : Fact Q.Prime]
    (hQ5 : 5 ≤ Q) (D : DimOneProp ℓ) : EtaHeckeMod ℓ Q (ℓ - 1) ℓ := by
  intro a ha ha0
  have hjj : jj ℓ = ℓ := Nat.mod_eq_of_lt h24
  have hodd : ℓ % 2 = 1 := (prime_ge h13).1
  have hw : ℓ - 1 - (ℓ + 1) / 2 = halfWt ℓ := by unfold halfWt; omega
  rw [hw]
  have hk : kPrime ℓ = ((ℓ - 1 : ℕ) : ℤ) := by
    unfold kPrime; rw [hjj]; congr 1; omega
  have hcoord : a * partitionGF ^ ℓ = coordOf ℓ a := by
    rw [coordOf, map_castInt_partitionGF, hjj]
  have ha0' : a.coeff 0 = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact ha0
  -- `a` lies in the integral cusp-form lattice
  have hL : a ∈ intLattice ℓ := by
    obtain ⟨F, hF⟩ := ha.cast hk.symm
    have hF0 : (UpperHalfPlane.qExpansion 1 F).coeff 0 = 0 := by
      rw [hF, PowerSeries.coeff_map, ha0', map_zero]
    exact ⟨ModularForm.toCuspForm F hF0, hF.symm⟩
  set T := heckeHalf (R := ZMod ℓ) Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) with hT
  by_cases h1 : ((a.coeff 1 : ℤ) : ZMod ℓ) = 0
  · -- `a ≡ 0 (mod ℓ)`
    have hΨ : Ψ ℓ a = 0 := by
      apply sturm ℓ 2 ((ℓ - 1 : ℕ) : ℤ) (by push_cast; omega) a ha
      rw [show ((ℓ - 1 : ℕ) : ℤ).toNat / 12 + 1 = 2 by rw [Int.toNat_natCast]; omega,
        X_pow_dvd_iff]
      intro n hn
      interval_cases n
      · rw [coeff_map, ha0', map_zero]
      · rw [coeff_map]; exact h1
    refine ⟨PowerSeries.C 0 * a, IntForm.C_mul 0 ha, by simp, ?_⟩
    rw [map_mul, hΨ, zero_mul, map_mul, map_mul, map_C, map_zero, map_zero, zero_mul, zero_mul,
      hT, heckeHalf_zero]
  · -- divide by `a(1)` modulo `ℓ`
    have hα : (coordOf ℓ a).coeff 1 ≠ 0 := by
      rw [coeff_one_coordOf a ha0']
      intro h; apply h1; rw [h, Int.cast_zero]
    obtain ⟨ν, hν⟩ := eigen_char0 h13 h24 hQ5 D hL hα
    rw [coeff_one_coordOf a ha0'] at hν
    have hmap := congrArg (PowerSeries.map (Int.castRingHom (ZMod ℓ))) hν
    rw [map_int_smul, map_int_smul, map_heckeHalf] at hmap
    set u : ZMod ℓ := ((a.coeff 1 : ℤ) : ZMod ℓ) with hu
    set m : ℤ := ((u⁻¹ * (ν : ZMod ℓ)).val : ℤ) with hm
    have hmc : ((m : ℤ) : ZMod ℓ) = u⁻¹ * (ν : ZMod ℓ) := by
      rw [hm, Int.cast_natCast, ZMod.natCast_zmod_val]
    refine ⟨PowerSeries.C m * a, IntForm.C_mul m ha, by simp [ha0], ?_⟩
    rw [hcoord, mul_assoc, ← hcoord, hcoord, map_mul, map_C]
    have hu0 : u ≠ 0 := h1
    have e1 : T (Ψ ℓ (coordOf ℓ a)) = u⁻¹ • (u • T (Ψ ℓ (coordOf ℓ a))) := by
      rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
    rw [e1]
    have e2 : u • T (Ψ ℓ (coordOf ℓ a)) = (ν : ZMod ℓ) • Ψ ℓ (coordOf ℓ a) := by
      simpa [hT] using hmap
    rw [e2, smul_smul, smul_eq_C_mul, ← hmc]
    simp

/-! ### The four primes -/

theorem etaHeckeMod_13 {Q : ℕ} [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 13 Q (13 - 1) 13 :=
  etaHeckeMod_of_dimOne (by norm_num) (by norm_num) hQ5 dimOne_13

theorem etaHeckeMod_17 {Q : ℕ} [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 17 Q (17 - 1) 17 :=
  etaHeckeMod_of_dimOne (by norm_num) (by norm_num) hQ5 dimOne_17

theorem etaHeckeMod_19 {Q : ℕ} [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 19 Q (19 - 1) 19 :=
  etaHeckeMod_of_dimOne (by norm_num) (by norm_num) hQ5 dimOne_19

theorem etaHeckeMod_23 {Q : ℕ} [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 23 Q (23 - 1) 23 :=
  etaHeckeMod_of_dimOne (by norm_num) (by norm_num) hQ5 dimOne_23

end RamanujanTau.AtkinSporadic.EigenLift
