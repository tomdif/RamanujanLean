import RamanujanTau.AtkinSporadic.Atkin13
import RamanujanTau.BoylanWebb.Assemble

/-!
# Ono–Weaver congruences `p((ℓQ³n+1)/24) ≡ 0 (mod ℓ)`, conditional on `EtaHecke`

For `13 ≤ ℓ ≤ 23` the Boylan–Webb certificates (`BoylanWebb.CertX.eigen`) give, unconditionally,
`U_ℓ(Δ^δ) ≡ c·f (mod ℓ)` with `f ∈ S_{ℓ−1}(SL₂(ℤ))` the normalized cusp form. With
`L_eq_partition` this is (`Pser_eq`)

  `Σ_m p(ℓm − δ) qᵐ ≡ c · f · P^ℓ (mod ℓ)`,   `P = Σ p(n) qⁿ`,

i.e. `Σ p((ℓm+1)/24) q^{m/24} ≡ c·f/η^ℓ`, a cusp form of weight `(ℓ−2)/2` with multiplier `ν_η^{−ℓ}`.

`weaver_index`: **if** `T(Q²)` preserves `η^{−ℓ}S_{ℓ−1}` (`EtaHecke Q (ℓ−1) ℓ`) and a kernel check
shows the `q¹` coefficient of `T(Q²)(Σ p(ℓm−δ)qᵐ)` vanishes mod `ℓ` (Sturm bound 2 in weight `ℓ−1`),
then `T(Q²)` kills the series mod `ℓ`, and `ℓ ∣ p(ℓ(Q²N − d) − δ)` whenever `Q ∣ 24N − ℓ` and
`Q² ∤ 24N − ℓ`. This is Ono's `p((ℓQ³n+1)/24) ≡ 0 (mod ℓ)` for `Q ∤ n`.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Weaver
open PowerSeries BoylanWebb RamanujanTau.FiniteArithmetic
open MockTheta5.JTP (qfacInf partitionGF)
open Atkin13 (legC)

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `λ = (ℓ − 1) − (ℓ + 1)/2`, so the weight of `f/η^ℓ` is `λ + 1/2`. -/
def wlam : ℕ := (ℓ - 1) - (ℓ + 1) / 2

/-- Coefficient `i` of `Σ p(ℓm − δ) qᵐ` from a packed prefix of `P mod ℓ`. -/
def Gv (B i : ℕ) : ZMod ℓ := if δ ℓ ≤ ℓ * i then (Packed.lane B (ℓ * i - δ ℓ) : ZMod ℓ) else 0

/-- The `q¹` coefficient of `T(Q²) Σ p(ℓm − δ) qᵐ`. -/
def Wco (Q B : ℕ) : ZMod ℓ :=
  (if hshift Q ℓ ≤ Q ^ 2 * 1 then Gv ℓ B (Q ^ 2 * 1 - hshift Q ℓ) else 0)
  + ((legC Q 12 * legC Q ((-1) ^ wlam ℓ) * legC Q (24 * 1 - ℓ) * (Q : ℤ) ^ (wlam ℓ - 1) : ℤ) :
      ZMod ℓ) * Gv ℓ B 1
  + (if Q ^ 2 ∣ 1 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
      Gv ℓ B ((1 + hshift Q ℓ) / Q ^ 2) else 0)

/-- The kernel certificate. -/
def wchk (Q Npre J : ℕ) : Bool :=
  match PartitionPrefix.pgfPrefix ℓ Npre J with
  | some B => decide (Wco ℓ Q B = 0)
  | none => false

lemma eB_one (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) : eB ℓ 1 = δ ℓ := by
  have h := ek_mul ℓ h24 1
  rw [eB, show (1 + 1) / 2 = 1 by norm_num]
  have : ((ℓ : ℤ) ^ (2 * 1)) = 24 * (δ ℓ : ℤ) + 1 := by
    rw [mul_one]; exact_mod_cast h24.symm
  linarith

lemma coeff_Pser1 (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (i : ℕ) :
    coeff i (Pser ℓ 1) = if δ ℓ ≤ ℓ * i then coeff (ℓ * i - δ ℓ) partitionGF else 0 := by
  rw [Pser, coeff_mk, eB_one ℓ h24, pZ, pow_one]
  split_ifs with h1 h2 h2
  · exfalso; push_cast at h1; omega
  · rfl
  · have e : ((ℓ : ℤ) * (i : ℤ) - (δ ℓ : ℤ)) = ((ℓ * i - δ ℓ : ℕ) : ℤ) := by
      rw [Nat.cast_sub h2]; push_cast; ring
    rw [e, Int.toNat_natCast]
  · exfalso; push_cast at h1; omega

/-- **`Σ p(ℓm − δ) qᵐ ≡ c·f·P^ℓ (mod ℓ)`** from `U(Δ^δ) ≡ c f`. -/
theorem Pser_eq (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (f : PowerSeries ℤ) (c : ZMod ℓ)
    (heig : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = PowerSeries.C c * Ψ ℓ f) :
    Ψ ℓ (Pser ℓ 1) = PowerSeries.C c * Ψ ℓ (f * partitionGF ^ ℓ) := by
  have hL1 : Ψ ℓ (L ℓ 1) = PowerSeries.C c * Ψ ℓ f := by
    rw [L_succ, Ψ_T_even ℓ h24 0 ⟨0, rfl⟩, show L ℓ 0 = 1 from rfl, map_one, mul_one, heig]
  have hLP := (L_eq_partition ℓ h24 0).2
  rw [show 2 * 0 + 1 = 1 by norm_num] at hLP
  have hF := TauCong.frob_qfacInf ℓ 1
  simp only [pow_one] at hF
  have hF' : Ψ ℓ (RankProof.Ea ℓ (hℓ0 ℓ) qfacInf) = (Ψ ℓ qfacInf) ^ ℓ := hF.symm
  have hEP : Ψ ℓ qfacInf * Ψ ℓ partitionGF = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
  rw [hLP, map_mul] at hL1
  rw [hF'] at hL1
  calc Ψ ℓ (Pser ℓ 1) = ((Ψ ℓ qfacInf) ^ ℓ * Ψ ℓ (Pser ℓ 1)) * (Ψ ℓ partitionGF) ^ ℓ := by
        rw [mul_comm ((Ψ ℓ qfacInf) ^ ℓ), mul_assoc, ← mul_pow, hEP, one_pow, mul_one]
    _ = PowerSeries.C c * Ψ ℓ (f * partitionGF ^ ℓ) := by
        rw [hL1, map_mul, map_pow]; ring

/-- **Ono–Weaver vanishing**, given `EtaHecke Q (ℓ−1) ℓ` and the `q¹` certificate. -/
theorem weaver_index (Q : ℕ) [Fact Q.Prime] (hQ3 : 3 ≤ Q) (hℓ13 : 13 ≤ ℓ) (hℓ23 : ℓ ≤ 23)
    (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (hd : 24 * hshift Q ℓ = (Q ^ 2 - 1) * ℓ)
    (hdQ : hshift Q ℓ < Q ^ 2)
    (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : constantCoeff f = 0)
    (c : ZMod ℓ) (hc : c ≠ 0) (heig : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = PowerSeries.C c * Ψ ℓ f)
    (Npre J : ℕ) (hN0 : 0 < Npre) (hN : Npre ≤ 2 ^ 16) (hJ : Npre ≤ PartitionPrefix.pentLow J)
    (hcov1 : ℓ * (Q ^ 2 * 1 - hshift Q ℓ) - δ ℓ < Npre) (hcov2 : ℓ * 1 - δ ℓ < Npre)
    (hcov3 : ℓ * ((1 + hshift Q ℓ) / Q ^ 2) - δ ℓ < Npre)
    (hok : wchk ℓ Q Npre J = true) (H : EtaHeckeMod ℓ Q (ℓ - 1) ℓ)
    (N : ℕ) (hNℓ : ℓ ≤ 24 * N) (hQ : (Q : ℤ) ∣ 24 * N - ℓ) (hQ2 : ¬ (Q : ℤ) ^ 2 ∣ 24 * N - ℓ) :
    ℓ ∣ Fintype.card (Nat.Partition (ℓ * (Q ^ 2 * N - hshift Q ℓ) - δ ℓ)) := by
  set G := Ψ ℓ (f * partitionGF ^ ℓ) with hGdef
  have hPs := Pser_eq ℓ h24 f c heig
  obtain ⟨f', hf', hf'0, hT⟩ := H f hf hf0
  set E : PowerSeries (ZMod ℓ) := Ψ ℓ qfacInf
  have hEP : E * Ψ ℓ partitionGF = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
  set T := heckeHalf (R := ZMod ℓ) Q ℓ (wlam ℓ) (heckeSign Q (wlam ℓ))
  have hTG : T G = Ψ ℓ (f' * partitionGF ^ ℓ) := by
    exact hT
  have hTP : T (Ψ ℓ (Pser ℓ 1)) = PowerSeries.C c * T G := by
    rw [hPs]; exact heckeHalf_C_mul _ _ _ _ _ _
  -- the certificate
  unfold wchk at hok
  cases hB : PartitionPrefix.pgfPrefix ℓ Npre J with
  | none => rw [hB] at hok; exact absurd hok (by simp)
  | some B =>
  rw [hB] at hok
  have hW : Wco ℓ Q B = 0 := by simpa using hok
  have hℓ21 : ℓ ≤ 2 ^ 21 := by omega
  have hcp := PartitionPrefix.coeff_pgf (by omega) hℓ21 hN0 hN hJ hB
  have hG : ∀ i, ℓ * i - δ ℓ < Npre → coeff i (Ψ ℓ (Pser ℓ 1)) = Gv ℓ B i := by
    intro i hi
    rw [coeff_map, coeff_Pser1 ℓ h24, Gv]
    split_ifs
    · rw [eq_intCast]; exact hcp _ hi
    · simp
  -- `q¹` coefficient of `T(Ψ Pser)` vanishes
  have h1 : coeff 1 (T (Ψ ℓ (Pser ℓ 1))) = 0 := by
    rw [← hW, coeff_heckeHalf, Wco, heckeSign, legendreSym_val Q hQ3 12,
      legendreSym_val Q hQ3 ((-1) ^ wlam ℓ), Nat.cast_one,
      legendreSym_val Q hQ3 (24 * 1 - (ℓ : ℤ)), hG 1 hcov2]
    have e1 : (if hshift Q ℓ ≤ Q ^ 2 * 1 then coeff (Q ^ 2 * 1 - hshift Q ℓ) (Ψ ℓ (Pser ℓ 1)) else 0) =
        (if hshift Q ℓ ≤ Q ^ 2 * 1 then Gv ℓ B (Q ^ 2 * 1 - hshift Q ℓ) else 0) := by
      split_ifs
      · exact hG _ hcov1
      · rfl
    have e3 : (if Q ^ 2 ∣ 1 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
          coeff ((1 + hshift Q ℓ) / Q ^ 2) (Ψ ℓ (Pser ℓ 1)) else 0) =
        (if Q ^ 2 ∣ 1 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
          Gv ℓ B ((1 + hshift Q ℓ) / Q ^ 2) else 0) := by
      split_ifs
      · rw [hG _ hcov3]
      · rfl
    rw [e1, e3]
    simp only [legC]
  -- hence `T G ≡ 0`
  have hTG0 : T G = 0 := by
    have h1' : coeff 1 (T G) = 0 := by
      have := h1
      rw [hTP, coeff_C_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hc
    have hX : (X : PowerSeries (ZMod ℓ)) ^ 2 ∣ Ψ ℓ (f' * partitionGF ^ ℓ) := by
      rw [X_pow_dvd_iff]
      intro n hn
      interval_cases n
      · rw [coeff_map, coeff_zero_eq_constantCoeff_apply, map_mul, hf'0, zero_mul, map_zero]
      · rw [← hTG]; exact h1'
    have hXf : (X : PowerSeries (ZMod ℓ)) ^ (((ℓ - 1 : ℕ) : ℤ).toNat / 12 + 1) ∣ Ψ ℓ f' := by
      have e : Ψ ℓ f' = Ψ ℓ (f' * partitionGF ^ ℓ) * E ^ ℓ := by
        rw [map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (Ψ ℓ partitionGF), hEP, one_pow,
          mul_one]
      rw [e, show ((ℓ - 1 : ℕ) : ℤ).toNat / 12 + 1 = 2 by rw [Int.toNat_natCast]; omega]
      exact Dvd.dvd.mul_right hX _
    have h0 := sturm ℓ 2 ((ℓ - 1 : ℕ) : ℤ) (by push_cast; omega) f' hf' hXf
    rw [hTG, map_mul, h0, zero_mul]
  have hTP0 : T (Ψ ℓ (Pser ℓ 1)) = 0 := by rw [hTP, hTG0, mul_zero]
  -- read off coefficient `N`
  have hN1 : 1 ≤ N := by omega
  have hle : hshift Q ℓ ≤ Q ^ 2 * N := by nlinarith
  have hleg : legendreSym Q (24 * (N : ℤ) - ℓ) = 0 :=
    (legendreSym.eq_zero_iff Q _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hQ)
  have hnd : ¬ Q ^ 2 ∣ N + hshift Q ℓ := by
    rintro ⟨k, hk⟩
    apply hQ2
    have hQ1 : 1 ≤ Q ^ 2 := by nlinarith
    refine ⟨24 * (k : ℤ) - ℓ, ?_⟩
    have h24k : (24 : ℤ) * (N + hshift Q ℓ) = 24 * (Q ^ 2 * k) := by exact_mod_cast congrArg (24 * ·) hk
    have hd' : (24 : ℤ) * hshift Q ℓ = ((Q : ℤ) ^ 2 - 1) * ℓ := by
      have := hd; push_cast [Nat.cast_sub hQ1] at this ⊢; exact_mod_cast this
    linear_combination h24k - hd'
  have hc := congrArg (coeff N) hTP0
  rw [coeff_heckeHalf, if_pos hle, hleg, if_neg hnd, map_zero] at hc
  simp only [mul_zero, zero_mul, Int.cast_zero, add_zero] at hc
  rw [coeff_map, coeff_Pser1 ℓ h24, if_pos] at hc
  · rw [MockTheta5.JTP.coeff_partitionGF_eq_card] at hc
    have : ((Fintype.card (Nat.Partition (ℓ * (Q ^ 2 * N - hshift Q ℓ) - δ ℓ)) : ℕ) : ZMod ℓ) = 0 := by
      simpa using hc
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  · -- `δ ≤ ℓ`, as `ℓ ≤ 23`
    have hδ : δ ℓ ≤ ℓ := by
      have : 24 * δ ℓ ≤ 24 * ℓ := by nlinarith
      omega
    have : 1 ≤ Q ^ 2 * N - hshift Q ℓ := by
      have : Q ^ 2 ≤ Q ^ 2 * N := Nat.le_mul_of_pos_right _ hN1
      omega
    nlinarith

end RamanujanTau.AtkinSporadic.Weaver
