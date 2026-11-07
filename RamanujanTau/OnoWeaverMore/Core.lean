import RamanujanTau.AtkinSporadic.WeaverUnconditional
import RamanujanTau.FiniteArithmetic.PartitionPrefix

/-!
# Ono–Weaver congruences of both types from a `T(Q²)` eigen-relation

Let `G = Σ_N p(ℓN − δ) q^N` (`BoylanWebb.Pser ℓ 1`) and `T = T(Q²)` in weight `λ + 1/2`,
`λ = (ℓ−1) − (ℓ+1)/2`, on the `N`-coordinate (`AtkinSporadic.heckeHalf`). If `T G ≡ μ G (mod ℓ)`:

* (`vanish_core`) for every `m` with `24 ∣ ℓQ²m + 1`, `Q² ∤ m` and
  `s·(m/Q)·Q^{λ−1} ≡ μ`, `ℓ ∣ p((ℓQ²m + 1)/24)` (`s = heckeSign`);
* (`atkin_of_eigen`) **Atkin type**: if `μ ≡ ε s Q^{λ−1}`, `ε = ±1`, then
  `ℓ ∣ p((ℓQ²m+1)/24)` whenever `(m/Q) = ε` (Weaver's tuples `(ℓ, Q, ±1)`);
* (`ono_of_eigen`) **Ono type**: if `μ ≡ 0`, then `ℓ ∣ p((ℓQ³n+1)/24)` whenever `Q ∤ n`.

The eigen-relation itself comes from `EtaHeckeMod` (`eigen_of_etaHecke`, for `ℓ ≤ 23`) together
with **one** coefficient identity, which `allOk_sound` reads off a kernel-certified long prefix of
`p(n) mod ℓ` (`PartitionPrefix.pgfPrefixG`): one prefix per `ℓ` serves all `Q` in a list.
-/

set_option autoImplicit false

namespace RamanujanTau.OnoWeaverMore
open PowerSeries BoylanWebb RamanujanTau.FiniteArithmetic RamanujanTau.AtkinSporadic
open MockTheta5.JTP (qfacInf partitionGF)
open Weaver (wlam)
open Atkin13 (legC)

section
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `T(Q²)` on `N`-indexed series modulo `ℓ`. -/
noncomputable abbrev TT (Q : ℕ) [Fact Q.Prime] (G : PowerSeries (ZMod ℓ)) : PowerSeries (ZMod ℓ) :=
  heckeHalf Q ℓ (wlam ℓ) (heckeSign Q (wlam ℓ)) G

/-- The eigenvalue `ε s Q^{λ−1}` attached to a sign `ε ∈ {−1, 0, 1}`. -/
noncomputable def muE (Q : ℕ) [Fact Q.Prime] (ε : ℤ) : ZMod ℓ :=
  ((heckeSign Q (wlam ℓ) * ε * (Q : ℤ) ^ (wlam ℓ - 1) : ℤ) : ZMod ℓ)

omit hℓ in
lemma coprime24 (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) : Nat.Coprime 24 ℓ := by
  have g1 : Nat.gcd 24 ℓ ∣ 24 * δ ℓ + 1 :=
    h24 ▸ (Nat.gcd_dvd_right 24 ℓ).trans (Dvd.intro ℓ (sq ℓ).symm)
  have g2 : Nat.gcd 24 ℓ ∣ 24 * δ ℓ := (Nat.gcd_dvd_left 24 ℓ).mul_right _
  exact Nat.dvd_one.mp ((Nat.dvd_add_right g2).mp g1)

/-- **Reading one coefficient of the eigen-relation.** -/
theorem vanish_core (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (μ : ZMod ℓ) (heig : TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C μ * Ψ ℓ (Pser ℓ 1))
    (m : ℕ) (hm : 24 ∣ ℓ * Q ^ 2 * m + 1) (hQ2 : ¬ Q ^ 2 ∣ m)
    (hμ : ((heckeSign Q (wlam ℓ) * legendreSym Q m * (Q : ℤ) ^ (wlam ℓ - 1) : ℤ) : ZMod ℓ) = μ) :
    ℓ ∣ Fintype.card (Nat.Partition ((ℓ * Q ^ 2 * m + 1) / 24)) := by
  obtain ⟨hQ2', hQ3'⟩ := Equivariance.prime_ge_five hQ.out hQ5
  have hq := TheoremA.HalfIntegral.sq_mod_24 hQ2' hQ3'
  obtain ⟨k, hk⟩ : ∃ k, Q ^ 2 = 24 * k + 1 := ⟨Q ^ 2 / 24, by omega⟩
  -- `24 ∣ m + ℓ`
  have h1 : 24 ∣ ℓ * m + 1 := by
    have e : ℓ * Q ^ 2 * m + 1 = (ℓ * m + 1) + 24 * (ℓ * k * m) := by rw [hk]; ring
    rw [e] at hm
    exact (Nat.dvd_add_left (dvd_mul_right 24 _)).mp hm
  have h2 : 24 ∣ (m + ℓ) * ℓ := by
    have e : (m + ℓ) * ℓ = (ℓ * m + 1) + 24 * δ ℓ := by
      have : ℓ * ℓ = 24 * δ ℓ + 1 := by rw [← sq]; exact h24.symm
      nlinarith [this]
    rw [e]
    exact dvd_add h1 (dvd_mul_right 24 _)
  obtain ⟨N, hN⟩ : 24 ∣ m + ℓ := (coprime24 ℓ h24).dvd_of_dvd_mul_right h2
  -- `d = kℓ`, `Q²N − d = km + N`
  set d := hshift Q ℓ with hddef
  have hd : 24 * d = (Q ^ 2 - 1) * ℓ := Equivariance.hshift_spec hQ2' hQ3' ℓ
  have hdk : d = k * ℓ := by
    rw [hk, Nat.add_sub_cancel] at hd
    have : 24 * d = 24 * (k * ℓ) := by rw [hd]; ring
    omega
  have hQN : Q ^ 2 * N = d + (k * m + N) := by
    rw [hdk, hk]
    have : 24 * ((24 * k + 1) * N) = 24 * (k * ℓ + (k * m + N)) := by
      have e1 : 24 * ((24 * k + 1) * N) = (24 * k + 1) * (24 * N) := by ring
      rw [e1, ← hN]; nlinarith [hN]
    omega
  have hle : d ≤ Q ^ 2 * N := by omega
  have hidx : Q ^ 2 * N - d = k * m + N := by omega
  -- the partition index
  set P := ℓ * (k * m + N) with hP
  have h24P : 24 * P = ℓ * Q ^ 2 * m + 24 * δ ℓ + 1 := by
    have : ℓ * ℓ = 24 * δ ℓ + 1 := by rw [← sq]; exact h24.symm
    have e1 : 24 * P = ℓ * (24 * k * m) + ℓ * (24 * N) := by rw [hP]; ring
    rw [e1, ← hN, hk]
    nlinarith [this]
  have hδP : δ ℓ ≤ P := by omega
  have hM : (ℓ * Q ^ 2 * m + 1) / 24 = P - δ ℓ := by omega
  -- the coefficient `N` of the eigen-relation
  have hleg : legendreSym Q (24 * (N : ℤ) - ℓ) = legendreSym Q m := by
    congr 1
    have : ((m + ℓ : ℕ) : ℤ) = ((24 * N : ℕ) : ℤ) := by rw [hN]
    push_cast at this
    linarith
  have hnd : ¬ Q ^ 2 ∣ N + d := by
    rintro ⟨c, hc⟩
    apply hQ2
    have e : 24 * (N + d) = m + Q ^ 2 * ℓ := by
      rw [hdk, hk]
      have : 24 * (N + k * ℓ) = 24 * N + 24 * k * ℓ := by ring
      rw [this, ← hN]; ring
    rw [hc] at e
    have e2 : Q ^ 2 * (24 * c) = 24 * (Q ^ 2 * c) := by ring
    exact ⟨24 * c - ℓ, by rw [Nat.mul_sub]; omega⟩
  have hc := congrArg (coeff N) heig
  rw [coeff_heckeHalf, if_pos hle, if_neg hnd, hleg, coeff_C_mul, add_zero, hμ, hidx] at hc
  have h0 : coeff (k * m + N) (Ψ ℓ (Pser ℓ 1)) = 0 := by
    have := hc; simpa using this
  rw [coeff_map, Weaver.coeff_Pser1 ℓ h24, ← hP, if_pos hδP,
    MockTheta5.JTP.coeff_partitionGF_eq_card] at h0
  rw [hM]
  have : ((Fintype.card (Nat.Partition (P - δ ℓ)) : ℕ) : ZMod ℓ) = 0 := by simpa using h0
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- **Atkin type** `(ℓ, Q, ε)`, `ε = ±1`. -/
theorem atkin_of_eigen (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (ε : ℤ) (hε : ε ≠ 0)
    (heig : TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C (muE ℓ Q ε) * Ψ ℓ (Pser ℓ 1))
    (m : ℕ) (hm : 24 ∣ ℓ * Q ^ 2 * m + 1) (hQm : legendreSym Q m = ε) :
    ℓ ∣ Fintype.card (Nat.Partition ((ℓ * Q ^ 2 * m + 1) / 24)) := by
  refine vanish_core ℓ h24 Q hQ5 _ heig m hm ?_ (by rw [hQm, muE])
  rintro ⟨c, hc⟩
  apply hε
  rw [← hQm, legendreSym.eq_zero_iff]
  have : ((m : ℤ) : ZMod Q) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff, hc]
    exact Dvd.dvd.mul_right (dvd_pow_self Q two_ne_zero) c
  exact this

/-- **Ono type** `(ℓ, Q, 0)`. -/
theorem ono_of_eigen (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (heig : TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C (muE ℓ Q 0) * Ψ ℓ (Pser ℓ 1))
    (n : ℕ) (hn : ¬ Q ∣ n) (h : 24 ∣ ℓ * Q ^ 3 * n + 1) :
    ℓ ∣ Fintype.card (Nat.Partition ((ℓ * Q ^ 3 * n + 1) / 24)) := by
  have e : ℓ * Q ^ 3 * n = ℓ * Q ^ 2 * (Q * n) := by ring
  rw [e] at h ⊢
  refine vanish_core ℓ h24 Q hQ5 _ heig (Q * n) h ?_ ?_
  · rintro ⟨c, hc⟩
    apply hn
    refine ⟨c, ?_⟩
    have : Q * n = Q * (Q * c) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hQ.out.pos this
  · have : legendreSym Q ((Q * n : ℕ) : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right _ _
    rw [this, muE]

/-- **The eigen-relation for `ℓ ≤ 23`** from `EtaHeckeMod` and the coefficient `q¹`. -/
theorem eigen_of_etaHecke (Q : ℕ) [Fact Q.Prime] (hℓ13 : 13 ≤ ℓ) (hℓ23 : ℓ ≤ 23) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : constantCoeff f = 0)
    (c : ZMod ℓ) (hc : c ≠ 0) (heig : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C c * Ψ ℓ f)
    (H : EtaHeckeMod ℓ Q (ℓ - 1) ℓ) (μ : ZMod ℓ)
    (h1 : coeff 1 (TT ℓ Q (Ψ ℓ (Pser ℓ 1))) = μ * coeff 1 (Ψ ℓ (Pser ℓ 1))) :
    TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C μ * Ψ ℓ (Pser ℓ 1) := by
  have hPs := Weaver.Pser_eq ℓ h24 f c heig
  obtain ⟨f', hf', hf'0, hT⟩ := H f hf hf0
  set G := Ψ ℓ (f * partitionGF ^ ℓ) with hGdef
  set E : PowerSeries (ZMod ℓ) := Ψ ℓ qfacInf
  have hEP : E * Ψ ℓ partitionGF = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
  have hTG : TT ℓ Q G = Ψ ℓ (f' * partitionGF ^ ℓ) := hT
  have hTP : TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C c * TT ℓ Q G := by
    rw [hPs]; exact heckeHalf_C_mul _ _ _ _ _ _
  have h1' : coeff 1 (TT ℓ Q G) = μ * coeff 1 G := by
    rw [hTP, hPs, coeff_C_mul, coeff_C_mul] at h1
    exact mul_left_cancel₀ hc (by rw [h1]; ring)
  set μ' : ℤ := (μ.val : ℤ)
  have hμ' : ((μ' : ℤ) : ZMod ℓ) = μ := by simp [μ']
  set D := f' - C μ' * f with hD
  have hDf : IntForm ((ℓ - 1 : ℕ) : ℤ) D := hf'.sub (hf.C_mul μ')
  have hDP : Ψ ℓ (D * partitionGF ^ ℓ) = TT ℓ Q G - C μ * G := by
    rw [hTG, hGdef, hD, sub_mul, map_sub, mul_assoc, map_mul (Ψ ℓ) (C μ'), map_C, eq_intCast, hμ']
  have hX : (X : PowerSeries (ZMod ℓ)) ^ 2 ∣ Ψ ℓ (D * partitionGF ^ ℓ) := by
    rw [X_pow_dvd_iff]
    intro n hn
    interval_cases n
    · rw [coeff_map, coeff_zero_eq_constantCoeff_apply, map_mul, hD]
      simp [hf'0, hf0]
    · rw [hDP, map_sub, coeff_C_mul, h1', sub_self]
  have hXf : (X : PowerSeries (ZMod ℓ)) ^ (((ℓ - 1 : ℕ) : ℤ).toNat / 12 + 1) ∣ Ψ ℓ D := by
    have e : Ψ ℓ D = Ψ ℓ (D * partitionGF ^ ℓ) * E ^ ℓ := by
      rw [map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (Ψ ℓ partitionGF), hEP, one_pow,
        mul_one]
    rw [e, show ((ℓ - 1 : ℕ) : ℤ).toNat / 12 + 1 = 2 by rw [Int.toNat_natCast]; omega]
    exact Dvd.dvd.mul_right hX _
  have h0 := sturm ℓ 2 ((ℓ - 1 : ℕ) : ℤ) (by push_cast; omega) D hDf hXf
  have hTG' : TT ℓ Q G = C μ * G := by
    have : Ψ ℓ (D * partitionGF ^ ℓ) = 0 := by rw [map_mul, h0, zero_mul]
    rw [hDP] at this
    exact sub_eq_zero.mp this
  rw [hTP, hTG', hPs]
  ring

/-! ### The coefficient certificate on a long partition prefix -/

/-- Coefficient `i` of `Σ p(ℓN − δ) q^N` from a packed prefix. -/
def gv (B i : ℕ) : ZMod ℓ := if δ ℓ ≤ ℓ * i then (Packed.lane B (ℓ * i - δ ℓ) : ZMod ℓ) else 0

/-- Coefficient `N₀` of `T(Q²) Σ p(ℓN − δ) q^N`, with computable Legendre symbols. -/
def Wc (Q B N0 : ℕ) : ZMod ℓ :=
  (if hshift Q ℓ ≤ Q ^ 2 * N0 then gv ℓ B (Q ^ 2 * N0 - hshift Q ℓ) else 0)
  + ((legC Q 12 * legC Q ((-1) ^ wlam ℓ) * legC Q (24 * (N0 : ℤ) - ℓ) * (Q : ℤ) ^ (wlam ℓ - 1) : ℤ) :
      ZMod ℓ) * gv ℓ B N0
  + (if Q ^ 2 ∣ N0 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
      gv ℓ B ((N0 + hshift Q ℓ) / Q ^ 2) else 0)

/-- `ε s Q^{λ−1}` times coefficient `N₀`. -/
def Wt (Q B N0 : ℕ) (ε : ℤ) : ZMod ℓ :=
  ((legC Q 12 * legC Q ((-1) ^ wlam ℓ) * ε * (Q : ℤ) ^ (wlam ℓ - 1) : ℤ) : ZMod ℓ) * gv ℓ B N0

def okQ (B Q N0 : ℕ) (ε : ℤ) (Npre : ℕ) : Bool :=
  decide (3 ≤ Q) &&
  decide (ℓ * (Q ^ 2 * N0 - hshift Q ℓ) - δ ℓ < Npre) && decide (ℓ * N0 - δ ℓ < Npre) &&
  decide (ℓ * ((N0 + hshift Q ℓ) / Q ^ 2) - δ ℓ < Npre) &&
  decide (gv ℓ B N0 ≠ 0) && decide (Wc ℓ Q B N0 = Wt ℓ Q B N0 ε)

/-- One certified prefix of `p(n) mod ℓ`, checked against a whole list of pairs `(Q, ε)`. -/
def allOk (R Npre d k n ku kb kc N0 : ℕ) (L : List (ℕ × ℤ)) : Bool :=
  match PartitionPrefix.pgfPrefixG ℓ R Npre d k n ku kb kc with
  | some B => L.all fun p => okQ ℓ B p.1 N0 p.2 Npre
  | none => false

theorem allOk_sound (hℓ21 : ℓ ≤ 2 ^ 21) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    {R Npre d k n ku kb kc kN N0 : ℕ}
    (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + ℓ * 2 ^ kc ≤ Packed.x) (hN0 : 0 < Npre)
    (hN : Npre ≤ 2 ^ kN) (hn : k * 2 ^ d ≤ 2 ^ 20) (hJ : Npre ≤ PartitionPrefix.pentLow (k * 2 ^ d))
    {L : List (ℕ × ℤ)} (hall : allOk ℓ R Npre d k n ku kb kc N0 L = true)
    (Q : ℕ) [Fact Q.Prime] (ε : ℤ) (hmem : (Q, ε) ∈ L) :
    coeff N0 (TT ℓ Q (Ψ ℓ (Pser ℓ 1))) = muE ℓ Q ε * coeff N0 (Ψ ℓ (Pser ℓ 1)) ∧
      coeff N0 (Ψ ℓ (Pser ℓ 1)) ≠ 0 := by
  unfold allOk at hall
  cases hB : PartitionPrefix.pgfPrefixG ℓ R Npre d k n ku kb kc with
  | none => rw [hB] at hall; exact absurd hall (by simp)
  | some B =>
  rw [hB] at hall
  have hok := List.all_eq_true.mp hall _ hmem
  simp only [okQ, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hQ3, hc1⟩, hc2⟩, hc3⟩, hnz⟩, hW⟩ := hok
  have hcp := PartitionPrefix.coeff_pgfG (Nat.Prime.one_le hℓ.out) hℓ21 hk hno hN0 hN hn hJ hB
  have hG : ∀ i, ℓ * i - δ ℓ < Npre → coeff i (Ψ ℓ (Pser ℓ 1)) = gv ℓ B i := by
    intro i hi
    rw [coeff_map, Weaver.coeff_Pser1 ℓ h24, gv]
    split_ifs
    · rw [eq_intCast]; exact hcp _ hi
    · simp
  refine ⟨?_, by rw [hG N0 hc2]; exact hnz⟩
  have e1 : (if hshift Q ℓ ≤ Q ^ 2 * N0 then coeff (Q ^ 2 * N0 - hshift Q ℓ) (Ψ ℓ (Pser ℓ 1))
      else 0) = (if hshift Q ℓ ≤ Q ^ 2 * N0 then gv ℓ B (Q ^ 2 * N0 - hshift Q ℓ) else 0) := by
    split_ifs
    · exact hG _ hc1
    · rfl
  have e3 : (if Q ^ 2 ∣ N0 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
        coeff ((N0 + hshift Q ℓ) / Q ^ 2) (Ψ ℓ (Pser ℓ 1)) else 0) =
      (if Q ^ 2 ∣ N0 + hshift Q ℓ then ((Q : ZMod ℓ) ^ (2 * wlam ℓ - 1)) *
        gv ℓ B ((N0 + hshift Q ℓ) / Q ^ 2) else 0) := by
    split_ifs
    · rw [hG _ hc3]
    · rfl
  have hWc : coeff N0 (TT ℓ Q (Ψ ℓ (Pser ℓ 1))) = Wc ℓ Q B N0 := by
    rw [TT, coeff_heckeHalf, heckeSign, legendreSym_val Q hQ3 12,
      legendreSym_val Q hQ3 ((-1) ^ wlam ℓ), legendreSym_val Q hQ3 (24 * (N0 : ℤ) - ℓ),
      hG N0 hc2, e1, e3, Wc]
    simp only [legC]
  have hWt : muE ℓ Q ε * coeff N0 (Ψ ℓ (Pser ℓ 1)) = Wt ℓ Q B N0 ε := by
    rw [muE, heckeSign, legendreSym_val Q hQ3 12, legendreSym_val Q hQ3 ((-1) ^ wlam ℓ),
      hG N0 hc2, Wt]
    simp only [legC]
  rw [hWc, hWt, hW]

end

end RamanujanTau.OnoWeaverMore
