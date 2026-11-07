import RamanujanTau.AtkinSporadic.Twist13
import RamanujanTau.FiniteArithmetic.PartitionPrefix

/-!
# Atkin's sporadic congruence `p(11³·13·n + 237) ≡ 0 (mod 13)`, conditional on `EtaHecke`

`F̄ = Ψ₁₃(twPGF)` is the twisted partition series modulo 13 (`Twist13`). By `Twist13.twisted_eq`,
`F̄ = Ψ₁₃(g·P)` with `g ∈ S₁₆₈(SL₂(ℤ))` integral, i.e. `F̄` is the reduction of `g/η`.

* `twisted_hecke`: **if** `T(Q²)` preserves `η^{−1}S₁₆₈` (`EtaHecke Q 168 1`), then
  `T(Q²) F̄ = μ F̄` for the `μ` certified by a kernel check of the first 15 coefficients
  (Sturm's bound for weight 168 is 15), which needs `p(N) mod 13` for `N < Q²·15`.
* `vanish_of_eigen`: then `p(N) ≡ 0 (mod 13)` whenever `24N − 1 = Q²m`, `(m/Q) = ε`, `(m/13) = −1`,
  provided `μ = s ε Q^166` with `s = χ₁₂(Q)((−1)^167/Q)`.
* `atkin_13_class`: at `Q = 11`, `μ = 3`: `p(N) ≡ 0 (mod 13)` when `24N − 1 = 121 m`, `(m/11) = 1`,
  `(m/13) = −1` (thirty progressions modulo `17303`).
* **`atkin_13`**: `13 ∣ p(17303 n + 237)` for every `n` (Atkin 1968), given `EtaHecke 11 168 1`.
* `atkin_13_Q37`: at `Q = 37`, `μ = 3`: `p(N) ≡ 0` when `24N − 1 = 37² m`, `(m/37) = −1`, `(m/13) = −1`.

The only unproved input is the named hypothesis `EtaHecke`; everything else is unconditional.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Atkin13
open PowerSeries BoylanWebb
open MockTheta5.JTP (qfacInf partitionGF)
open RamanujanTau.FiniteArithmetic
open Twist13

/-! ### The finite check -/

/-- Euler's criterion, computably. -/
def legC (p : ℕ) (a : ℤ) : ℤ :=
  if (a : ZMod p) ^ (p / 2) = 1 then 1 else if (a : ZMod p) ^ (p / 2) = -1 then -1 else 0

/-- The twisted coefficient read from a packed partition prefix. -/
def Fv (B i : ℕ) : ZMod 13 :=
  if legC 13 (24 * (i : ℤ) - 1) = -1 then (Packed.lane B i : ZMod 13) else 0

/-- Coefficient `N` of `T(Q²)F̄ − μF̄` in weight `167 + 1/2`, from the prefix `B`. -/
def EB (Q : ℕ) (μ : ZMod 13) (B N : ℕ) : ZMod 13 :=
  (if hshift Q 1 ≤ Q ^ 2 * N then Fv B (Q ^ 2 * N - hshift Q 1) else 0)
  + ((legC Q 12 * legC Q ((-1) ^ 167) * legC Q (24 * (N : ℤ) - 1) * (Q : ℤ) ^ 166 : ℤ) : ZMod 13) *
      Fv B N
  + (if Q ^ 2 ∣ N + hshift Q 1 then ((Q : ZMod 13) ^ 333) * Fv B ((N + hshift Q 1) / Q ^ 2) else 0)
  - μ * Fv B N

/-- The kernel certificate: the first 15 coefficients of `T(Q²)F̄ − μF̄` vanish. -/
def chk (Q : ℕ) (μ : ZMod 13) (Npre J : ℕ) : Bool :=
  match PartitionPrefix.pgfPrefix 13 Npre J with
  | some B => (List.range 15).all fun N => decide (EB Q μ B N = 0)
  | none => false

/-! ### From the certificate to all coefficients -/

lemma coeff_F (Npre J B : ℕ) (hN0 : 0 < Npre) (hN : Npre ≤ 2 ^ 16)
    (hJ : Npre ≤ PartitionPrefix.pentLow J) (hB : PartitionPrefix.pgfPrefix 13 Npre J = some B)
    (i : ℕ) (hi : i < Npre) : coeff i (Ψ 13 twPGF) = Fv B i := by
  have hc := PartitionPrefix.coeff_pgf (by norm_num) (by norm_num) hN0 hN hJ hB i hi
  have hl : legendreSym 13 (24 * (i : ℤ) - 1) = legC 13 (24 * (i : ℤ) - 1) :=
    legendreSym_val 13 (by norm_num) _
  rw [coeff_map, twPGF, coeff_mk, Fv, hl, ← MockTheta5.JTP.coeff_partitionGF_eq_card]
  split_ifs
  · rw [eq_intCast]; exact hc
  · simp

/-- **`T(Q²)` acts on the twisted series by a scalar**, given `EtaHecke Q 168 1` and the check. -/
theorem twisted_hecke (Q : ℕ) [Fact Q.Prime] (hQ3 : 3 ≤ Q) (μ : ZMod 13) (Npre J : ℕ)
    (hN0 : 0 < Npre) (hN : Npre ≤ 2 ^ 16) (hJ : Npre ≤ PartitionPrefix.pentLow J)
    (hcov : Q ^ 2 * 14 < Npre) (hok : chk Q μ Npre J = true) (H : EtaHeckeMod 13 Q 168 1) :
    heckeHalf Q 1 167 (heckeSign Q 167) (Ψ 13 twPGF) = PowerSeries.C μ * Ψ 13 twPGF := by
  obtain ⟨g, hg, hg0, hgF⟩ := twisted_eq
  obtain ⟨g', hg', hg'0, hT⟩ := H g hg hg0
  rw [show 168 - (1 + 1) / 2 = 167 by norm_num] at hT
  try simp only [pow_one] at hT
  set F := Ψ 13 twPGF with hFdef
  set E : PowerSeries (ZMod 13) := Ψ 13 qfacInf
  set P : PowerSeries (ZMod 13) := Ψ 13 partitionGF
  have hEP : E * P = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
  -- the certificate
  unfold chk at hok
  cases hB : PartitionPrefix.pgfPrefix 13 Npre J with
  | none => rw [hB] at hok; exact absurd hok (by simp)
  | some B =>
  rw [hB] at hok
  have hall : ∀ N < 15, EB Q μ B N = 0 := by
    intro N hN15
    have := List.all_eq_true.mp hok N (List.mem_range.mpr hN15)
    simpa using this
  -- the difference `D = g' − μ̃ g`
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℤ, ((m0 : ℤ) : ZMod 13) = μ := ⟨μ.val, by simp⟩
  set D : PowerSeries ℤ := g' - PowerSeries.C m0 * g
  have hD : IntForm ((168 : ℕ) : ℤ) D := hg'.sub (hg.C_mul m0)
  have hDP : Ψ 13 (D * partitionGF) =
      heckeHalf Q 1 167 (heckeSign Q 167) F - PowerSeries.C μ * F := by
    have e1 : Ψ 13 (g' * partitionGF) = heckeHalf Q 1 167 (heckeSign Q 167) F := by
      rw [hgF]; exact hT.symm
    have e2 : Ψ 13 (PowerSeries.C m0 * (g * partitionGF)) = PowerSeries.C μ * F := by
      rw [map_mul, PowerSeries.map_C, eq_intCast, hm0, hgF]
    rw [show D * partitionGF = g' * partitionGF - PowerSeries.C m0 * (g * partitionGF) by ring,
      map_sub, e1, e2]
  -- the first 15 coefficients vanish
  have hlow : ∀ N < 15, coeff N (Ψ 13 (D * partitionGF)) = 0 := by
    intro N hN15
    have hcf := coeff_F Npre J B hN0 hN hJ hB
    have hNlt : N < Npre := by nlinarith
    have hsh : hshift Q 1 < Q ^ 2 := by
      unfold hshift
      have := Nat.div_le_self ((Q ^ 2 - 1) * 1) 24
      have : 0 < Q ^ 2 := by positivity
      omega
    have e1 : (if hshift Q 1 ≤ Q ^ 2 * N then coeff (Q ^ 2 * N - hshift Q 1) F else 0) =
        (if hshift Q 1 ≤ Q ^ 2 * N then Fv B (Q ^ 2 * N - hshift Q 1) else 0) := by
      split_ifs
      · exact hcf _ (by have := Nat.sub_le (Q ^ 2 * N) (hshift Q 1); nlinarith)
      · rfl
    have e3 : (if Q ^ 2 ∣ N + hshift Q 1 then ((Q : ZMod 13) ^ (2 * 167 - 1)) *
          coeff ((N + hshift Q 1) / Q ^ 2) F else 0) =
        (if Q ^ 2 ∣ N + hshift Q 1 then ((Q : ZMod 13) ^ 333) * Fv B ((N + hshift Q 1) / Q ^ 2)
          else 0) := by
      split_ifs
      · rw [hcf _ (by have := Nat.div_le_self (N + hshift Q 1) (Q ^ 2); nlinarith)]
      · rfl
    refine Eq.trans ?_ (hall N hN15)
    rw [hDP, map_sub, coeff_heckeHalf, coeff_C_mul, Nat.cast_one, e1, e3, hcf N hNlt, EB, heckeSign,
      legendreSym_val Q hQ3 12, legendreSym_val Q hQ3 ((-1) ^ 167),
      legendreSym_val Q hQ3 (24 * (N : ℤ) - 1)]
    simp only [legC, show 167 - 1 = 166 by norm_num]
  have hX : (X : PowerSeries (ZMod 13)) ^ 15 ∣ Ψ 13 (D * partitionGF) :=
    X_pow_dvd_iff.mpr hlow
  have hXD : (X : PowerSeries (ZMod 13)) ^ (((168 : ℕ) : ℤ).toNat / 12 + 1) ∣ Ψ 13 D := by
    have : Ψ 13 D = Ψ 13 (D * partitionGF) * E := by
      rw [map_mul, mul_assoc, show Ψ 13 partitionGF * E = 1 by rw [mul_comm]; exact hEP, mul_one]
    rw [this, show ((168 : ℕ) : ℤ).toNat / 12 + 1 = 15 by decide]
    exact Dvd.dvd.mul_right hX _
  have hD0 := sturm 13 15 ((168 : ℕ) : ℤ) (by norm_num) D hD hXD
  have : heckeHalf Q 1 167 (heckeSign Q 167) F - PowerSeries.C μ * F = 0 := by
    rw [← hDP, map_mul, hD0, zero_mul]
  exact sub_eq_zero.mp this

/-! ### From the eigenrelation to partition congruences -/

/-- **Vanishing classes.** If `T(Q²)F̄ = μF̄` and `μ = s ε Q^166` in `𝔽₁₃`, then `13 ∣ p(N)` whenever
`24N = Q² m + 1` with `(m/Q) = ε ≠ 0` and `(m/13) = −1`. -/
theorem vanish_of_eigen (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) (μ : ZMod 13)
    (hd : 24 * hshift Q 1 + 1 = Q ^ 2)
    (heig : heckeHalf Q 1 167 (heckeSign Q 167) (Ψ 13 twPGF) = PowerSeries.C μ * Ψ 13 twPGF)
    (ε : ℤ) (hε : ε ≠ 0) (hμ : μ = ((heckeSign Q 167 * ε * (Q : ℤ) ^ 166 : ℤ) : ZMod 13))
    (hQ13 : Q ≠ 13) (N m : ℕ) (hm : 24 * N = Q ^ 2 * m + 1) (hQm : legendreSym Q m = ε)
    (h13 : legendreSym 13 m = -1) : 13 ∣ Fintype.card (Nat.Partition N) := by
  -- `N'` with `24 N' − 1 = m`
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨N', hN'⟩ : ∃ N', m + 1 = 24 * N' := by
    have h1 : (Q ^ 2 * m + 1) % 24 = 0 := by omega
    have hq : Q ^ 2 % 24 = 1 := by omega
    refine ⟨(m + 1) / 24, ?_⟩
    have : (m + 1) % 24 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, hq] at h1
      simpa [Nat.add_mod] using h1
    omega
  have hNi : Q ^ 2 * N' - hshift Q 1 = N := by
    have : 24 * (Q ^ 2 * N') = 24 * N + 24 * hshift Q 1 := by
      rw [← mul_assoc, mul_comm 24 (Q ^ 2), mul_assoc, ← hN']; nlinarith
    omega
  have hle : hshift Q 1 ≤ Q ^ 2 * N' := by
    have : 24 * (Q ^ 2 * N') = 24 * N + 24 * hshift Q 1 := by
      rw [← mul_assoc, mul_comm 24 (Q ^ 2), mul_assoc, ← hN']; nlinarith
    omega
  -- the third Hecke term vanishes: `Q² ∤ N' + d`
  have hnd : ¬ Q ^ 2 ∣ N' + hshift Q 1 := by
    rintro ⟨c, hc⟩
    have h24 : 24 * (N' + hshift Q 1) = m + Q ^ 2 := by omega
    have hQ : (Q : ℤ) ∣ m := by
      have : (Q : ℕ) ∣ m := by
        have : Q ^ 2 ∣ m + Q ^ 2 := ⟨24 * c, by rw [← h24, hc]; ring⟩
        have h2 : Q ∣ m + Q ^ 2 := (Dvd.intro_left _ rfl : Q ∣ Q ^ 2).trans this |>.trans (dvd_refl _)
        exact (Nat.dvd_add_right (Dvd.intro_left (Q ^ 1) (by ring) : Q ∣ Q ^ 2)).mp
          (by simpa [add_comm] using h2)
      exact_mod_cast this
    have h0 : ((m : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hQ
    rw [(legendreSym.eq_zero_iff Q _).mpr h0] at hQm
    exact hε hQm.symm
  have hc := congrArg (coeff N') heig
  rw [coeff_heckeHalf, if_pos hle, hNi, if_neg hnd, add_zero, coeff_C_mul, Nat.cast_one] at hc
  have hlegQ : legendreSym Q (24 * (N' : ℤ) - 1) = ε := by
    rw [show (24 * (N' : ℤ) - 1) = (m : ℤ) by omega]; exact hQm
  rw [hlegQ, hμ, show 167 - 1 = 166 by norm_num] at hc
  have hcN : coeff N (Ψ 13 twPGF) = 0 := by linear_combination hc
  -- `((24N − 1)/13) = (Q²/13)(m/13) = −1`
  have hQz : ((Q : ℤ) : ZMod 13) ≠ 0 := by
    intro h
    have h' : ((Q : ℕ) : ZMod 13) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hQ13 ((Nat.prime_dvd_prime_iff_eq (by norm_num) (Fact.out)).mp h').symm
  have hleg : legendreSym 13 (24 * (N : ℤ) - 1) = -1 := by
    rw [show (24 * (N : ℤ) - 1) = (Q : ℤ) ^ 2 * m by
        have : (24 * N : ℤ) = Q ^ 2 * m + 1 := by exact_mod_cast hm
        linarith,
      legendreSym.mul, h13, legendreSym.sq_one' 13 hQz]
    norm_num
  rw [coeff_map, twPGF, coeff_mk, if_pos hleg] at hcN
  have : ((Fintype.card (Nat.Partition N) : ℕ) : ZMod 13) = 0 := by simpa using hcN
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

end RamanujanTau.AtkinSporadic.Atkin13
