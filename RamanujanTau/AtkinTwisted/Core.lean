import RamanujanTau.AtkinSporadic.Atkin13
import RamanujanTau.GaussSign.EtaHeckeAll

/-!
# Atkin's twisted mod-13 class: `T(Q²)` eigen-relations for many `Q`, from one long prefix

`F̄ = Ψ₁₃(twPGF) = Σ_{((24N−1)/13) = −1} p(N) qᴺ (mod 13)` is the reduction of `g/η`,
`g ∈ S₁₆₈(SL₂ℤ)` (`AtkinSporadic.Twist13.twisted_eq`). For every prime `Q ≥ 5`,
`GaussSign.etaHecke_all` gives `EtaHecke Q 168 1`, so `T(Q²)F̄ − μF̄ = D/η` with `D ∈ S₁₆₈`
reduced mod 13, and Sturm's bound (15 coefficients) decides `T(Q²)F̄ = μF̄`.

* `allOk`: **one** kernel-certified prefix of `p(n) mod 13` (`PartitionPrefix.pgfPrefixG`, any
  length) checked against a list of pairs `(Q, μ)` (15 coefficients `Atkin13.EB` each).
* `eigen_of_allOk`: the eigen-relation `T(Q²)F̄ = μF̄` for every pair in the list, unconditionally.
* `vanish_ono`: if `μ = 0`, then `13 ∣ p(N)` whenever `24N − 1 = Q³n`, `Q ∤ n`, `(Qn/13) = −1`.
  (The Atkin type `μ = s ε Q¹⁶⁶` is `Atkin13.vanish_of_eigen`.)
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinTwisted
open PowerSeries BoylanWebb
open MockTheta5.JTP (qfacInf partitionGF)
open RamanujanTau.FiniteArithmetic RamanujanTau.AtkinSporadic
open Twist13
open Atkin13 (legC Fv EB)

/-- `T(Q²)` (weight `167 + 1/2`) on the twisted series modulo 13. -/
noncomputable abbrev TT (Q : ℕ) [Fact Q.Prime] : PowerSeries (ZMod 13) :=
  heckeHalf Q 1 167 (heckeSign Q 167) (Ψ 13 twPGF)

/-- `EtaHeckeMod 13 Q 168 1` for every prime `Q ≥ 5` (from `GaussSign.etaHecke_all`). -/
theorem etaHeckeMod (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 13 Q 168 1 :=
  (GaussSign.etaHecke_all Q hQ5 168 (by norm_num)).toMod 13

/-- **Sturm step.** If the twisted coefficients below `Npre` are read off `B` and the 15 checked
coefficients of `T(Q²)F̄ − μF̄` vanish, then `T(Q²)F̄ = μF̄`. -/
theorem eigen_of_coeffs (Q : ℕ) [Fact Q.Prime] (hQ3 : 3 ≤ Q) (μ : ZMod 13) (Npre B : ℕ)
    (hcf : ∀ i < Npre, coeff i (Ψ 13 twPGF) = Fv B i) (hcov : Q ^ 2 * 14 < Npre)
    (hall : ∀ N < 15, EB Q μ B N = 0) (H : EtaHeckeMod 13 Q 168 1) :
    heckeHalf Q 1 167 (heckeSign Q 167) (Ψ 13 twPGF) = PowerSeries.C μ * Ψ 13 twPGF := by
  obtain ⟨g, hg, hg0, hgF⟩ := twisted_eq
  obtain ⟨g', hg', hg'0, hT⟩ := H g hg hg0
  rw [show 168 - (1 + 1) / 2 = 167 by norm_num] at hT
  try simp only [pow_one] at hT
  set F := Ψ 13 twPGF with hFdef
  set E : PowerSeries (ZMod 13) := Ψ 13 qfacInf
  set P : PowerSeries (ZMod 13) := Ψ 13 partitionGF
  have hEP : E * P = 1 := by rw [← map_mul, qfac_mul_pgf, map_one]
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
  have hlow : ∀ N < 15, coeff N (Ψ 13 (D * partitionGF)) = 0 := by
    intro N hN15
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

/-- The 15 Sturm coefficients for one pair `(Q, μ)`, plus the coverage condition. -/
def okQ (B Npre : ℕ) (p : ℕ × ZMod 13) : Bool :=
  decide (p.1 ^ 2 * 14 < Npre) && (List.range 15).all fun N => decide (EB p.1 p.2 B N = 0)

/-- One long certified prefix of `p(n) mod 13`, checked against a list of pairs `(Q, μ)`. -/
def allOk (R Npre d k n ku kb kc : ℕ) (L : List (ℕ × ZMod 13)) : Bool :=
  match PartitionPrefix.pgfPrefixG 13 R Npre d k n ku kb kc with
  | some B => L.all (okQ B Npre)
  | none => false

/-- **The eigen-relation for every pair of a certified list**, unconditionally. -/
theorem eigen_of_allOk {R Npre d k n ku kb kc kN : ℕ}
    (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + 13 * 2 ^ kc ≤ Packed.x) (hN0 : 0 < Npre)
    (hN : Npre ≤ 2 ^ kN) (hn : k * 2 ^ d ≤ 2 ^ 20) (hJ : Npre ≤ PartitionPrefix.pentLow (k * 2 ^ d))
    {L : List (ℕ × ZMod 13)} (hok : allOk R Npre d k n ku kb kc L = true)
    (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) (μ : ZMod 13) (hmem : (Q, μ) ∈ L) :
    TT Q = PowerSeries.C μ * Ψ 13 twPGF := by
  unfold allOk at hok
  cases hB : PartitionPrefix.pgfPrefixG 13 R Npre d k n ku kb kc with
  | none => rw [hB] at hok; exact absurd hok (by simp)
  | some B =>
  rw [hB] at hok
  have h1 := List.all_eq_true.mp hok _ hmem
  simp only [okQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h1
  obtain ⟨hcov, hall⟩ := h1
  have hcp := PartitionPrefix.coeff_pgfG (Q := 13) (by norm_num) (by norm_num) hk hno hN0 hN hn hJ hB
  have hcf : ∀ i < Npre, coeff i (Ψ 13 twPGF) = Fv B i := by
    intro i hi
    have hl : legendreSym 13 (24 * (i : ℤ) - 1) = legC 13 (24 * (i : ℤ) - 1) :=
      legendreSym_val 13 (by norm_num) _
    rw [coeff_map, twPGF, coeff_mk, Fv, hl, ← MockTheta5.JTP.coeff_partitionGF_eq_card]
    split_ifs
    · rw [eq_intCast]; exact hcp i hi
    · simp
  exact eigen_of_coeffs Q (by omega) μ Npre B hcf hcov (fun N hN => by simpa using hall N hN)
    (etaHeckeMod Q hQ5)

/-- **Ono type in the twisted class.** If `T(Q²)F̄ = 0`, then `13 ∣ p(N)` whenever
`24N − 1 = Q³n` with `Q ∤ n` and `(Qn/13) = −1`. -/
theorem vanish_ono (Q : ℕ) [Fact Q.Prime] (hQ13 : Q ≠ 13)
    (hd24 : 24 * hshift Q 1 + 1 = Q ^ 2)
    (heig : TT Q = PowerSeries.C 0 * Ψ 13 twPGF)
    (N n : ℕ) (hm : 24 * N = Q ^ 3 * n + 1) (hQn : ¬ Q ∣ n)
    (h13 : legendreSym 13 ((Q : ℤ) * n) = -1) : 13 ∣ Fintype.card (Nat.Partition N) := by
  set c := hshift Q 1 with hd
  have hc : Q ^ 2 = 24 * c + 1 := hd24.symm
  -- `N'` with `24 N' − 1 = Q n`
  obtain ⟨N', hN'⟩ : ∃ N', Q * n + 1 = 24 * N' := by
    have e : Q ^ 3 * n + 1 = (Q * n + 1) + 24 * (c * Q * n) := by
      rw [show Q ^ 3 = Q ^ 2 * Q by ring, hc]; ring
    have h1 : 24 ∣ Q * n + 1 := by
      have : 24 ∣ Q ^ 3 * n + 1 := ⟨N, by omega⟩
      rw [e] at this
      exact (Nat.dvd_add_left (dvd_mul_right 24 _)).mp this
    obtain ⟨t, ht⟩ := h1
    exact ⟨t, ht⟩
  have key : 24 * (Q ^ 2 * N') = 24 * N + 24 * c := by
    have : 24 * (Q ^ 2 * N') = Q ^ 2 * (Q * n + 1) := by rw [hN']; ring
    rw [this, hc]
    have e2 : 24 * N = Q ^ 3 * n + 1 := hm
    rw [show Q ^ 3 = Q ^ 2 * Q by ring, hc] at e2
    nlinarith
  have hle : hshift Q 1 ≤ Q ^ 2 * N' := by omega
  have hNi : Q ^ 2 * N' - hshift Q 1 = N := by omega
  have hnd : ¬ Q ^ 2 ∣ N' + hshift Q 1 := by
    rintro ⟨e, he⟩
    apply hQn
    have h24 : 24 * (N' + hshift Q 1) = Q * n + Q ^ 2 := by omega
    have : Q ^ 2 ∣ Q * n + Q ^ 2 := ⟨24 * e, by rw [← h24, he]; ring⟩
    have h2 : Q ^ 2 ∣ Q * n := (Nat.dvd_add_left (dvd_refl _)).mp this
    rw [sq] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (Fact.out : Q.Prime).pos h2
  have hcoef := congrArg (coeff N') heig
  rw [TT, coeff_heckeHalf, if_pos hle, hNi, if_neg hnd, add_zero, coeff_C_mul, Nat.cast_one] at hcoef
  have hlegQ : legendreSym Q (24 * (N' : ℤ) - 1) = 0 := by
    rw [show (24 * (N' : ℤ) - 1) = (Q : ℤ) * n by omega]
    rw [legendreSym.eq_zero_iff]
    push_cast; simp
  rw [hlegQ] at hcoef
  have hcN : coeff N (Ψ 13 twPGF) = 0 := by simpa using hcoef
  have hQz : ((Q : ℤ) : ZMod 13) ≠ 0 := by
    intro h
    have h' : ((Q : ℕ) : ZMod 13) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hQ13 ((Nat.prime_dvd_prime_iff_eq (by norm_num) (Fact.out)).mp h').symm
  have hleg : legendreSym 13 (24 * (N : ℤ) - 1) = -1 := by
    rw [show (24 * (N : ℤ) - 1) = (Q : ℤ) ^ 2 * ((Q : ℤ) * n) by
        have : (24 * N : ℤ) = Q ^ 3 * n + 1 := by exact_mod_cast hm
        linear_combination this,
      legendreSym.mul, h13, legendreSym.sq_one' 13 hQz]
    norm_num
  rw [coeff_map, twPGF, coeff_mk, if_pos hleg] at hcN
  have : ((Fintype.card (Nat.Partition N) : ℕ) : ZMod 13) = 0 := by simpa using hcN
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

end RamanujanTau.AtkinTwisted
