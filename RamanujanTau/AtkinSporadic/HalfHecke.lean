import RamanujanTau.BoylanWebb.Forms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Half-integral weight Hecke operators on `η`-multiplier forms (q-expansion level)

For a level-one cusp form `G` of weight `k` and `0 < j < 24` with `gcd(j, 6) = 1`, the function
`F = G/η^j` is a cusp form of weight `λ + 1/2 = k − j/2` on `SL₂(ℤ)` with multiplier `ν_η^{−j}`.
Writing `G · ∏(1−qⁿ)^{−j} = Σ_N c(N) qᴺ`, one has `F = Σ_N c(N) q^{(24N − j)/24}`, so the index
`m = 24N − j` is the exponent of `F(24z)`.

For a prime `Q ≥ 5` the Hecke operator `T(Q²)` acts on these coefficients by
`b(m) = a(Q²m) + χ₁₂(Q) ((−1)^λ m / Q) Q^{λ−1} a(m) + Q^{2λ−1} a(m/Q²)`.
In the `N`-index `m = Q²m'` corresponds to `Q²N − d` with `d = (Q²−1)j/24`, and `m/Q²` to
`(N + d)/Q²`. `heckeHalf` is this operator on power series over any commutative ring.

`EtaHecke Q k j` is the classical statement that `T(Q²)` preserves `η^{−j}·S_k(SL₂(ℤ))`
with integral coefficients. It is a theorem of the theory of half-integral weight Hecke operators
(Shimura; for `η`-multipliers on `SL₂(ℤ)` see Y. Yang, Nagoya Math. J. 215 (2014), and Knopp,
*Modular functions in analytic number theory*, Ch. 4). **It is not proved here**; every theorem
that uses it takes it as an explicit hypothesis. The coefficient formula and the sign convention
were checked numerically in characteristic zero (`scripts/atkinsporadic/hecke_check.gp`).
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic
open PowerSeries
open MockTheta5.JTP (qfacInf partitionGF)

/-- `d = (Q² − 1) j / 24`, the shift `m ↦ Q² m` in the `N`-index. -/
def hshift (Q j : ℕ) : ℕ := (Q ^ 2 - 1) * j / 24

section Op
variable {R : Type*} [CommRing R]

/-- `T(Q²)` in weight `λ + 1/2` on the `N`-indexed coefficients of `G/η^j`, with middle sign `s`. -/
noncomputable def heckeHalf (Q : ℕ) [Fact Q.Prime] (j lam : ℕ) (s : ℤ) (c : PowerSeries R) :
    PowerSeries R :=
  PowerSeries.mk fun N =>
    (if hshift Q j ≤ Q ^ 2 * N then coeff (Q ^ 2 * N - hshift Q j) c else 0)
    + ((s * legendreSym Q (24 * (N : ℤ) - j) * (Q : ℤ) ^ (lam - 1) : ℤ) : R) * coeff N c
    + (if Q ^ 2 ∣ N + hshift Q j then ((Q : R) ^ (2 * lam - 1)) * coeff ((N + hshift Q j) / Q ^ 2) c
        else 0)

lemma coeff_heckeHalf (Q : ℕ) [Fact Q.Prime] (j lam : ℕ) (s : ℤ) (c : PowerSeries R) (N : ℕ) :
    coeff N (heckeHalf Q j lam s c) =
      (if hshift Q j ≤ Q ^ 2 * N then coeff (Q ^ 2 * N - hshift Q j) c else 0)
      + ((s * legendreSym Q (24 * (N : ℤ) - j) * (Q : ℤ) ^ (lam - 1) : ℤ) : R) * coeff N c
      + (if Q ^ 2 ∣ N + hshift Q j then ((Q : R) ^ (2 * lam - 1)) * coeff ((N + hshift Q j) / Q ^ 2) c
          else 0) := by
  rw [heckeHalf, coeff_mk]

lemma map_heckeHalf {S : Type*} [CommRing S] (φ : R →+* S) (Q : ℕ) [Fact Q.Prime] (j lam : ℕ)
    (s : ℤ) (c : PowerSeries R) :
    PowerSeries.map φ (heckeHalf Q j lam s c) = heckeHalf Q j lam s (PowerSeries.map φ c) := by
  ext N
  rw [coeff_map, coeff_heckeHalf, coeff_heckeHalf]
  simp only [map_add, map_mul, apply_ite φ, map_zero, map_intCast, map_pow, map_natCast, coeff_map]

lemma heckeHalf_sub (Q : ℕ) [Fact Q.Prime] (j lam : ℕ) (s : ℤ) (c d : PowerSeries R) :
    heckeHalf Q j lam s (c - d) = heckeHalf Q j lam s c - heckeHalf Q j lam s d := by
  ext N
  simp only [coeff_heckeHalf, map_sub]
  split_ifs <;> ring

lemma heckeHalf_C_mul (Q : ℕ) [Fact Q.Prime] (j lam : ℕ) (s : ℤ) (x : R) (c : PowerSeries R) :
    heckeHalf Q j lam s (C x * c) = C x * heckeHalf Q j lam s c := by
  ext N
  simp only [coeff_heckeHalf, coeff_C_mul]
  split_ifs <;> ring

end Op

/-- The middle sign `χ₁₂(Q)·((−1)^λ / Q)`. -/
def heckeSign (Q : ℕ) [Fact Q.Prime] (lam : ℕ) : ℤ := legendreSym Q 12 * legendreSym Q ((-1) ^ lam)

/-- **Hypothesis (classical, not proved here).** For a prime `Q ≥ 5`, `T(Q²)` maps
`G/η^j`, `G ∈ S_k(SL₂(ℤ))` with integral q-expansion, to `G'/η^j` with `G' ∈ S_k(SL₂(ℤ))` integral.
Here `λ = k − (j+1)/2`. In q-series: `heckeHalf (G · P^j) = G' · P^j`, `P = Σ p(n) qⁿ`. -/
def EtaHecke (Q : ℕ) [Fact Q.Prime] (k j : ℕ) : Prop :=
  ∀ a : PowerSeries ℤ, BoylanWebb.IntForm (k : ℤ) a → constantCoeff a = 0 →
    ∃ a' : PowerSeries ℤ, BoylanWebb.IntForm (k : ℤ) a' ∧ constantCoeff a' = 0 ∧
      heckeHalf Q j (k - (j + 1) / 2) (heckeSign Q (k - (j + 1) / 2)) (a * partitionGF ^ j) =
        a' * partitionGF ^ j

/-- **Weaker hypothesis**: the same stability, only modulo `ℓ`. It follows from `EtaHecke`
(`EtaHecke.toMod`) and is all the congruence proofs use. -/
def EtaHeckeMod (ℓ Q : ℕ) [Fact Q.Prime] (k j : ℕ) : Prop :=
  ∀ a : PowerSeries ℤ, BoylanWebb.IntForm (k : ℤ) a → constantCoeff a = 0 →
    ∃ a' : PowerSeries ℤ, BoylanWebb.IntForm (k : ℤ) a' ∧ constantCoeff a' = 0 ∧
      heckeHalf Q j (k - (j + 1) / 2) (heckeSign Q (k - (j + 1) / 2))
          (BoylanWebb.Ψ ℓ (a * partitionGF ^ j)) = BoylanWebb.Ψ ℓ (a' * partitionGF ^ j)

theorem EtaHecke.toMod {Q : ℕ} [Fact Q.Prime] {k j : ℕ} (ℓ : ℕ) (H : EtaHecke Q k j) :
    EtaHeckeMod ℓ Q k j := by
  intro a ha h0
  obtain ⟨a', ha', h0', hT⟩ := H a ha h0
  exact ⟨a', ha', h0', by rw [← map_heckeHalf, hT]⟩

/-! ### Evaluating Legendre symbols by Euler's criterion -/

/-- If `a^((p−1)/2) ≡ r (mod p)` with `r ∈ {−1, 0, 1}`, then `(a/p) = r`. -/
lemma legendreSym_eq_of_pow (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a r : ℤ) (hr : r = -1 ∨ r = 0 ∨ r = 1)
    (h : (a : ZMod p) ^ (p / 2) = (r : ZMod p)) : legendreSym p a = r := by
  have he := legendreSym.eq_pow p a
  rw [h] at he
  have hL : legendreSym p a = -1 ∨ legendreSym p a = 0 ∨ legendreSym p a = 1 := by
    by_cases h0 : (a : ZMod p) = 0
    · exact Or.inr (Or.inl ((legendreSym.eq_zero_iff p a).mpr h0))
    · rcases legendreSym.eq_one_or_neg_one p h0 with h1 | h1
      · exact Or.inr (Or.inr h1)
      · exact Or.inl h1
  have hinj : ∀ x y : ℤ, (x = -1 ∨ x = 0 ∨ x = 1) → (y = -1 ∨ y = 0 ∨ y = 1) →
      (x : ZMod p) = (y : ZMod p) → x = y := by
    intro x y hx hy hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
    have hle : (y - x).natAbs < p := by omega
    have hdvd := Int.natAbs_dvd_natAbs.mpr hxy
    simp only [Int.natAbs_natCast] at hdvd
    have : (y - x).natAbs = 0 := by
      by_contra hne
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (by omega)
    omega
  exact hinj _ _ hL hr he

/-- Euler's criterion as a computable formula. -/
lemma legendreSym_val (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ℤ) :
    legendreSym p a = if (a : ZMod p) ^ (p / 2) = 1 then 1
      else if (a : ZMod p) ^ (p / 2) = -1 then -1 else 0 := by
  have he := legendreSym.eq_pow p a
  have h1 : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) = 1 - (-1) := by ring
      push_cast; rw [this, ← h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  split_ifs with ha hb
  · exact legendreSym_eq_of_pow p hp a 1 (by simp) (by rw [ha]; simp)
  · exact legendreSym_eq_of_pow p hp a (-1) (by simp) (by rw [hb]; simp)
  · by_cases h0 : (a : ZMod p) = 0
    · exact (legendreSym.eq_zero_iff p a).mpr h0
    · exfalso
      rcases legendreSym.eq_one_or_neg_one p h0 with h | h
      · rw [h] at he; exact ha (by rw [← he]; simp)
      · rw [h] at he; exact hb (by rw [← he]; simp)

end RamanujanTau.AtkinSporadic
