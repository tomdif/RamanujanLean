/-
# Entry 3.21: `G(q)H(−q) − G(−q)H(q) = 2qψ(q¹⁰)/f(−q²)` (Watson 1933)

Watson's argument (Berndt et al. §24). Entries 3.2 and 3.3 at `q` and `−q` express `G, qH, G(−q), qH(−q)` through
`φ(±q), φ(±q⁵)`, `G(q⁴)` and `H(q⁴)`. Then `φ(q)φ(−q) = φ(−q²)²`, and Lemma 7.1 at `q ↦ −q²` finishes the computation.
-/
import RamanujanTau.Forty.NgTools

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf isUnit_Pinf)

local notation "φ" => RamanujanTau.Septic.phi
local notation "ψ" => RamanujanTau.Septic.ramF 1 3

private lemma at2 (b a M : ℕ) (hb : 1 ≤ b) (ha : a < M) (hd : a ∣ M) (ha1 : 1 ≤ a) (hk : M / a = 2) :
    Pinf b a = Pinf b M * Pinf (b + a) M := by
  rw [atom b a M hb ha hd ha1, hk]; simp [prod_range_succ]

lemma nE (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) {b' a' : ℕ} (h1 : b' = 2 * b) (h2 : a' = 2 * a) :
    Ng (Pinf b' a') = Pinf b' a' := by subst h1 h2; exact Ng_Pinf_even b a hb ha

lemma S5_chip1 : S 5 (chip 1) = chip 5 := by rw [chip, S_one]; rfl

lemma Ng_E5 : Ng (Pinf 5 5) = Pinf 10 10 * chip 5 := by
  have h := Ng_S5 (Pinf 1 1)
  rw [S_Pinf 5 1 1 le_rfl le_rfl, Ng_E1, map_mul, S_Pinf 5 2 2 (by norm_num) (by norm_num), S5_chip1] at h
  exact h

lemma Ng_phi5 : Ng (S 5 φ) = Pinf 5 10 ^ 2 * Pinf 10 10 := by
  rw [Ng_S5, Ng_phi, map_mul, map_pow, S_Pinf 5 1 2 le_rfl (by norm_num), S_Pinf 5 2 2 (by norm_num) (by norm_num)]

/-- Lemma 7.1 at `q ↦ −q`, in product form. -/
lemma lemma71_neg : (Pinf 5 10 ^ 2 * Pinf 5 5 ^ 2 - Pinf 1 2 ^ 2 * Pinf 1 1 ^ 2) * Pinf 2 2 * Pinf 5 10 =
    4 * X * Pinf 10 10 * Pinf 10 10 * Pinf 1 1 := by
  have st := congrArg Ng lemma71
  simp only [map_mul, map_sub, map_pow, map_ofNat, Ng_X, Ng_E1, Ng_phi, Ng_phi5, Ng_E5,
    nE 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) rfl, nE 1 1 le_rfl le_rfl (rfl : 2 = 2 * 1) rfl,
    nE 10 10 (by norm_num) (by norm_num) (rfl : 20 = 2 * 10) rfl] at st
  have hc1 := chip_mul 1
  have hc5 := chip_mul 5
  norm_num at hc1 hc5
  have a1 := E1_split
  have a5 := at2 5 5 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a2 := at2 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a10 := at2 10 10 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at a5 a2 a10
  have hne : chip 1 * Pinf 4 4 ≠ 0 := by
    refine mul_ne_zero ?_ (Pinf_ne 4 4 (by norm_num) (by norm_num))
    intro h0; rw [h0, zero_mul] at hc1; exact Pinf_ne 2 4 (by norm_num) (by norm_num) hc1.symm
  apply mul_left_cancel₀ hne
  rw [a1, a5]
  linear_combination (-Pinf 5 10) * st
    + 4 * X * Pinf 10 10 * Pinf 2 2 * (Pinf 2 2 * Pinf 20 20 * hc5 - Pinf 10 10 * Pinf 4 4 * hc1
      - Pinf 2 2 * a10 + Pinf 10 10 * a2)

/-- **Entry 3.21** (Watson 1933): `G(q)H(−q) − G(−q)H(q) = 2qψ(q¹⁰)/f(−q²)`. -/
theorem entry_3_21 : G * Ng H - Ng G * H = 2 * X * S 10 ψ * Ring.inverse (fm 2) := by
  have hA := entry_3_2
  have hB0 := entry_3_3
  have hE2 : IsUnit (Pinf 2 2) := isUnit_Pinf 2 2 (by norm_num) (by norm_num)
  have hB : (G * S 4 G - X * H * S 4 H) * Pinf 2 2 = S 5 φ := by
    rw [hB0, fm, mul_assoc, Ring.inverse_mul_cancel _ hE2, mul_one]
  have hA' : Ng G * S 4 G - X * Ng H * S 4 H = Pinf 1 2 ^ 2 := by
    have h := congrArg Ng hA
    simp only [map_add, map_mul, map_pow, Ng_X, Ng_S_ev 4 (by norm_num), Ng_chip1] at h
    linear_combination h
  have hB' : (Ng G * S 4 G + X * Ng H * S 4 H) * Pinf 2 2 = Ng (S 5 φ) := by
    have h := congrArg Ng hB
    simp only [map_sub, map_mul, Ng_X, Ng_S_ev 4 (by norm_num), Ng_P22] at h
    linear_combination h
  have h1 : 2 * X * S 4 G * S 4 H * Pinf 2 2 ^ 2 * (G * Ng H - Ng G * H) =
      S 5 φ * Ng (S 5 φ) - chip 1 ^ 2 * Pinf 1 2 ^ 2 * Pinf 2 2 ^ 2 := by
    rw [← hB', ← hB, ← hA, ← hA']; ring
  have hc1 := chip_mul 1
  norm_num at hc1
  have h2 : S 5 φ * Ng (S 5 φ) = Pinf 10 20 ^ 2 * Pinf 10 10 ^ 2 := by
    have h : φ * Ng φ = Pinf 2 4 ^ 2 * Pinf 2 2 ^ 2 := by
      rw [Ng_phi, phi_chip]; linear_combination (Pinf 2 2 ^ 2 * (chip 1 * Pinf 1 2 + Pinf 2 4)) * hc1
    have h' := congrArg (S 5) h
    rw [map_mul, map_mul, map_pow, map_pow, S_Pinf 5 2 4 (by norm_num) (by norm_num),
      S_Pinf 5 2 2 (by norm_num) (by norm_num), ← Ng_S5] at h'
    exact h'
  have hL : (Pinf 10 20 ^ 2 * Pinf 10 10 ^ 2 - Pinf 2 4 ^ 2 * Pinf 2 2 ^ 2) * Pinf 4 4 * Pinf 10 20 =
      4 * X ^ 2 * Pinf 20 20 * Pinf 20 20 * Pinf 2 2 := by
    have h := congrArg (S 2) lemma71_neg
    simp only [map_mul, map_sub, map_pow, map_ofNat, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
      S_Pinf 2 5 10 (by norm_num) (by norm_num), S_Pinf 2 5 5 (by norm_num) (by norm_num),
      S_Pinf 2 1 2 le_rfl (by norm_num), S_Pinf 2 1 1 le_rfl le_rfl, S_Pinf 2 2 2 (by norm_num) (by norm_num),
      S_Pinf 2 10 10 (by norm_num) (by norm_num)] at h
    exact h
  have hGH4 := SGH_E 4
  norm_num at hGH4
  have hψ : S 10 ψ * Pinf 10 20 = Pinf 20 20 := by
    have h := congrArg (S 10) psi_mul
    rw [map_mul, S_Pinf 10 1 2 le_rfl (by norm_num), S_Pinf 10 2 2 (by norm_num) (by norm_num)] at h
    exact h
  apply eq_mul_inv_of hE2
  have hK : (2 * X * Pinf 20 20 * Pinf 10 20 * Pinf 2 2 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne X_ne_zero) (Pinf_ne 20 20 (by norm_num) (by norm_num)))
      (Pinf_ne 10 20 (by norm_num) (by norm_num))) (Pinf_ne 2 2 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hK
  linear_combination (Pinf 10 20 * Pinf 4 4) * h1 + (Pinf 10 20 * Pinf 4 4) * h2
    - (2 * X * Pinf 10 20 * Pinf 2 2 ^ 2 * (G * Ng H - Ng G * H)) * hGH4 + hL
    - (4 * X ^ 2 * Pinf 20 20 * Pinf 2 2) * hψ
    - (Pinf 10 20 * Pinf 2 2 ^ 2 * Pinf 4 4 * (chip 1 * Pinf 1 2 + Pinf 2 4)) * hc1

end Forty
