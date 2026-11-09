/-
# Entry 3.33 (Bressoud; Berndt et al. §32, second proof)

`{G(q)G(q⁵⁴) + q¹¹H(q)H(q⁵⁴)}·χ(−q)χ(−q⁹) = {G(q²⁷)H(q²) − q⁵G(q²)H(q²⁷)}·χ(−q³)χ(−q²⁷)`,
i.e. Ramanujan's (3.41) with the denominators cleared.

Berndt et al.'s second proof, with `g(q) = f(−q)G(q)`, `h(q) = f(−q)H(q)`:
* Entries 3.6, 3.7, 3.8 in `g, h` form (`C6`, `C7`, `C8`) at `q`, `q²`, `q³`, `q⁶`, `q⁹`;
* two `3 × 3` eliminations (32.17)–(32.20), done here as explicit cofactor linear combinations (`hN33`, `hM33`);
* the 3-dissections `φ(−q) = φ(−q⁹) − 2qχ(−q³)ψ(q⁹)` (`d33_1`) and `ψ(q)χ(−q³) = φ(−q⁹) + qχ(−q³)ψ(q⁹)` (`d33_2`),
  from `θ_dissect` (n = 3) and `dis2`;
* `f(−q²)²χ(−q) = ψ(q)φ(−q)` and `f(−q)² = φ(−q)χ(−q)ψ(q)` (`P29`, `P30`).
Then `2qχ(−q⁹)N(q) = φ(−q³)φ(−q⁹) − φ(−q)φ(−q²⁷) = 2qχ(−q³)M(q)` (32.32), (32.34).
-/
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.E06
import RamanujanTau.Forty.E07
import RamanujanTau.Forty.E08
import RamanujanTau.Forty.NgTools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

local notation "ψ" => RamanujanTau.Septic.ramF 1 3
local notation "X" => PowerSeries.X

/-! ## `q ↦ q^a` bookkeeping -/

lemma S_comp (a b c : ℕ) [NeZero a] [NeZero b] [NeZero c] (h : a * b = c) (f : PowerSeries ℤ) :
    S a (S b f) = S c f := by
  subst h
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  ext n
  rw [coeff_S, coeff_S, coeff_S]
  by_cases h1 : a ∣ n
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right a m), Nat.mul_div_cancel_left m ha]
    by_cases h2 : b ∣ m
    · obtain ⟨k, rfl⟩ := h2
      rw [if_pos (dvd_mul_right b k), if_pos (by rw [← mul_assoc]; exact dvd_mul_right _ _),
        Nat.mul_div_cancel_left k hb, ← mul_assoc, Nat.mul_div_cancel_left k (Nat.mul_pos ha hb)]
    · rw [if_neg h2, if_neg]
      intro h3
      exact h2 (Nat.dvd_of_mul_dvd_mul_left ha h3)
  · rw [if_neg h1, if_neg]
    intro h3
    exact h1 (dvd_trans (dvd_mul_right a b) h3)

lemma SX (a : ℕ) [NeZero a] : S a X = X ^ a := RankProof.Ea_X a _

lemma SP (a : ℕ) [NeZero a] (b M : ℕ) {b' M' : ℕ} (hb : 1 ≤ b) (hM33 : 1 ≤ M) (h1 : b' = a * b) (h2 : M' = a * M) :
    S a (Pinf b M) = Pinf b' M' := by
  subst h1 h2; exact S_Pinf a b M hb hM33

/-! ## Entries 3.6, 3.7, 3.8 with `f(−q^a)` cleared -/

/-- 3.6: `g(q)g(q⁹) + q²h(q)h(q⁹) = f(−q³)²`. -/
lemma C6 : (G * Pinf 1 1) * (S 9 G * Pinf 9 9) + X ^ 2 * (H * Pinf 1 1) * (S 9 H * Pinf 9 9) = Pinf 3 3 ^ 2 := by
  have e := entry_3_6
  have hu : IsUnit (fm 1 * fm 9) := (isUnit_Pinf 1 1 le_rfl le_rfl).mul (isUnit_Pinf 9 9 (by norm_num) (by norm_num))
  have hi := Ring.inverse_mul_cancel _ hu
  simp only [fm] at e hi
  linear_combination (Pinf 1 1 * Pinf 9 9) * e + Pinf 3 3 ^ 2 * hi

/-- 3.7: `g(q²)g(q³) + qh(q²)h(q³) = ψ(q)φ(−q³)`. -/
lemma C7 : (S 2 G * Pinf 2 2) * (S 3 G * Pinf 3 3) + X * (S 2 H * Pinf 2 2) * (S 3 H * Pinf 3 3) = ψ * J 3 6 := by
  have e := entry_3_7
  have hu : IsUnit (chim 1) := isUnit_Pinf 1 2 le_rfl (by norm_num)
  have hi := Ring.inverse_mul_cancel _ hu
  have hp := psi_mul
  have a3 := atom 3 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a3
  norm_num at a3
  have hsp := E1_split
  have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a2
  norm_num at a2
  simp only [chim, Nat.reduceMul] at e hi
  simp only [J, Nat.reduceSub]
  rw [a3]
  linear_combination (Pinf 2 2 * Pinf 3 6 * Pinf 6 6) * e - Pinf 3 6 ^ 2 * Pinf 6 6 * Ring.inverse (Pinf 1 2) * hp
    + Pinf 3 6 ^ 2 * Pinf 6 6 * ψ * hi

/-- 3.8: `g(q⁶)h(q) − qg(q)h(q⁶) = φ(−q)ψ(q³)`. -/
lemma C8 : (S 6 G * Pinf 6 6) * (H * Pinf 1 1) - X * (G * Pinf 1 1) * (S 6 H * Pinf 6 6) = J 1 2 * S 3 ψ := by
  have e := entry_3_8
  have hu : IsUnit (chim 3) := isUnit_Pinf 3 6 (by norm_num) (by norm_num)
  have hi := Ring.inverse_mul_cancel _ hu
  have hp := congrArg (S 3) psi_mul
  rw [map_mul, SP 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2),
    SP 3 2 2 (by norm_num) (by norm_num) (rfl : 6 = 3 * 2) (rfl : 6 = 3 * 2)] at hp
  have hsp := E1_split
  simp only [chim, Nat.reduceMul] at e hi
  simp only [J, Nat.reduceSub]
  rw [hsp]
  linear_combination (Pinf 6 6 * Pinf 1 2 * Pinf 2 2) * e - Pinf 1 2 ^ 2 * Pinf 2 2 * Ring.inverse (Pinf 3 6) * hp
    + Pinf 1 2 ^ 2 * Pinf 2 2 * S 3 ψ * hi

/-! ## the instances needed at `q², q³, q⁶, q⁹` -/

lemma C6_2 : (S 2 G * Pinf 2 2) * (S 18 G * Pinf 18 18) + X ^ 4 * (S 2 H * Pinf 2 2) * (S 18 H * Pinf 18 18) =
    Pinf 6 6 ^ 2 := by
  have h := congrArg (S 2) C6
  simp only [map_mul, map_add, map_pow, SX, S_comp 2 9 18 rfl, SP 2 1 1 le_rfl le_rfl rfl rfl,
    SP 2 9 9 (by norm_num) (by norm_num) (rfl : 18 = 2 * 9) rfl, SP 2 3 3 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) rfl] at h
  linear_combination h

lemma C6_3 : (S 3 G * Pinf 3 3) * (S 27 G * Pinf 27 27) + X ^ 6 * (S 3 H * Pinf 3 3) * (S 27 H * Pinf 27 27) =
    Pinf 9 9 ^ 2 := by
  have h := congrArg (S 3) C6
  simp only [map_mul, map_add, map_pow, SX, S_comp 3 9 27 rfl, SP 3 1 1 le_rfl le_rfl rfl rfl,
    SP 3 9 9 (by norm_num) (by norm_num) (rfl : 27 = 3 * 9) rfl, SP 3 3 3 (by norm_num) (by norm_num) (rfl : 9 = 3 * 3) rfl] at h
  linear_combination h

lemma C6_6 : (S 6 G * Pinf 6 6) * (S 54 G * Pinf 54 54) + X ^ 12 * (S 6 H * Pinf 6 6) * (S 54 H * Pinf 54 54) =
    Pinf 18 18 ^ 2 := by
  have h := congrArg (S 6) C6
  simp only [map_mul, map_add, map_pow, SX, S_comp 6 9 54 rfl, SP 6 1 1 le_rfl le_rfl rfl rfl,
    SP 6 9 9 (by norm_num) (by norm_num) (rfl : 54 = 6 * 9) rfl, SP 6 3 3 (by norm_num) (by norm_num) (rfl : 18 = 6 * 3) rfl] at h
  linear_combination h

lemma C7_3 : (S 6 G * Pinf 6 6) * (S 9 G * Pinf 9 9) + X ^ 3 * (S 6 H * Pinf 6 6) * (S 9 H * Pinf 9 9) =
    S 3 ψ * J 9 18 := by
  have h := congrArg (S 3) C7
  simp only [map_mul, map_add, map_pow, SX, S_comp 3 2 6 rfl, S_comp 3 3 9 rfl,
    SP 3 2 2 (by norm_num) (by norm_num) (rfl : 6 = 3 * 2) rfl, SP 3 3 3 (by norm_num) (by norm_num) (rfl : 9 = 3 * 3) rfl,
    S_J' 3 3 6 (by norm_num) (by norm_num) (rfl : 9 = 3 * 3) (rfl : 18 = 3 * 6)] at h
  linear_combination h

lemma C7_9 : (S 18 G * Pinf 18 18) * (S 27 G * Pinf 27 27) + X ^ 9 * (S 18 H * Pinf 18 18) * (S 27 H * Pinf 27 27) =
    S 9 ψ * J 27 54 := by
  have h := congrArg (S 9) C7
  simp only [map_mul, map_add, map_pow, SX, S_comp 9 2 18 rfl, S_comp 9 3 27 rfl,
    SP 9 2 2 (by norm_num) (by norm_num) (rfl : 18 = 9 * 2) rfl, SP 9 3 3 (by norm_num) (by norm_num) (rfl : 27 = 9 * 3) rfl,
    S_J' 9 3 6 (by norm_num) (by norm_num) (rfl : 27 = 9 * 3) (rfl : 54 = 9 * 6)] at h
  linear_combination h

lemma C8_3 : (S 18 G * Pinf 18 18) * (S 3 H * Pinf 3 3) - X ^ 3 * (S 3 G * Pinf 3 3) * (S 18 H * Pinf 18 18) =
    J 3 6 * S 9 ψ := by
  have h := congrArg (S 3) C8
  simp only [map_mul, map_sub, map_pow, SX, S_comp 3 6 18 rfl, S_comp 3 3 9 rfl,
    SP 3 6 6 (by norm_num) (by norm_num) (rfl : 18 = 3 * 6) rfl, SP 3 1 1 le_rfl le_rfl rfl rfl,
    S_J' 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2)] at h
  linear_combination h

lemma C8_9 : (S 54 G * Pinf 54 54) * (S 9 H * Pinf 9 9) - X ^ 9 * (S 9 G * Pinf 9 9) * (S 54 H * Pinf 54 54) =
    J 9 18 * S 27 ψ := by
  have h := congrArg (S 9) C8
  simp only [map_mul, map_sub, map_pow, SX, S_comp 9 6 54 rfl, S_comp 9 3 27 rfl,
    SP 9 6 6 (by norm_num) (by norm_num) (rfl : 54 = 9 * 6) rfl, SP 9 1 1 le_rfl le_rfl rfl rfl,
    S_J' 9 1 2 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 18 = 9 * 2)] at h
  linear_combination h

/-! ## the two eliminations (32.17)–(32.20) -/

/-- (32.19): `N(q)ψ(q³)φ(−q⁹) = f(−q¹⁸)²f(−q³)² − q²φ(−q⁹)ψ(q²⁷)ψ(q³)φ(−q)`. -/
lemma hN33 : ((G * Pinf 1 1) * (S 54 G * Pinf 54 54) + X ^ 11 * (H * Pinf 1 1) * (S 54 H * Pinf 54 54)) *
      S 3 ψ * J 9 18 = Pinf 18 18 ^ 2 * Pinf 3 3 ^ 2 - X ^ 2 * J 9 18 * S 27 ψ * S 3 ψ * J 1 2 := by
  linear_combination
    (-((G * Pinf 1 1) * (S 54 G * Pinf 54 54) + X ^ 11 * (H * Pinf 1 1) * (S 54 H * Pinf 54 54))) * C7_3
    + Pinf 3 3 ^ 2 * C6_6
    + ((S 6 G * Pinf 6 6) * (S 54 G * Pinf 54 54) + X ^ 12 * (S 6 H * Pinf 6 6) * (S 54 H * Pinf 54 54)) * C6
    - X ^ 2 * ((S 54 G * Pinf 54 54) * (S 9 H * Pinf 9 9) - X ^ 9 * (S 9 G * Pinf 9 9) * (S 54 H * Pinf 54 54)) * C8
    - X ^ 2 * (S 3 ψ * J 1 2) * C8_9

/-- (32.20): `qM(q)ψ(q⁹)φ(−q³) = ψ(q⁹)φ(−q²⁷)ψ(q)φ(−q³) − f(−q⁹)²f(−q⁶)²`. -/
lemma hM33 : X * ((S 2 H * Pinf 2 2) * (S 27 G * Pinf 27 27) - X ^ 5 * (S 2 G * Pinf 2 2) * (S 27 H * Pinf 27 27)) *
      S 9 ψ * J 3 6 = S 9 ψ * J 27 54 * ψ * J 3 6 - Pinf 9 9 ^ 2 * Pinf 6 6 ^ 2 := by
  linear_combination
    (-(X * ((S 2 H * Pinf 2 2) * (S 27 G * Pinf 27 27) - X ^ 5 * (S 2 G * Pinf 2 2) * (S 27 H * Pinf 27 27)))) * C8_3
    + (ψ * J 3 6) * C7_9
    + ((S 18 G * Pinf 18 18) * (S 27 G * Pinf 27 27) + X ^ 9 * (S 18 H * Pinf 18 18) * (S 27 H * Pinf 27 27)) * C7
    - Pinf 9 9 ^ 2 * C6_2
    - ((S 2 G * Pinf 2 2) * (S 18 G * Pinf 18 18) + X ^ 4 * (S 2 H * Pinf 2 2) * (S 18 H * Pinf 18 18)) * C6_3

/-! ## the 3-dissections (32.23)–(32.28) -/

/-- the 3-dissection `θ_N(e,c) = θ_{9N}(3N+3e,c³) + t^{N−e}(−c⁻¹)θ_{9N}(3e,c³) + t^{3N−2e}c⁻²θ_{9N}(3e−3N,c³)`. -/
lemma dis3 {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : M = N * 3 * 3) (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hN e c = θ hM (3 * N + 3 * e) (c ^ 3) + mono (N - e) (-c⁻¹) * θ hM (3 * e) (c ^ 3)
      + mono (3 * N - 2 * e) (c⁻¹ ^ 2) * θ hM (3 * e - 3 * N) (c ^ 3) := by
  rw [θ_dissect hN 3 (by norm_num) e hc, Fin.sum_univ_three]
  simp only [θ_N' hMN.symm _ hM]
  have h1 : c2 (-((0 : Fin 3) : ℕ) : ℤ) = 0 := by simp [c2]
  have h2 : c2 (-((1 : Fin 3) : ℕ) : ℤ) = 1 := by simp [c2]
  have h3 : c2 (-((2 : Fin 3) : ℕ) : ℤ) = 3 := by simp [c2]
  have h4 : c2 3 = 3 := by simp [c2]
  rw [h1, h2, h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, h4]
  have m0 : (mono ((N : ℤ) * 0 - e * 0) ((-1) ^ (-((0 : ℕ) : ℤ)) * c ^ (-((0 : ℕ) : ℤ))) : L) = 1 := by
    simp [mono]
  simp only [Nat.cast_zero] at m0
  rw [m0, one_mul]
  congr 1
  · congr 1
    · exact θ_cg' _ (by ring) (by ring)
    · congr 1
      · exact mono_ext (by ring) (by rw [zpow_neg, zpow_neg, zpow_one, zpow_one]; field_simp)
      · exact θ_cg' _ (by ring) (by ring)
  · congr 1
    · exact mono_ext (by ring) (by rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat, inv_pow]; norm_num)
    · exact θ_cg' _ (by ring) (by ring)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm4 : 1 ≤ 4 := by norm_num
private lemma hm9 : 1 ≤ 9 := by norm_num
private lemma hm18 : 1 ≤ 18 := by norm_num
private lemma hm36 : 1 ≤ 36 := by norm_num

/-- `φ(−q) = φ(−q⁹) − 2qf(−q³,−q¹⁵)` in `ℂ((t))`. -/
lemma T33_1 : θ hm2 1 1 = θ hm18 9 1 - 2 * mono 1 1 * θ hm18 3 1 := by
  rw [dis3 hm2 hm18 rfl 1 one_ne_zero]
  norm_num
  rw [θ_nfr1 hm18 3 (-1) (-3) (-1) (e := (-3)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num
  ring

/-- `ψ(q) = f(q³,q⁶) + qψ(q⁹)` in `ℂ((t))`. -/
lemma T33_2 : θ hm4 1 (-1) = θ hm9 3 (-1) + mono 1 1 * θ hm36 9 (-1) := by
  rw [dis3 hm4 hm36 rfl 1 (by norm_num : (-1 : ℂ) ≠ 0),
    dis2 hm9 hm36 rfl 3 (by norm_num : (-1 : ℂ) ≠ 0) 15 (-3) 6 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  norm_num
  rw [θ_nfrm hm36 9 (-1) (-9) 1 (e := (-9)) (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_nfrm hm36 3 (-1) (-3) 1 (e := (-3)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, ← mul_assoc,
    mono_mul, mono_mul]
  norm_num

private lemma ι_ne33 {f : PowerSeries ℤ} (h : f ≠ 0) : ι f ≠ 0 := fun h0 => h (ι_inj (h0.trans (map_zero ι).symm))

private lemma J_ne33 (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- `f(q^e, q^{N−e}) = x` once `x J_{e,N} = J_{2e,2N} J_{N,2N}`. -/
private lemma θm33 {N : ℕ} (h : 1 ≤ N) (e : ℕ) {e' : ℤ} (he' : e' = e) (he : 1 ≤ e) (heN : e < N) (x : PowerSeries ℤ)
    (hx : x * J e N = J (2 * e) (2 * N) * J N (2 * N)) : θ h e' (-1) = ι x := by
  have hb := θ_bar h e he heN
  rw [he']
  apply mul_right_cancel₀ (ι_ne33 (J_ne33 e N he heN))
  rw [hb, ← map_mul, hx]

lemma psiJ : ψ * J 1 4 = J 2 8 * J 4 8 := by
  have h1 := psi_prod1
  have h2 := psi_mul
  apply mul_left_cancel₀ (Pinf_ne 1 2 le_rfl (by norm_num))
  linear_combination -h1 + J 1 4 * h2

lemma S9ψ_mul : S 9 ψ * Pinf 9 18 = Pinf 18 18 := by
  have h := congrArg (S 9) psi_mul
  rwa [map_mul, SP 9 1 2 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 18 = 9 * 2),
    SP 9 2 2 (by norm_num) (by norm_num) (rfl : 18 = 9 * 2) rfl] at h

lemma S3ψ_mul : S 3 ψ * Pinf 3 6 = Pinf 6 6 := by
  have h := congrArg (S 3) psi_mul
  rwa [map_mul, SP 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2),
    SP 3 2 2 (by norm_num) (by norm_num) (rfl : 6 = 3 * 2) rfl] at h

lemma S27ψ_mul : S 27 ψ * Pinf 27 54 = Pinf 54 54 := by
  have h := congrArg (S 27) psi_mul
  rwa [map_mul, SP 27 1 2 le_rfl (by norm_num) (rfl : 27 = 27 * 1) (rfl : 54 = 27 * 2),
    SP 27 2 2 (by norm_num) (by norm_num) (rfl : 54 = 27 * 2) rfl] at h

/-- (32.25): `φ(−q) = φ(−q⁹) − 2qχ(−q³)ψ(q⁹)`. -/
lemma d33_1 : J 1 2 = J 9 18 - 2 * X * (Pinf 3 6 * S 9 ψ) := by
  have h := T33_1
  rw [θu' hm2 1 (e' := 1) (by norm_num) le_rfl (by norm_num), θu' hm18 9 (e' := 9) (by norm_num) (by norm_num) (by norm_num),
    θu' hm18 3 (e' := 3) (by norm_num) (by norm_num) (by norm_num)] at h
  have hJ : J 3 18 = Pinf 3 6 * S 9 ψ := by
    have a := atom 3 6 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at a
    norm_num at a
    simp only [J, Nat.reduceSub]
    rw [a]
    linear_combination (-(Pinf 3 18 * Pinf 15 18)) * S9ψ_mul
  rw [← hJ]
  apply ι_inj
  simp only [map_sub, map_mul, map_ofNat, ι_X]
  exact h

/-- (32.26) times `χ(−q³)`: `ψ(q)χ(−q³) = φ(−q⁹) + qχ(−q³)ψ(q⁹)`. -/
lemma d33_2 : ψ * Pinf 3 6 = J 9 18 + X * (Pinf 3 6 * S 9 ψ) := by
  have h := T33_2
  have i1 := θm33 hm4 1 (e' := 1) (by norm_num) le_rfl (by norm_num) ψ psiJ
  have i2 : θ hm36 9 (-1) = ι (S 9 ψ) := by
    refine θm33 hm36 9 (by norm_num) (by norm_num) (by norm_num) _ ?_
    have h9 := congrArg (S 9) psiJ
    simp only [map_mul, S_J' 9 1 4 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 36 = 9 * 4),
      S_J' 9 2 8 (by norm_num) (by norm_num) (rfl : 18 = 9 * 2) (rfl : 72 = 9 * 8),
      S_J' 9 4 8 (by norm_num) (by norm_num) (rfl : 36 = 9 * 4) (rfl : 72 = 9 * 8)] at h9
    exact h9
  have i3 : θ hm9 3 (-1) * ι (Pinf 3 6) = ι (J 9 18) := by
    have hb := θ_bar hm9 3 (by norm_num) (by norm_num)
    have k : J 3 9 = J 6 18 * Pinf 3 6 := by
      simp only [J, Nat.reduceSub]
      simp (disch := norm_num) only [atom _ _ 18]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
        add_zero, mul_one]
      ring
    norm_num at hb
    rw [k, map_mul] at hb
    apply mul_right_cancel₀ (ι_ne33 (J_ne33 6 18 (by norm_num) (by norm_num)))
    linear_combination hb
  rw [i1, i2] at h
  apply ι_inj
  simp only [map_add, map_mul, ι_X]
  rw [h, ← i3]
  ring

/-! ## (32.29), (32.30) -/

lemma P29 (k : ℕ) [NeZero k] (hk : S k ψ * Pinf k (2 * k) = Pinf (2 * k) (2 * k)) :
    Pinf (2 * k) (2 * k) ^ 2 * Pinf k (2 * k) = S k ψ * J k (2 * k) := by
  simp only [J, show 2 * k - k = k by omega]
  linear_combination (-(Pinf k (2 * k) * Pinf (2 * k) (2 * k))) * hk

lemma P30 (k : ℕ) [NeZero k] (hk : S k ψ * Pinf k (2 * k) = Pinf (2 * k) (2 * k)) :
    Pinf k k ^ 2 = J k (2 * k) * Pinf k (2 * k) * S k ψ := by
  have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hs := RankProof.Pinf_split k k h1 h1
  rw [show k + k = 2 * k by ring] at hs
  simp only [J, show 2 * k - k = k by omega]
  rw [hs]
  linear_combination (-(Pinf k (2 * k) ^ 2 * Pinf (2 * k) (2 * k))) * hk

/-! ## (32.31)–(32.34) and Entry 3.33 -/

lemma d33_1_3 : J 3 6 = J 27 54 - 2 * X ^ 3 * (Pinf 9 18 * S 27 ψ) := by
  have h := congrArg (S 3) d33_1
  simp only [map_mul, map_sub, map_ofNat, SX, S_comp 3 9 27 rfl, SP 3 3 6 (by norm_num) (by norm_num) (rfl : 9 = 3 * 3)
    (rfl : 18 = 3 * 6), S_J' 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2),
    S_J' 3 9 18 (by norm_num) (by norm_num) (rfl : 27 = 3 * 9) (rfl : 54 = 3 * 18)] at h
  exact h

lemma d33_2_3 : S 3 ψ * Pinf 9 18 = J 27 54 + X ^ 3 * (Pinf 9 18 * S 27 ψ) := by
  have h := congrArg (S 3) d33_2
  simp only [map_mul, map_add, SX, S_comp 3 9 27 rfl, SP 3 3 6 (by norm_num) (by norm_num) (rfl : 9 = 3 * 3)
    (rfl : 18 = 3 * 6), S_J' 3 9 18 (by norm_num) (by norm_num) (rfl : 27 = 3 * 9) (rfl : 54 = 3 * 18)] at h
  exact h

private lemma Sψ_ne {x : PowerSeries ℤ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : x * Pinf a b = Pinf b b) : x ≠ 0 := by
  rintro rfl; rw [zero_mul] at h; exact Pinf_ne b b hb hb h.symm

/-- (32.32) and (32.34): `2qχ(−q⁹)N(q) = φ(−q³)φ(−q⁹) − φ(−q)φ(−q²⁷) = 2qχ(−q³)M(q)`. -/
theorem NM33 : Pinf 9 18 * ((G * Pinf 1 1) * (S 54 G * Pinf 54 54) + X ^ 11 * (H * Pinf 1 1) * (S 54 H * Pinf 54 54)) =
    Pinf 3 6 * ((S 2 H * Pinf 2 2) * (S 27 G * Pinf 27 27) - X ^ 5 * (S 2 G * Pinf 2 2) * (S 27 H * Pinf 27 27)) := by
  have p29_9 := P29 9 S9ψ_mul
  have p29_3 := P29 3 S3ψ_mul
  have p30_9 := P30 9 S9ψ_mul
  have p30_3 := P30 3 S3ψ_mul
  simp only [Nat.reduceMul] at p29_9 p29_3 p30_9 p30_3
  have hψ3 := Sψ_ne (by norm_num) (by norm_num) S3ψ_mul
  have hψ9 := Sψ_ne (by norm_num) (by norm_num) S9ψ_mul
  have h31 : Pinf 9 18 * ((G * Pinf 1 1) * (S 54 G * Pinf 54 54) + X ^ 11 * (H * Pinf 1 1) * (S 54 H * Pinf 54 54)) =
      Pinf 3 6 * J 3 6 * S 9 ψ - X ^ 2 * S 27 ψ * Pinf 9 18 * J 1 2 := by
    apply mul_right_cancel₀ (mul_ne_zero hψ3 (J_ne33 9 18 (by norm_num) (by norm_num)))
    linear_combination Pinf 9 18 * hN33 + Pinf 3 3 ^ 2 * p29_9 + (S 9 ψ * J 9 18) * p30_3
  have h33 : X * Pinf 3 6 * ((S 2 H * Pinf 2 2) * (S 27 G * Pinf 27 27) - X ^ 5 * (S 2 G * Pinf 2 2) * (S 27 H * Pinf 27 27)) =
      Pinf 3 6 * J 27 54 * ψ - S 3 ψ * Pinf 9 18 * J 9 18 := by
    apply mul_right_cancel₀ (mul_ne_zero hψ9 (J_ne33 3 6 (by norm_num) (by norm_num)))
    linear_combination Pinf 3 6 * hM33 - Pinf 9 9 ^ 2 * p29_3 - (S 3 ψ * J 3 6) * p30_9
  have h32 : 2 * X * (Pinf 9 18 * ((G * Pinf 1 1) * (S 54 G * Pinf 54 54) + X ^ 11 * (H * Pinf 1 1) * (S 54 H * Pinf 54 54))) =
      J 3 6 * J 9 18 - J 1 2 * J 27 54 := by
    linear_combination 2 * X * h31 + J 3 6 * d33_1 - J 1 2 * d33_1_3
  have h34 : 2 * (X * Pinf 3 6 * ((S 2 H * Pinf 2 2) * (S 27 G * Pinf 27 27) - X ^ 5 * (S 2 G * Pinf 2 2) * (S 27 H * Pinf 27 27))) =
      J 3 6 * J 9 18 - J 1 2 * J 27 54 := by
    linear_combination 2 * h33 + 2 * J 27 54 * d33_2 - 2 * J 9 18 * d33_2_3 + J 27 54 * d33_1 - J 9 18 * d33_1_3
  apply mul_left_cancel₀ (mul_ne_zero two_ne PowerSeries.X_ne_zero)
  linear_combination h32 - h34

/-- **Entry 3.33** (Bressoud; Berndt et al. §32), denominators cleared:
`{G(q)G(q⁵⁴) + q¹¹H(q)H(q⁵⁴)} χ(−q)χ(−q⁹) = {G(q²⁷)H(q²) − q⁵G(q²)H(q²⁷)} χ(−q³)χ(−q²⁷)`. -/
theorem entry_3_33 : (G * S 54 G + X ^ 11 * H * S 54 H) * (chim 1 * chim 9) =
    (S 27 G * S 2 H - X ^ 5 * S 2 G * S 27 H) * (chim 3 * chim 27) := by
  have fin := NM33
  have hsp := E1_split
  have hsp27 := congrArg (S 27) E1_split
  rw [map_mul, SP 27 1 1 le_rfl le_rfl rfl rfl, SP 27 1 2 le_rfl (by norm_num) rfl (rfl : 54 = 27 * 2),
    SP 27 2 2 (by norm_num) (by norm_num) (rfl : 54 = 27 * 2) rfl] at hsp27
  simp only [chim, Nat.reduceMul]
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 54 54 (by norm_num) (by norm_num)))
  linear_combination fin - Pinf 9 18 * (G * S 54 G + X ^ 11 * H * S 54 H) * Pinf 54 54 * hsp
    + Pinf 3 6 * (S 27 G * S 2 H - X ^ 5 * S 2 G * S 27 H) * Pinf 2 2 * hsp27

/-- Entry 3.33 in Ramanujan's quotient form: `K/L = χ(−q³)χ(−q²⁷)/(χ(−q)χ(−q⁹))`. -/
theorem entry_3_33' : G * S 54 G + X ^ 11 * H * S 54 H =
    (S 27 G * S 2 H - X ^ 5 * S 2 G * S 27 H) * (chim 3 * chim 27) * Ring.inverse (chim 1 * chim 9) :=
  eq_mul_inv_of ((isUnit_Pinf 1 2 le_rfl (by norm_num)).mul (isUnit_Pinf 9 18 (by norm_num) (by norm_num))) entry_3_33

end Forty
