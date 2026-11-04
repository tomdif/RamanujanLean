import RamanujanTau.LehmerSmall.Congruences
import RamanujanTau.DiscriminantQExpansion

/-! # Refined congruences: `τ` modulo 9 and the 2-adic condition from `E₄³ = E₁₂ + (432000/691)Δ`

* `tau_mod9_all` : `256 τ(n) ≡ 160σ₇ + 176σ₉ − 320n²σ₇ + 2(σ₁ + 5σ₃ − 6nσ₁) + 6σ₁ (mod 9)`.
  This is the mod-3 identity `core3` pushed one 3-adic digit further: `Z ≡ 2S₁² + 2S₁ (mod 3)` and
  `12 S₁² = S₁ + 5S₃ − 6θS₁` (Ramanujan's `12θE₂ = E₂² − E₄`).
* `tau_E4cube_int` : `691·[qⁿ]E₄³ = 65520σ₁₁(n) + 432000τ(n)` in `ℤ` (from `Mod691.tau_mod_relation`), and
  `E4_cube` : `E₄³ = 1 − 720S₃ + 1440S₇ + 13824000S₃³`, whence for `τ(p) = 0` the 2-adic condition
  `691(1440σ₇(p) − 720σ₃(p)) ≡ 65520σ₁₁(p) (mod 2¹²)`.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open PowerSeries ModP Igusa
open scoped ArithmeticFunction.sigma

/-- `12 S₁² = S₁ + 5 S₃ − 6 θS₁` (from `12θE₂ = E₂² − E₄`). -/
lemma coeff_Sk (k n : ℕ) : coeff n (Sk k) = (σ k n : ℤ) := coeff_mk _ _

lemma S1_sq : 12 * Sk 1 ^ 2 = Sk 1 + 5 * Sk 3 - 6 * theta (Sk 1) := by
  obtain ⟨-, -, R3⟩ := RamanujanODEProof.ramanujanODE
  rw [E2_eq, E4_eq, theta_sub, theta_one, theta_ofNat_mul] at R3
  have : (48 : PowerSeries ℤ) * (12 * Sk 1 ^ 2 - (Sk 1 + 5 * Sk 3 - 6 * theta (Sk 1))) = 0 := by
    linear_combination -R3
  have h48 : (48 : PowerSeries ℤ) ≠ 0 := by
    intro h; have := congrArg (coeff 0) h
    rw [show (48 : PowerSeries ℤ) = PowerSeries.C (48 : ℤ) from (map_ofNat _ _).symm, coeff_zero_C,
      map_zero] at this
    norm_num at this
  linear_combination (mul_eq_zero.mp this).resolve_left h48

lemma map_Sk_mod3 {k : ℕ} (hk : ∀ x : ZMod 3, x ^ k = x) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (Sk k) = PowerSeries.map (Int.castRingHom (ZMod 3)) (Sk 1) := by
  ext n
  simp only [coeff_map, Sk, coeff_mk, eq_intCast]
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  exact Finset.sum_congr rfl fun d _ => by simp [hk]

lemma Zs3_mod3 :
    PowerSeries.map (Int.castRingHom (ZMod 3)) Zs3 =
      PowerSeries.map (Int.castRingHom (ZMod 3)) (2 * Sk 1 ^ 2 + 2 * Sk 1) := by
  have h3 := map_Sk_mod3 (k := 3) (by decide)
  have h7 := map_Sk_mod3 (k := 7) (by decide)
  have h9 := map_Sk_mod3 (k := 9) (by decide)
  simp only [Zs3, map_add, map_mul, map_pow, map_neg, map_ofNat, h3, h7, h9]
  set s := PowerSeries.map (Int.castRingHom (ZMod 3)) (Sk 1)
  have e3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C (3 : ZMod 3) from (map_ofNat _ _).symm,
      show (3 : ZMod 3) = 0 by decide, map_zero]
  linear_combination (5098 * s ^ 2 + 26 * s + 522240 * s ^ 3) * e3

/-- **`τ` modulo 9.** -/
theorem tau_mod9_all {n : ℕ} (hn : n ≠ 0) :
    (256 * TauCong.tauPS n : ZMod 9) =
      160 * (σ 7 n : ZMod 9) + 176 * (σ 9 n : ZMod 9) - 320 * (n : ZMod 9) ^ 2 * (σ 7 n : ZMod 9) +
        2 * ((σ 1 n : ZMod 9) + 5 * (σ 3 n : ZMod 9) - 6 * (n : ZMod 9) * (σ 1 n : ZMod 9)) +
        6 * (σ 1 n : ZMod 9) := by
  have hc3 := core3 hn
  have hz : ((coeff n Zs3 : ℤ) : ZMod 3) = ((2 * coeff n (Sk 1 ^ 2) + 2 * (σ 1 n : ℤ) : ℤ) : ZMod 3) := by
    have := congrArg (coeff n) Zs3_mod3
    simp only [coeff_map, eq_intCast] at this
    rw [this, map_add, coeff_ofNat_mul', coeff_ofNat_mul']; simp [Sk]
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hz.symm
  have hs2 := congrArg (coeff n) S1_sq
  simp only [coeff_ofNat_mul', map_sub, map_add, coeff_theta, coeff_Sk] at hs2
  push_cast at hw
  have hint : 256 * TauCong.tauPS n - (160 * (σ 7 n : ℤ) + 176 * (σ 9 n : ℤ) - 320 * (n : ℤ) ^ 2 * (σ 7 n : ℤ) +
      2 * ((σ 1 n : ℤ) + 5 * (σ 3 n : ℤ) - 6 * (n : ℤ) * (σ 1 n : ℤ)) + 6 * (σ 1 n : ℤ)) =
      9 * (w - 2 * coeff n (Sk 1 ^ 2)) := by
    linear_combination hc3 + 3 * hw + 2 * hs2
  have := congrArg (fun x : ℤ => (x : ZMod 9)) hint
  simp only at this
  push_cast at this
  rw [show (9 : ZMod 9) = 0 by decide, zero_mul] at this
  linear_combination this

/-- `120 S₃² = S₇ − S₃`. -/
lemma S3_sq : 120 * Sk 3 ^ 2 = Sk 7 - Sk 3 := by
  have h := E4_sq
  rw [E4_eq] at h
  have : (480 : PowerSeries ℤ) * (120 * Sk 3 ^ 2 - (Sk 7 - Sk 3)) = 0 := by linear_combination h
  have h480 : (480 : PowerSeries ℤ) ≠ 0 := by
    intro h; have := congrArg (coeff 0) h
    rw [show (480 : PowerSeries ℤ) = PowerSeries.C (480 : ℤ) from (map_ofNat _ _).symm, coeff_zero_C,
      map_zero] at this
    norm_num at this
  linear_combination (mul_eq_zero.mp this).resolve_left h480

/-- `E₄³ = 1 − 720S₃ + 1440S₇ + 13824000S₃³`. -/
lemma E4_cube : E4 ℤ ^ 3 = 1 - 720 * Sk 3 + 1440 * Sk 7 + 13824000 * Sk 3 ^ 3 := by
  rw [E4_eq]; linear_combination 1440 * S3_sq

/-- The `E₁₂` relation in `ℤ`: `691·[qⁿ]E₄³ = 65520σ₁₁(n) + 432000τ(n)` (`n ≥ 1`). -/
theorem tau_E4cube_int {n : ℕ} (hn : n ≠ 0) :
    691 * coeff n (E4 ℤ ^ 3) = 65520 * (σ 11 n : ℤ) + 432000 * TauCong.tauPS n := by
  have h := RamanujanTau.Mod691.tau_mod_relation hn
  rw [ModP.qExpansion_E4, RamanujanTau.DiscriminantBridge.qExpansion_discriminant_coeff] at h
  have hE : E4 ℂ ^ 3 = PowerSeries.map (Int.castRingHom ℂ) (E4 ℤ ^ 3) := by rw [map_pow, map_E4]
  rw [hE, coeff_map] at h
  simp only [eq_intCast] at h
  exact_mod_cast h

/-- The 2-adic consequence at a zero: `691(1440σ₇ − 720σ₃) − 65520σ₁₁ ≡ 0 (mod 2¹²)` whenever `τ(n) = 0`. -/
theorem two_adic_of_tau_eq_zero {n : ℕ} (hn : n ≠ 0) (h0 : TauCong.tauPS n = 0) :
    (691 * (1440 * (σ 7 n : ZMod 4096) - 720 * (σ 3 n : ZMod 4096)) - 65520 * (σ 11 n : ZMod 4096)) = 0 := by
  have h := tau_E4cube_int hn
  rw [E4_cube, h0] at h
  simp only [map_add, map_sub, coeff_one, if_neg hn, coeff_ofNat_mul', Sk, coeff_mk] at h
  have := congrArg (fun x : ℤ => (x : ZMod 4096)) h
  simp only at this
  push_cast at this
  rw [show (13824000 : ZMod 4096) = 0 by decide] at this
  linear_combination this

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.tau_mod9_all
#print axioms RamanujanTau.LehmerSmall.two_adic_of_tau_eq_zero
