import RamanujanTau.RamanujanODE.Main
import RamanujanTau.ModP.Structure
import RamanujanTau.TauBridge

/-! # Ramanujan's congruences mod 7 and mod 25, from Ramanujan's differential equations

* `tau_mod7_all`  : `τ(n) ≡ n σ₃(n) (mod 7)` for every `n ≥ 1`;
* `tau_mod25_all` : `τ(n) ≡ n σ₉(n) (mod 25)` for every `n ≥ 1`.

Inputs (all theorems of the repo): Ramanujan's ODEs over `ℤ` (`RamanujanODEProof.ramanujanODE`),
`E₄³ − E₆² = 1728Δ` (`ModP.ev_disc`), and `E₄E₆ = E₁₀` (proved here from `ModP.exists_poly_Eis`, the
structure theorem for level-one forms).

*mod 7.* In `𝔽₇⟦q⟧`, `E₆ = 1`, so `2θE₆ = E₂E₆ − E₄²` gives `E₂ = E₄²` and `3θE₄ = E₂E₄ − E₆ = E₄³ − E₆²
= 1728Δ`; reading off `qⁿ`, `720 n σ₃(n) = 1728 τ(n)`, i.e. `τ(n) = nσ₃(n)` in `𝔽₇`.

*mod 25.* Over `ℤ`, `6θ(E₄E₆) = 5G − 5184Δ` with `G = E₂E₄E₆ − E₄³ + 1728Δ`. In `𝔽₅⟦q⟧`, `E₄ = 1`, so
`E₂ = E₆` and `G ≡ E₆² − 1 + 1728Δ = 0`: `5 ∣ G`. With `E₄E₆ = 1 − 264Σσ₉qⁿ`, the `qⁿ` coefficient is
`−1584 n σ₉(n) ≡ −5184 τ(n) (mod 25)`, i.e. `9τ(n) ≡ 9nσ₉(n)`.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open PowerSeries ModP Igusa
open scoped ArithmeticFunction.sigma

/-- `S_k = Σ_{n ≥ 1} σ_k(n) qⁿ` over `ℤ`. -/
noncomputable def Sk (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => (σ k n : ℤ)

lemma coeff_E4 {R : Type*} [CommRing R] (n : ℕ) :
    coeff n (E4 R) = if n = 0 then 1 else 240 * (σ 3 n : R) := by
  rw [E4, coeff_map, RamanujanTau.Mod691.coeff_p4]; split_ifs <;> simp

lemma coeff_E6 {R : Type*} [CommRing R] (n : ℕ) :
    coeff n (E6 R) = if n = 0 then 1 else -504 * (σ 5 n : R) := by
  rw [E6, coeff_map, RamanujanTau.Mod691.coeff_p6]; split_ifs <;> simp

lemma coeff_Dq {R : Type*} [CommRing R] (n : ℕ) : coeff n (Dq R) = (TauCong.tauPS n : R) := by
  rw [Dq, coeff_map]; rfl

lemma disc_eq {R : Type*} [CommRing R] : E4 R ^ 3 - E6 R ^ 2 = 1728 * Dq R := by
  have h := ev_disc R
  simpa only [map_sub, map_pow, ev_X0, ev_X1] using h

/-- **`E₄E₆ = E₁₀ = 1 − 264 Σ σ₉(n) qⁿ`** over `ℤ`. -/
theorem E4_mul_E6 : E4 ℤ * E6 ℤ = 1 - 264 * Sk 9 := by
  obtain ⟨P, hP, hPe⟩ := exists_poly_Eis (k := 10) (by norm_num) ⟨5, rfl⟩
  obtain ⟨Q, -, hQ0, hPQ⟩ := exists_div hP
  rw [hQ0 (by norm_num), mul_zero, add_zero] at hPQ
  have hb : (base 10 : MvPolynomial (Fin 2) ℚ) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
    simp [base, bexp0, bexp1]
  rw [hb] at hPQ
  set c := MvPolynomial.eval one2 P
  have hev : TateCurve.Eis 10 = PowerSeries.C c * (E4 ℚ * E6 ℚ) := by
    rw [← hPe, hPQ, map_mul, map_mul, ev_C, ev_X0, ev_X1]
  have h0 := congrArg (coeff 0) hev
  rw [TateCurve.coeff_Eis, coeff_C_mul, coeff_zero_eq_constantCoeff_apply, map_mul,
    constantCoeff_E4, constantCoeff_E6] at h0
  simp at h0
  -- h0 : 1 = c
  have h1 := congrArg (coeff 1) hev
  rw [TateCurve.coeff_Eis, coeff_C_mul, ← h0, one_mul, coeff_mul] at h1
  simp [Finset.Nat.sum_antidiagonal_succ, coeff_E4, coeff_E6] at h1
  norm_num at h1
  -- h1 : kappa 10 = -264  (in some normal form)
  apply PowerSeries.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [map_mul, map_E4, map_E6]
  ext n
  have hn := congrArg (coeff n) hev
  rw [← h0, map_one, one_mul] at hn
  rw [← hn, TateCurve.coeff_Eis, h1, map_sub, map_one,
    show (264 : PowerSeries ℤ) = PowerSeries.C (264 : ℤ) from (map_ofNat _ _).symm,
    map_mul, map_C, map_sub, coeff_one, coeff_C_mul, coeff_map]
  simp [Sk]; ring

/-- **`E₄² = E₈ = 1 + 480 Σ σ₇(n) qⁿ`** over `ℤ`. -/
theorem E4_sq : E4 ℤ ^ 2 = 1 + 480 * Sk 7 := by
  obtain ⟨P, hP, hPe⟩ := exists_poly_Eis (k := 8) (by norm_num) ⟨4, rfl⟩
  obtain ⟨Q, -, hQ0, hPQ⟩ := exists_div hP
  rw [hQ0 (by norm_num), mul_zero, add_zero] at hPQ
  have hb : (base 8 : MvPolynomial (Fin 2) ℚ) = MvPolynomial.X 0 ^ 2 := by
    simp [base, bexp0, bexp1]
  rw [hb] at hPQ
  set c := MvPolynomial.eval one2 P
  have hev : TateCurve.Eis 8 = PowerSeries.C c * (E4 ℚ ^ 2) := by
    rw [← hPe, hPQ, map_mul, map_pow, ev_C, ev_X0]
  have h0 := congrArg (coeff 0) hev
  rw [TateCurve.coeff_Eis, coeff_C_mul, coeff_zero_eq_constantCoeff_apply, map_pow,
    constantCoeff_E4] at h0
  simp at h0
  have h1 := congrArg (coeff 1) hev
  rw [TateCurve.coeff_Eis, coeff_C_mul, ← h0, one_mul, sq, coeff_mul] at h1
  simp [Finset.Nat.sum_antidiagonal_succ, coeff_E4] at h1
  norm_num at h1
  apply PowerSeries.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [map_pow, map_E4]
  ext n
  have hn := congrArg (coeff n) hev
  rw [← h0, map_one, one_mul] at hn
  rw [← hn, TateCurve.coeff_Eis, h1, map_add, map_one,
    show (480 : PowerSeries ℤ) = PowerSeries.C (480 : ℤ) from (map_ofNat _ _).symm,
    map_mul, map_C, map_add, coeff_one, coeff_C_mul, coeff_map]
  simp [Sk]

lemma coeff_ofNat_mul' {R : Type*} [CommRing R] (c n : ℕ) [c.AtLeastTwo] (f : PowerSeries R) :
    coeff n ((no_index (OfNat.ofNat c : PowerSeries R)) * f) = (OfNat.ofNat c : R) * coeff n f := by
  rw [show (OfNat.ofNat c : PowerSeries R) = PowerSeries.C (OfNat.ofNat c : R) from (map_ofNat _ _).symm,
    coeff_C_mul]

/-- **Ramanujan's congruence mod 7**: `τ(n) ≡ n σ₃(n) (mod 7)` for every `n ≥ 1`. -/
theorem tau_mod7_all {n : ℕ} (hn : n ≠ 0) :
    (TauCong.tauPS n : ZMod 7) = (n : ZMod 7) * (σ 3 n : ZMod 7) := by
  obtain ⟨h1, h2, -⟩ := Igusa.ode_map (R := ZMod 7) RamanujanODEProof.ramanujanODE
  have hE6 : E6 (ZMod 7) = 1 := by
    ext m; rw [coeff_E6, coeff_one]
    split_ifs
    · rfl
    · rw [show (-504 : ZMod 7) = 0 by decide, zero_mul]
  rw [hE6, theta_one, mul_zero, mul_one] at h2
  simp only [hE6] at h1
  have hd := disc_eq (R := ZMod 7)
  rw [hE6, one_pow] at hd
  have hE2 : Igusa.E2 (ZMod 7) = E4 (ZMod 7) ^ 2 := by linear_combination -h2
  have key : 3 * theta (E4 (ZMod 7)) = 1728 * Dq (ZMod 7) := by
    rw [h1, hE2]; linear_combination hd
  have hc := congrArg (coeff n) key
  rw [coeff_ofNat_mul', coeff_ofNat_mul', coeff_theta, coeff_E4, coeff_Dq, if_neg hn] at hc
  have e1 : (3 : ZMod 7) * 240 = -1 := by decide
  have e2 : (1728 : ZMod 7) = -1 := by decide
  linear_combination hc - ((n : ZMod 7) * (σ 3 n : ZMod 7)) * e1 + (TauCong.tauPS n : ZMod 7) * e2

/-- `6θ(E₄E₆) = 5G − 5184Δ` with `G = E₂E₄E₆ − E₄³ + 1728Δ` (over `ℤ`). -/
lemma theta_E10 :
    6 * theta (E4 ℤ * E6 ℤ) =
      5 * (Igusa.E2 ℤ * E4 ℤ * E6 ℤ - E4 ℤ ^ 3 + 1728 * Dq ℤ) - 5184 * Dq ℤ := by
  obtain ⟨h1, h2, -⟩ := RamanujanODEProof.ramanujanODE
  have hd := disc_eq (R := ℤ)
  rw [theta_mul]
  linear_combination 2 * E6 ℤ * h1 + 3 * E4 ℤ * h2 + 2 * hd

/-- `G = E₂E₄E₆ − E₄³ + 1728Δ ≡ 0 (mod 5)`. -/
lemma G_mod5 :
    PowerSeries.map (Int.castRingHom (ZMod 5))
      (Igusa.E2 ℤ * E4 ℤ * E6 ℤ - E4 ℤ ^ 3 + 1728 * Dq ℤ) = 0 := by
  obtain ⟨h1, -, -⟩ := Igusa.ode_map (R := ZMod 5) RamanujanODEProof.ramanujanODE
  have hE4 : E4 (ZMod 5) = 1 := by
    ext m; rw [coeff_E4, coeff_one]
    split_ifs
    · rfl
    · rw [show (240 : ZMod 5) = 0 by decide, zero_mul]
  rw [hE4, theta_one, mul_zero, mul_one] at h1
  have hd := disc_eq (R := ZMod 5)
  rw [hE4, one_pow] at hd
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, Igusa.map_E2, map_E4, map_E6, map_Dq, hE4]
  linear_combination (-(E6 (ZMod 5))) * h1 - hd

/-- **Ramanujan's congruence mod 25**: `τ(n) ≡ n σ₉(n) (mod 25)` for every `n ≥ 1`. -/
theorem tau_mod25_all {n : ℕ} (hn : n ≠ 0) :
    (TauCong.tauPS n : ZMod 25) = (n : ZMod 25) * (σ 9 n : ZMod 25) := by
  have hG : (5 : ℤ) ∣ coeff n (Igusa.E2 ℤ * E4 ℤ * E6 ℤ - E4 ℤ ^ 3 + 1728 * Dq ℤ) := by
    have := congrArg (coeff n) G_mod5
    rw [coeff_map, map_zero] at this
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp this
  obtain ⟨g, hg⟩ := hG
  have hk := congrArg (coeff n) theta_E10
  rw [coeff_ofNat_mul', coeff_theta, E4_mul_E6, map_sub, coeff_one, if_neg hn, coeff_ofNat_mul',
    map_sub, coeff_ofNat_mul', hg, coeff_ofNat_mul', coeff_Dq] at hk
  simp only [Sk, coeff_mk] at hk
  set t := TauCong.tauPS n
  set sg : ℤ := (σ 9 n : ℤ)
  have h9 : (((9 : ℤ) * (t - n * sg) : ℤ) : ZMod 25) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨g - 207 * t + 63 * n * sg, by linear_combination hk⟩
  push_cast at h9
  have e : (125 : ZMod 25) = 0 := by decide
  have hsg : (sg : ZMod 25) = (σ 9 n : ZMod 25) := by simp [sg]
  rw [← hsg]
  linear_combination 14 * h9 - ((t : ZMod 25) - n * sg) * e

lemma theta_sub {R : Type*} [CommRing R] (f g : PowerSeries R) : theta (f - g) = theta f - theta g := by
  ext n; simp [coeff_theta, mul_sub]

lemma theta_ofNat_mul {R : Type*} [CommRing R] (c : ℕ) [c.AtLeastTwo] (f : PowerSeries R) :
    theta ((OfNat.ofNat c : PowerSeries R) * f) = (OfNat.ofNat c : PowerSeries R) * theta f := by
  ext n; rw [coeff_theta, coeff_ofNat_mul', coeff_ofNat_mul', coeff_theta]; ring

/-- `36 θ²(E₄²) = 18X − 13824Δ`, `X = E₂²E₄² − 2E₂E₄E₆ + E₄³` (over `ℤ`). -/
lemma theta2_E8 :
    36 * theta (theta (E4 ℤ ^ 2)) =
      18 * (Igusa.E2 ℤ ^ 2 * E4 ℤ ^ 2 - 2 * Igusa.E2 ℤ * (E4 ℤ * E6 ℤ) + E4 ℤ ^ 3) - 13824 * Dq ℤ := by
  obtain ⟨R1, R2, R3⟩ := RamanujanODEProof.ramanujanODE
  have hd := disc_eq (R := ℤ)
  have R1' := congrArg theta R1
  rw [theta_ofNat_mul, theta_sub, theta_mul] at R1'
  have hθ : theta (theta (E4 ℤ ^ 2)) =
      2 * (theta (E4 ℤ)) ^ 2 + 2 * E4 ℤ * theta (theta (E4 ℤ)) := by
    rw [sq, theta_mul, theta_add, theta_mul, theta_mul]; ring
  rw [hθ]
  set a := theta (E4 ℤ)
  set A := Igusa.E2 ℤ * E4 ℤ - E6 ℤ
  linear_combination (8 * (3 * a + A) + 8 * Igusa.E2 ℤ * E4 ℤ) * R1 + 24 * E4 ℤ * R1' +
    2 * E4 ℤ ^ 2 * R3 - 12 * E4 ℤ * R2 - 8 * hd

lemma E4_eq : E4 ℤ = 1 + 240 * Sk 3 := by
  ext n; rw [coeff_E4, map_add, coeff_one, coeff_ofNat_mul']; simp only [Sk, coeff_mk]
  split_ifs with h <;> simp [h]

lemma E2_eq : Igusa.E2 ℤ = 1 - 24 * Sk 1 := by
  simp [Igusa.E2, Igusa.e2Z, Sk]

lemma sigma7_eq_sigma9_mod3 (n : ℕ) : (σ 7 n : ZMod 3) = (σ 9 n : ZMod 3) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  generalize (d : ZMod 3) = x
  revert x; decide

/-- The integer series `Z` with `E₂²E₄² − 2E₂E₄E₆ + E₄³ = 3(W + 2Y) + 9Z`. -/
noncomputable def Zs3 : PowerSeries ℤ :=
  (-8 * Sk 1) ^ 2 + 2 * (-8 * Sk 1) * (160 * Sk 7) + 3 * (-8 * Sk 1) ^ 2 * (160 * Sk 7) +
    2 * (-8 * Sk 1) * (88 * Sk 9) + 80 * Sk 3 + 3 * (80 * Sk 3) ^ 2 + 3 * (80 * Sk 3) ^ 3

/-- The exact identity behind the 3-adic congruences:
`320 n² σ₇(n) = 160 σ₇(n) + 176 σ₉(n) + 3 Z_n − 256 τ(n)`. -/
theorem core3 {n : ℕ} (hn : n ≠ 0) :
    320 * (n : ℤ) ^ 2 * (σ 7 n : ℤ) =
      160 * (σ 7 n : ℤ) + 176 * (σ 9 n : ℤ) + 3 * coeff n Zs3 - 256 * TauCong.tauPS n := by
  set U := -8 * Sk 1
  set V := 80 * Sk 3
  set W := 160 * Sk 7
  set Y := 88 * Sk 9
  have hX : Igusa.E2 ℤ ^ 2 * E4 ℤ ^ 2 - 2 * Igusa.E2 ℤ * (E4 ℤ * E6 ℤ) + E4 ℤ ^ 3 =
      3 * (W + 2 * Y) + 9 * Zs3 := by
    have e4 : E4 ℤ = 1 + 3 * V := by rw [E4_eq]; simp only [V]; ring
    have e2 : Igusa.E2 ℤ = 1 + 3 * U := by rw [E2_eq]; simp only [U]; ring
    have e8 : E4 ℤ ^ 2 = 1 + 3 * W := by rw [E4_sq]; simp only [W]; ring
    have e10 : E4 ℤ * E6 ℤ = 1 - 3 * Y := by rw [E4_mul_E6]; simp only [Y]; ring
    rw [show E4 ℤ ^ 3 = (1 + 3 * V) ^ 3 by rw [e4], e8, e10, e2, Zs3]; ring
  have hk := congrArg (coeff n) theta2_E8
  rw [hX, E4_sq] at hk
  simp only [W, Y] at hk
  simp only [map_add, map_sub, coeff_ofNat_mul', coeff_theta, coeff_one, if_neg hn, coeff_Dq,
    Sk, coeff_mk] at hk
  have : (54 : ℤ) * (320 * (n : ℤ) ^ 2 * (σ 7 n : ℤ) - (160 * (σ 7 n : ℤ) + 176 * (σ 9 n : ℤ) +
      3 * coeff n Zs3 - 256 * TauCong.tauPS n)) = 0 := by
    linear_combination hk
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linear_combination this

/-- **Ramanujan's congruence mod 3**: `τ(n) ≡ n² σ₇(n) (mod 3)` for every `n ≥ 1`. -/
theorem tau_mod3_all {n : ℕ} (hn : n ≠ 0) :
    (TauCong.tauPS n : ZMod 3) = (n : ZMod 3) ^ 2 * (σ 7 n : ZMod 3) := by
  have hc := congrArg (fun x : ℤ => (x : ZMod 3)) (core3 hn)
  simp only at hc
  push_cast at hc
  rw [← sigma7_eq_sigma9_mod3 n] at hc
  have e1 : (320 : ZMod 3) = 2 := by decide
  have e2 : (160 : ZMod 3) = 1 := by decide
  have e3 : (176 : ZMod 3) = 2 := by decide
  have e4 : (256 : ZMod 3) = 1 := by decide
  have e5 : (3 : ZMod 3) = 0 := by decide
  rw [e1, e2, e3, e4, e5] at hc
  linear_combination hc + ((σ 7 n : ZMod 3) - (n : ZMod 3) ^ 2 * (σ 7 n : ZMod 3)) * e5

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.E4_mul_E6
#print axioms RamanujanTau.LehmerSmall.tau_mod7_all
#print axioms RamanujanTau.LehmerSmall.tau_mod25_all
#print axioms RamanujanTau.LehmerSmall.tau_mod3_all
