/-
# Integrality of a short curve from an integral invariant differential in the coordinate `w^{1/3}`

For `E : y² = x³ + Ax + B` over a field `K` of characteristic `0`, let `c = v^{1/3}` (`w = z³ v`) and
`Ω = z·c` (so `Ω³ = w`). If `Ω'(z) · Ψ_E(z) = g(Ω(z))` (`Ψ_E = ∂₂F_E(z, 0)`), then
  `[s⁴] g = -A/3`,  `[s²] g = 0`,  `[s⁶] g = -2B/3`         (`coeffs_g`).
Computation modulo `z⁷`, in `Q = K⟦z⟧ ⧸ (z⁷)`:
* `w ≡ z³ + A z⁷ + B z⁹ (mod z¹⁰)`, hence `v ≡ 1 + A z⁴ + B z⁶ (mod z⁷)` and `c ≡ 1 + (A/3) z⁴ + (B/3) z⁶`;
* `Ω' ≡ 1 + (5A/3) z⁴ + (7B/3) z⁶`, `Ψ_E ≡ 1 - 2A z⁴ - 3B z⁶`, `Ω ≡ z + (A/3) z⁵ (mod z⁷)`.
-/
import RamanujanTau.VeluDescent.CubeRoot
import RamanujanTau.VeluLubin.Main

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open PowerSeries

variable {K : Type*} [Field K]

local notation "Qr" => PowerSeries K ⧸ Ideal.span {(X : PowerSeries K) ^ 7}
local notation "mk" => Ideal.Quotient.mk (Ideal.span {(X : PowerSeries K) ^ 7})

lemma mk_X7 : mk ((X : PowerSeries K) ^ 7) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

lemma mk_eq_of_dvd {f g : PowerSeries K} (h : (X : PowerSeries K) ^ 7 ∣ f - g) : mk f = mk g :=
  Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)

lemma dvd_of_mk_eq {f g : PowerSeries K} (h : mk f = mk g) : (X : PowerSeries K) ^ 7 ∣ f - g :=
  Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)

lemma coeff_eq_of_mk_eq {f g : PowerSeries K} (h : mk f = mk g) {n : ℕ} (hn : n < 7) :
    coeff n f = coeff n g := by
  have := (X_pow_dvd_iff.1 (dvd_of_mk_eq h)) n hn
  rw [map_sub] at this
  exact sub_eq_zero.1 this

/-! ### `w` of a short curve modulo `z¹⁰` -/

variable (A B : K)

local notation "Wc" => VeluLubin.shortO A B

lemma w_short_eq : EllipticFormal.w Wc =
    X ^ 3 + C A * X * EllipticFormal.w Wc ^ 2 + C B * EllipticFormal.w Wc ^ 3 := by
  have h := EllipticFormal.w_eq Wc
  simp only [VeluLubin.shortO, map_zero, zero_mul, add_zero] at h
  exact h

lemma w_short_mod : (X : PowerSeries K) ^ 10 ∣
    EllipticFormal.w Wc - (X ^ 3 + C A * X ^ 7 + C B * X ^ 9) := by
  set w := EllipticFormal.w Wc
  set w0 : PowerSeries K := X ^ 3 + C A * X ^ 7 + C B * X ^ 9
  set M := C A * X * (w + w0) + C B * (w ^ 2 + w * w0 + w0 ^ 2)
  have hM : constantCoeff M = 0 := by
    have hw : constantCoeff w = 0 := EllipticFormal.cc_w _
    simp [M, w0, hw]
  have hE : (X : PowerSeries K) ^ 10 ∣ C A * X * w0 ^ 2 + C B * w0 ^ 3 + X ^ 3 - w0 := by
    refine ⟨X * (C A * (C A + C B * X ^ 2) * ((1 + C A * X ^ 4 + C B * X ^ 6) + 1)) +
      X ^ 3 * (C B * (C A + C B * X ^ 2) * ((1 + C A * X ^ 4 + C B * X ^ 6) ^ 2 +
        (1 + C A * X ^ 4 + C B * X ^ 6) + 1)), ?_⟩
    simp only [w0]; ring
  obtain ⟨q, hq⟩ := hE
  have hd : (w - w0) * (1 - M) = X ^ 10 * q := by
    rw [← hq]
    have h := w_short_eq A B
    simp only [M]
    linear_combination h
  have hu : IsUnit (1 - M) := by
    rw [isUnit_iff_constantCoeff, map_sub, map_one, hM, sub_zero]; exact isUnit_one
  obtain ⟨u, hu'⟩ := hu
  refine ⟨q * ↑u⁻¹, ?_⟩
  have : w - w0 = (w - w0) * (1 - M) * ↑u⁻¹ := by
    rw [← hu', mul_assoc, Units.mul_inv, mul_one]
  rw [this, hd, mul_assoc]

lemma v_short_mod : (X : PowerSeries K) ^ 7 ∣
    EllipticFormal.v Wc - (1 + C A * X ^ 4 + C B * X ^ 6) := by
  obtain ⟨q, hq⟩ := w_short_mod A B
  rw [EllipticFormal.w_eq_X3_mul_v] at hq
  refine ⟨q, ?_⟩
  have hX : (X : PowerSeries K) ^ 3 ≠ 0 := pow_ne_zero 3 X_ne_zero
  apply mul_left_cancel₀ hX
  linear_combination hq

lemma w_short_mod7 : (X : PowerSeries K) ^ 7 ∣ EllipticFormal.w Wc - X ^ 3 := by
  obtain ⟨q, hq⟩ := w_short_mod A B
  exact ⟨X ^ 3 * q + C A + C B * X ^ 2, by linear_combination hq⟩

/-! ### Computations in `Q = K⟦z⟧/(z⁷)` -/

lemma mk_pow_eq_zero {n : ℕ} (hn : 7 ≤ n) : (mk X : Qr) ^ n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, ← map_pow, mk_X7, zero_mul]

lemma mk_w : mk (EllipticFormal.w Wc) = (mk X) ^ 3 := by
  rw [mk_eq_of_dvd (w_short_mod7 A B), map_pow]

lemma mk_v : mk (EllipticFormal.v Wc) = 1 + mk (C A) * (mk X) ^ 4 + mk (C B) * (mk X) ^ 6 := by
  rw [mk_eq_of_dvd (v_short_mod A B)]; simp only [map_add, map_one, map_mul, map_pow]

/-- the cube root of `v` modulo `z⁷`. -/
lemma mk_c (h3 : (3 : K) ≠ 0) {c : PowerSeries K} (hc : c ^ 3 = EllipticFormal.v Wc)
    (hc1 : constantCoeff c = 1) :
    mk c = mk (1 + C (A / 3) * X ^ 4 + C (B / 3) * X ^ 6) := by
  set c1 : PowerSeries K := 1 + C (A / 3) * X ^ 4 + C (B / 3) * X ^ 6
  have hA : mk (C A) = 3 * mk (C (A / 3)) := by
    have e : (C A : PowerSeries K) = 3 * C (A / 3) := by
      rw [← map_ofNat (C (R := K)) 3, ← map_mul]; congr 1; field_simp
    rw [e, map_mul, map_ofNat]
  have hB : mk (C B) = 3 * mk (C (B / 3)) := by
    have e : (C B : PowerSeries K) = 3 * C (B / 3) := by
      rw [← map_ofNat (C (R := K)) 3, ← map_mul]; congr 1; field_simp
    rw [e, map_mul, map_ofNat]
  have h7 := mk_pow_eq_zero (K := K) (le_refl 7)
  have hcube : mk (c ^ 3) = mk (c1 ^ 3) := by
    rw [hc, mk_v, hA, hB]
    simp only [c1, map_pow, map_add, map_one, map_mul]
    set x := (mk X : Qr)
    set α := mk (C (A / 3))
    set β := mk (C (B / 3))
    linear_combination (-(x * (3 * (α + β * x ^ 2) ^ 2) + x ^ 5 * (α + β * x ^ 2) ^ 3)) * h7
  set u := c ^ 2 + c * c1 + c1 ^ 2
  have hu : IsUnit u := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff c1 = 1 := by simp [c1]
    simp only [u, map_add, map_mul, map_pow, hc1, this]
    norm_num
    exact h3
  have hfac : mk (c - c1) * mk u = 0 := by
    rw [← map_mul, show (c - c1) * u = c ^ 3 - c1 ^ 3 by ring, map_sub, hcube, sub_self]
  have hmu : IsUnit (mk u) := hu.map _
  have := (hmu.mul_left_eq_zero).1 hfac
  rw [map_sub, sub_eq_zero] at this
  exact this

/-! ### Derivatives -/

local notation "pdz" => MvPowerSeries.pd ()

lemma pd_X' : pdz (X : PowerSeries K) = 1 := by
  show pdz (MvPowerSeries.X () : MvPowerSeries Unit K) = 1; rw [MvPowerSeries.pd_X]; simp

lemma pd_C' (a : K) : pdz (C a : PowerSeries K) = 0 := MvPowerSeries.pd_C () a

lemma pd_one' : pdz (1 : PowerSeries K) = 0 := by rw [← map_one (C (R := K)), pd_C']

lemma pd_X_pow (n : ℕ) : pdz ((X : PowerSeries K) ^ (n + 1)) = (n + 1 : PowerSeries K) * X ^ n := by
  induction n with
  | zero => simp [pd_X']
  | succ n ih =>
    rw [pow_succ, MvPowerSeries.pd_mul, ih, pd_X']
    push_cast; ring

/-- `Ω' = (z c)' ≡ 1 + 5(A/3) z⁴ + 7(B/3) z⁶ (mod z⁷)`. -/
lemma mk_pd_Omega (h3 : (3 : K) ≠ 0) {c : PowerSeries K} (hc : c ^ 3 = EllipticFormal.v Wc)
    (hc1 : constantCoeff c = 1) :
    mk (pdz (X * c)) = 1 + 5 * mk (C (A / 3)) * (mk X) ^ 4 + 7 * mk (C (B / 3)) * (mk X) ^ 6 := by
  obtain ⟨r, hr⟩ := dvd_of_mk_eq (mk_c A B h3 hc hc1)
  have hc' : c = 1 + C (A / 3) * X ^ 4 + C (B / 3) * X ^ 6 + X ^ 7 * r := by linear_combination hr
  rw [MvPowerSeries.pd_mul, pd_X', one_mul, hc']
  simp only [MvPowerSeries.pd_add, MvPowerSeries.pd_mul, pd_C', pd_one', zero_mul, zero_add,
    show (X : PowerSeries K) ^ 4 = X ^ (3 + 1) from rfl, show (X : PowerSeries K) ^ 6 = X ^ (5 + 1) from rfl,
    show (X : PowerSeries K) ^ 7 = X ^ (6 + 1) from rfl, pd_X_pow]
  have h7 := mk_pow_eq_zero (K := K) (le_refl 7)
  simp only [map_add, map_mul, map_pow, map_one, map_natCast, map_ofNat, Nat.cast_ofNat]
  set x := (mk X : Qr)
  linear_combination (8 * mk r + x * mk (pdz r)) * h7

/-- `Ψ_E ≡ 1 - 2A z⁴ - 3B z⁶ (mod z⁷)`. -/
lemma mk_Psi : mk (FGL.Ψ (EllipticFormal.formalGroup Wc) (FGL.T : PowerSeries K)) =
    1 - 2 * mk (C A) * (mk X) ^ 4 - 3 * mk (C B) * (mk X) ^ 6 := by
  rw [VeluLubin.Ψ_short]
  show mk (1 - 2 * C A * X * EllipticFormal.w Wc - 3 * C B * EllipticFormal.w Wc ^ 2) = _
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, mk_w]
  ring

/-! ### The coefficients of `g` -/

lemma trunc_dvd (g : PowerSeries K) :
    (X : PowerSeries K) ^ 7 ∣ g - ∑ k ∈ Finset.range 7, C (coeff k g) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range 7) m (fun k => coeff k g), if_pos (Finset.mem_range.2 hm),
    sub_self]

lemma sb_add' {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) (f g : PowerSeries K) :
    VeluLubin.sb Ω (f + g) = VeluLubin.sb Ω f + VeluLubin.sb Ω g :=
  MvPowerSeries.subst_add (FGL.hs (VeluLubin.hc (a := (Ω : MvPowerSeries Unit K)) hΩ)) f g

lemma sb_mul' {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) (f g : PowerSeries K) :
    VeluLubin.sb Ω (f * g) = VeluLubin.sb Ω f * VeluLubin.sb Ω g :=
  MvPowerSeries.subst_mul (FGL.hs (VeluLubin.hc (a := (Ω : MvPowerSeries Unit K)) hΩ)) f g

lemma sb_pow' {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) (f : PowerSeries K) (n : ℕ) :
    VeluLubin.sb Ω (f ^ n) = VeluLubin.sb Ω f ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, ← map_one (C (R := K)), VeluLubin.sb]
    exact MvPowerSeries.subst_C _
  | succ n ih => rw [pow_succ, sb_mul' hΩ, ih, pow_succ]

lemma sb_C' {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) (a : K) :
    VeluLubin.sb Ω (C a) = C a := by
  rw [VeluLubin.sb]; exact MvPowerSeries.subst_C _

lemma sb_X' {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) : VeluLubin.sb Ω (X : PowerSeries K) = Ω :=
  VeluLubin.sb_X hΩ

lemma sb_poly {Ω : PowerSeries K} (hΩ : constantCoeff Ω = 0) (a : ℕ → K) (n : ℕ) :
    VeluLubin.sb Ω (∑ k ∈ Finset.range n, C (a k) * X ^ k) = ∑ k ∈ Finset.range n, C (a k) * Ω ^ k := by
  induction n with
  | zero => simp only [Finset.sum_range_zero]; rw [← map_zero (C (R := K)), sb_C' hΩ]
  | succ n ih =>
    rw [Finset.sum_range_succ, sb_add' hΩ, ih, sb_mul' hΩ, sb_C' hΩ, sb_pow' hΩ, sb_X' hΩ,
      Finset.sum_range_succ]

/-- the algebra of `coeffs_g`, in any commutative ring with `x⁷ = 0`. -/
lemma alg_core {Q : Type*} [CommRing Q] (x α β Z : Q) (g : ℕ → Q) (h7 : x ^ 7 = 0)
    (H : (1 + 5 * α * x ^ 4 + 7 * β * x ^ 6) * (1 - 2 * (3 * α) * x ^ 4 - 3 * (3 * β) * x ^ 6) =
      ∑ k ∈ Finset.range 7, g k * (x * (1 + α * x ^ 4 + β * x ^ 6)) ^ k +
        (x * (1 + α * x ^ 4 + β * x ^ 6)) ^ 7 * Z) :
    1 - α * x ^ 4 - 2 * β * x ^ 6 = g 0 + g 1 * x + g 2 * x ^ 2 + g 3 * x ^ 3 + g 4 * x ^ 4 +
      (g 5 + α * g 1) * x ^ 5 + (g 6 + 2 * α * g 2) * x ^ 6 := by
  have hz : ∀ n : ℕ, 7 ≤ n → x ^ n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, h7, zero_mul]
  set y := x + α * x ^ 5 with hyd
  have hy : x * (1 + α * x ^ 4 + β * x ^ 6) = y := by linear_combination β * h7
  have hy2 : y ^ 2 = x ^ 2 + 2 * α * x ^ 6 := by linear_combination (α ^ 2 * x ^ 3) * h7
  have hyk : ∀ k : ℕ, 3 ≤ k → y ^ k = x ^ k := by
    intro k hk
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (1 + α * x ^ 4) 1 k
    rw [one_pow] at ht
    have e : y = x * (1 + α * x ^ 4) := by rw [hyd]; ring
    have : x ^ k * (1 + α * x ^ 4) ^ k - x ^ k = x ^ (k + 4) * (α * t) := by
      calc x ^ k * (1 + α * x ^ 4) ^ k - x ^ k = x ^ k * ((1 + α * x ^ 4) ^ k - 1) := by ring
        _ = x ^ k * ((1 + α * x ^ 4 - 1) * t) := by rw [ht]
        _ = x ^ (k + 4) * (α * t) := by ring
    rw [hz (k + 4) (by omega), zero_mul] at this
    rw [e, mul_pow]
    exact sub_eq_zero.1 this
  rw [hy] at H
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at H
  rw [hy2, hyk 3 (by norm_num), hyk 4 (by norm_num), hyk 5 (by norm_num), hyk 6 (by norm_num),
    hyk 7 (by norm_num), h7] at H
  linear_combination H + (30 * α ^ 2 * x + 87 * α * β * x ^ 3 + 63 * β ^ 2 * x ^ 5) * h7

/-- **the coefficients of `g`** in `Ω'·Ψ_E = g(Ω)`. -/
theorem coeffs_g (h3 : (3 : K) ≠ 0) {c : PowerSeries K} (hc : c ^ 3 = EllipticFormal.v Wc)
    (hc1 : constantCoeff c = 1) (g : PowerSeries K)
    (hg : pdz (X * c) * FGL.Ψ (EllipticFormal.formalGroup Wc) (FGL.T : PowerSeries K) =
      VeluLubin.sb (X * c) g) :
    coeff 4 g = -(A / 3) ∧ coeff 6 g = -(2 * (B / 3)) := by
  have hΩ0 : constantCoeff (X * c : PowerSeries K) = 0 := by simp
  obtain ⟨g', hg'⟩ := trunc_dvd g
  have hgd : g = ∑ k ∈ Finset.range 7, C (coeff k g) * X ^ k + X ^ 7 * g' := by
    linear_combination hg'
  rw [hgd, sb_add' hΩ0, sb_mul' hΩ0, sb_poly hΩ0, sb_pow' hΩ0, sb_X' hΩ0] at hg
  have H := congrArg mk hg
  have hA : mk (C A) = 3 * mk (C (A / 3)) := by
    have e : (C A : PowerSeries K) = 3 * C (A / 3) := by
      rw [← map_ofNat (C (R := K)) 3, ← map_mul]; congr 1; field_simp
    rw [e, map_mul, map_ofNat]
  have hB : mk (C B) = 3 * mk (C (B / 3)) := by
    have e : (C B : PowerSeries K) = 3 * C (B / 3) := by
      rw [← map_ofNat (C (R := K)) 3, ← map_mul]; congr 1; field_simp
    rw [e, map_mul, map_ofNat]
  have hmc := mk_c A B h3 hc hc1
  simp only [map_add, map_mul, map_pow, map_one] at hmc
  rw [map_mul, mk_pd_Omega A B h3 hc hc1, mk_Psi, hA, hB, map_add, map_sum, map_mul, map_pow,
    map_mul, hmc] at H
  simp only [map_mul, map_pow, hmc] at H
  have h7 : (mk X : Qr) ^ 7 = 0 := mk_pow_eq_zero le_rfl
  have core := alg_core (mk X) (mk (C (A / 3))) (mk (C (B / 3))) _ (fun k => mk (C (coeff k g))) h7 H
  set Lp : PowerSeries K := 1 - C (A / 3) * X ^ 4 - C (2 * (B / 3)) * X ^ 6
  set Rp : PowerSeries K := C (coeff 0 g) + C (coeff 1 g) * X + C (coeff 2 g) * X ^ 2 +
    C (coeff 3 g) * X ^ 3 + C (coeff 4 g) * X ^ 4 + C (coeff 5 g + A / 3 * coeff 1 g) * X ^ 5 +
    C (coeff 6 g + 2 * (A / 3) * coeff 2 g) * X ^ 6
  have key : mk Lp = mk Rp := by
    simp only [Lp, Rp, map_sub, map_add, map_mul, map_pow, map_one, map_ofNat]
    exact core
  have c2 := coeff_eq_of_mk_eq key (n := 2) (by norm_num)
  have c4 := coeff_eq_of_mk_eq key (n := 4) (by norm_num)
  have c6 := coeff_eq_of_mk_eq key (n := 6) (by norm_num)
  simp only [Lp, Rp, LinearMap.map_add, LinearMap.map_sub, coeff_one, coeff_C_mul_X_pow, coeff_X,
    coeff_C, coeff_C_mul, coeff_X_pow] at c2 c4 c6
  norm_num at c2 c4 c6
  refine ⟨by linear_combination -c4, ?_⟩
  linear_combination -c6 + 2 * (A / 3) * c2

end VeluDescent
