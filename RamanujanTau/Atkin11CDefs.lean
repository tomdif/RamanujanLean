/-
# Atkin 11^k: the level-11 eta ratios and Atkin's `g₂` as a theta quotient

`η_a = (q^a;q¹¹)_∞ (q^{11−a};q¹¹)_∞` and the five ratios
`c₀ = η₄/η₂`, `c₁ = −η₂/η₁`, `c₂ = −η₅/η₃`, `c₄ = −q η₁/η₅`, `c₇ = η₃/η₄`.
(They are the 11-dissection components of `E(q)/E(q¹²¹)`, see `Atkin11DissectPS`.)

Atkin's `g₂` is `GN(c)/GD(c)` for two explicit polynomials (`Atkin11Cert.PGN`, `PGD`). The denominator
has constant term `1`, so `g₂` is an integral power series with `g₂ = q + O(q²)`.
-/
import RamanujanTau.RankTheta
import RamanujanTau.Atkin11Cert.Pieces
import RamanujanTau.SPolyHom

set_option autoImplicit false

namespace Atkin11
open PowerSeries RankProof

/-- `η_a = (q^a;q¹¹)_∞ (q^{11−a};q¹¹)_∞`. -/
noncomputable def ηP (a : ℕ) : PowerSeries ℤ := Pinf a 11 * Pinf (11 - a) 11

lemma isUnit_ηP {a : ℕ} (h0 : 1 ≤ a) (h1 : a < 11) : IsUnit (ηP a) :=
  (isUnit_Pinf a 11 h0 (by norm_num)).mul (isUnit_Pinf (11 - a) 11 (by omega) (by norm_num))

noncomputable def cP0 : PowerSeries ℤ := ηP 4 * Ring.inverse (ηP 2)
noncomputable def cP1 : PowerSeries ℤ := -(ηP 2 * Ring.inverse (ηP 1))
noncomputable def cP2 : PowerSeries ℤ := -(ηP 5 * Ring.inverse (ηP 3))
noncomputable def cP4 : PowerSeries ℤ := -(X * ηP 1 * Ring.inverse (ηP 5))
noncomputable def cP7 : PowerSeries ℤ := ηP 3 * Ring.inverse (ηP 4)

/-- the coefficient point `(c₀, c₁, c₂, c₄, c₇)`. -/
noncomputable def cPs : List (PowerSeries ℤ) := [cP0, cP1, cP2, cP4, cP7]

/-! ### constant terms -/

lemma cc_Pinf {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) : constantCoeff (Pinf b a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have := (X_pow_dvd_iff.mp (X_pow_dvd_Pinf_sub b a hb ha 0)) 0 (by omega)
  rw [map_sub, sub_eq_zero, Pfin] at this
  rw [this]; simp

lemma cc_ηP {a : ℕ} (h0 : 1 ≤ a) (h1 : a < 11) : constantCoeff (ηP a) = 1 := by
  rw [ηP, map_mul, cc_Pinf h0 (by norm_num), cc_Pinf (by omega) (by norm_num), mul_one]

lemma cc_inv {u : PowerSeries ℤ} (hu : IsUnit u) (h : constantCoeff u = 1) : constantCoeff (Ring.inverse u) = 1 := by
  have := congrArg constantCoeff (Ring.mul_inverse_cancel u hu)
  rwa [map_mul, h, one_mul, map_one] at this

lemma cc_cPs : cPs.map constantCoeff = [1, -1, -1, 0, 1] := by
  simp only [cPs, List.map_cons, List.map_nil, cP0, cP1, cP2, cP4, cP7, map_mul, map_neg, constantCoeff_X,
    cc_ηP (a := 1) le_rfl (by norm_num), cc_ηP (a := 2) (by norm_num) (by norm_num),
    cc_ηP (a := 3) (by norm_num) (by norm_num), cc_ηP (a := 4) (by norm_num) (by norm_num),
    cc_ηP (a := 5) (by norm_num) (by norm_num),
    cc_inv (isUnit_ηP (a := 1) le_rfl (by norm_num)) (cc_ηP (a := 1) le_rfl (by norm_num)),
    cc_inv (isUnit_ηP (a := 2) (by norm_num) (by norm_num)) (cc_ηP (a := 2) (by norm_num) (by norm_num)),
    cc_inv (isUnit_ηP (a := 3) (by norm_num) (by norm_num)) (cc_ηP (a := 3) (by norm_num) (by norm_num)),
    cc_inv (isUnit_ηP (a := 4) (by norm_num) (by norm_num)) (cc_ηP (a := 4) (by norm_num) (by norm_num)),
    cc_inv (isUnit_ηP (a := 5) (by norm_num) (by norm_num)) (cc_ηP (a := 5) (by norm_num) (by norm_num))]
  norm_num

/-! ### the theta form of `g₂` -/

/-- numerator `GN(c)`. -/
noncomputable def gN : PowerSeries ℤ := SPoly.evalP cPs Atkin11Cert.PGN
/-- denominator `GD(c)`. -/
noncomputable def gD : PowerSeries ℤ := SPoly.evalP cPs Atkin11Cert.PGD

lemma cc_gN : constantCoeff gN = 0 := by
  rw [gN, SPoly.evalP_map, cc_cPs]; decide +kernel

lemma cc_gD : constantCoeff gD = 1 := by
  rw [gD, SPoly.evalP_map, cc_cPs]; decide +kernel

lemma isUnit_gD : IsUnit gD := by
  rw [isUnit_iff_constantCoeff, cc_gD]; exact isUnit_one

end Atkin11
