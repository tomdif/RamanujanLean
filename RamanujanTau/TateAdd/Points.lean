/-
# The three Tate points in `T` and their relations

In `T = ℚ⟦a⟧⟦X⟧⟦b⟧` (with `c = 1 + X`, `t = X`) the points `P(u)`, `P(v)`, `P(uv)` in the short model
scaled by `u = 6` (`X = 36x + 3`, `Y = 108 θx`, `A = 1296a₄ − 27`, `B = 46656a₆ − 3888a₄ + 54`).
`P(v)` is near the origin: `v = 1 + t`, and we use the pole-cleared `x₂ = t²X₂`, `y₂ = t³Y₂`.
-/
import RamanujanTau.TateAdd.Ring3
import RamanujanTau.TateAdd.Alg

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot

local notation "aX" => (Polynomial.X : P)

/-- `t = X` in `T`. -/
abbrev tT : T := C (X : k2)
/-- `a` in `T`. -/
abbrev aT : T := C ca

lemma ιu_C (p : P) : ιu (C p) = C (ev2 ca p) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ιu, coeff_C, coeff_C]; split_ifs with h <;> simp [h, ev2]
lemma ιv_C (p : P) : ιv (C p) = C (ev2 (1 + X) p) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ιv, coeff_C, coeff_C]; split_ifs with h <;> simp [h, ev2]
lemma ιw_C (p : P) : ιw (C p) = C (ev2 (ca * (1 + X)) p) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ιw, coeff_C, coeff_C]; split_ifs with h <;> simp [h, ev2]

lemma ιu_vB : ιu vB = aT - 1 := by rw [ιu_C]; simp [ev2]
lemma ιu_wB : ιu wB = aT := by rw [ιu_C]; simp [ev2]
lemma ιv_vB : ιv vB = tT := by rw [ιv_C]; simp [ev2]
lemma ιv_wB : ιv wB = 1 + tT := by rw [ιv_C]; simp [ev2]
lemma ιw_vB : ιw vB = aT * (1 + tT) - 1 := by rw [ιw_C]; simp [ev2]
lemma ιw_wB : ιw wB = aT * (1 + tT) := by rw [ιw_C]; simp [ev2]

lemma D_aT : D aT = aT := by rw [D_C, D'_ca]
lemma D_tT : D tT = -(1 + tT) := by rw [D_C, D'_X]; simp
lemma D_one_add_tT : D (1 + tT) = -(1 + tT) := by rw [isDer_D.add, isDer_D.one, D_tT, zero_add]

/-! ### `q`-series coefficients -/

/-- `a₄(q)` in `T`. -/
def a4T : T := ιw a4B
/-- `a₆(q)` in `T`. -/
def a6T : T := ιw a6B

lemma ιu_a4B : ιu a4B = a4T := by
  simp only [ιu, ιw, a4T, RingHom.comp_apply, a4B, (ι3_resc _).1]
lemma ιv_a4B : ιv a4B = a4T := by
  simp only [ιv, ιw, a4T, RingHom.comp_apply, a4B, (ι3_resc _).2]
lemma ιu_a6B : ιu a6B = a6T := by
  simp only [ιu, ιw, a6T, RingHom.comp_apply, a6B, (ι3_resc _).1]
lemma ιv_a6B : ιv a6B = a6T := by
  simp only [ιv, ιw, a6T, RingHom.comp_apply, a6B, (ι3_resc _).2]

lemma D_a4T : D a4T = 0 := D_ιw _
lemma D_a6T : D a6T = 0 := D_ιw _

/-! ### The point at `v = 1 + t` near the origin -/

/-- `Rm 0 N / (a−1)²`. -/
def Rm0' (N : ℕ) : P := ∑ d ∈ N.divisors, (d : P) * aX ^ (N - d) * (∑ i ∈ Finset.range d, aX ^ i) ^ 2
/-- `Rm 1 N / (a−1)`. -/
def Rm1' (N : ℕ) : P :=
  ∑ d ∈ N.divisors, (d : P) ^ 2 * aX ^ (N - d) * ∑ i ∈ Finset.range (2 * d), aX ^ i

lemma Rm0_fac (N : ℕ) : Rm 0 N = (aX - 1) ^ 2 * Rm0' N := by
  rw [Rm, Rm0', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  have hg := geom_sum_mul (aX) d
  have e1 : aX ^ (N + d) = aX ^ (N - d) * (aX ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have e2 : aX ^ N = aX ^ (N - d) * aX ^ d := by rw [← pow_add]; congr 1; omega
  simp only [zero_add, pow_one, pow_zero, one_mul, if_true]
  rw [e1, e2]
  linear_combination -((d : P) * aX ^ (N - d) * ((∑ i ∈ Finset.range d, aX ^ i) * (aX - 1) +
    (aX ^ d - 1))) * hg

lemma Rm1_fac (N : ℕ) : Rm 1 N = (aX - 1) * Rm1' N := by
  rw [Rm, Rm1', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  have hg := geom_sum_mul (aX) (2 * d)
  have e1 : aX ^ (N + d) = aX ^ (N - d) * aX ^ (2 * d) := by rw [← pow_add]; congr 1; omega
  simp only [one_ne_zero, if_false, zero_mul, sub_zero, pow_one]
  rw [e1]
  linear_combination -((d : P) ^ 2 * aX ^ (N - d)) * hg

lemma zB0_fac : zB 0 = C aX + C ((aX - 1) ^ 4) * mk Rm0' := by
  have : mk (Rm 0) = C ((aX - 1) ^ 2) * mk Rm0' := by
    ext N; rw [coeff_mk, coeff_C_mul, coeff_mk, Rm0_fac]
  rw [zB, this, cpoly, ← mul_assoc, ← map_mul]; ring_nf

lemma zB1_fac : zB 1 = C (-(aX * (1 + aX))) + C ((aX - 1) ^ 4) * mk Rm1' := by
  have : mk (Rm 1) = C (aX - 1) * mk Rm1' := by
    ext N; rw [coeff_mk, coeff_C_mul, coeff_mk, Rm1_fac]
  rw [zB, this, cpoly, ← mul_assoc, ← map_mul]; ring_nf

/-- the regular part of `x(1+t)`. -/
def eT : T := ιv (mk Rm0')
/-- the regular part of `θx(1+t)`. -/
def fT : T := ιv (mk Rm1')

lemma z0v_eq : ιv (zB 0) = (1 + tT) + tT ^ 4 * eT := by
  rw [zB0_fac, map_add, map_mul, ιv_C, ιv_C, eT]
  simp only [ev2, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, map_add, map_one, map_pow, add_sub_cancel_left]
lemma z1v_eq : ιv (zB 1) = -((1 + tT) * (2 + tT)) + tT ^ 4 * fT := by
  rw [zB1_fac, map_add, map_mul, ιv_C, ιv_C, fT]
  simp only [ev2, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    map_add, map_one, map_pow, map_neg, map_mul, add_sub_cancel_left]
  ring

/-! ### Relations from `ℤ[a]⟦b⟧` -/

lemma rel_img (ι : R2 →+* T) (m : ℕ) (hm : m ≤ 3) :
    ι vB * ι (Θ (zB m)) = ((m : T) + 2) * ι wB * ι (zB m) + ι (zB (m + 1)) := by
  have := congrArg ι (zB_rel m hm)
  rw [map_mul, map_add, map_mul, map_mul, map_add, map_natCast, map_ofNat] at this
  exact this

lemma curve_img (ι : R2 →+* T) :
    ι (zB 1) ^ 2 = 4 * ι (zB 0) ^ 3 + ι vB ^ 2 * ι (zB 0) ^ 2 + 4 * ι vB ^ 4 * ι a4B * ι (zB 0) +
      4 * ι vB ^ 6 * ι a6B := by
  have := congrArg ι EB_v
  simp only [map_mul, map_add, map_pow, map_ofNat] at this
  exact this

lemma z2_img (ι : R2 →+* T) :
    ι (zB 2) = 6 * ι (zB 0) ^ 2 + ι vB ^ 2 * ι (zB 0) + 2 * ι vB ^ 4 * ι a4B := by
  have := congrArg ι zB2_eq
  simp only [map_mul, map_add, map_pow, map_ofNat] at this
  exact this

/-! ### Units -/

/-- the triple constant coefficient. -/
def ε3 : T →+* ℚ := (constantCoeff (R := ℚ)).comp ((constantCoeff (R := k1)).comp (constantCoeff (R := k2)))

lemma isUnit_T {x : T} (h : ε3 x ≠ 0) : IsUnit x := by
  rw [isUnit_iff_constantCoeff, isUnit_iff_constantCoeff, isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr h

lemma ε3_tT : ε3 tT = 0 := by simp [ε3]
lemma ε3_aT : ε3 aT = 0 := by simp [ε3]

/-- `α = a − 1`. -/
abbrev αT : T := aT - 1
/-- `β = a(1+t) − 1`. -/
abbrev βT : T := aT * (1 + tT) - 1

lemma isUnit_αT : IsUnit αT := isUnit_T (by simp [ε3_aT])
lemma isUnit_βT : IsUnit βT := isUnit_T (by simp [ε3_aT, ε3_tT])

/-- `α⁻¹`. -/
def αi : T := Ring.inverse αT
/-- `β⁻¹`. -/
def βi : T := Ring.inverse βT

lemma hαi : αT * αi = 1 := Ring.mul_inverse_cancel _ isUnit_αT
lemma hβi : βT * βi = 1 := Ring.mul_inverse_cancel _ isUnit_βT

lemma D_αi : D αi = -(αi ^ 2 * aT) := by
  rw [isDer_D.inv hαi, isDer_D.sub, isDer_D.one, D_aT, sub_zero]
lemma D_βi : D βi = 0 := by
  rw [isDer_D.inv hβi, isDer_D.sub, isDer_D.one, isDer_D.mul, D_aT, D_one_add_tT]; ring

end TateAdd
