/-
# The norm of `ψ`: `Ẽ₁₁ · z = q⁵`

`φ = q⁵E(q¹²¹)/E(q)` is a root of `R(Y) = X⁵⁵ + Σ_j (−1)ʲ Ẽ_j(q¹¹) Yʲ`. Rescaling `q ↦ ζᵏq` fixes the
coefficients, so the eleven conjugates `φ(ζᵏq)` are roots too. They are distinct (their `q⁵` coefficients
are `ζ^{5k}`). Hence `X⁵⁵ = Ẽ₁₁(q¹¹)·∏_k φ(ζᵏq)`, and `prod_conj_E` evaluates the product as `z(q¹¹)`.
-/
import RamanujanTau.Atkin11CH
import RamanujanTau.Atkin11Conj
import RamanujanTau.Atkin11Roots
import RamanujanTau.Atkin11Final
import RamanujanTau.SPoly6Hom

set_option autoImplicit false

namespace Atkin11
open PowerSeries Atkin11Cert

/-- the coefficient `Ẽ_j(q¹¹)` at the evaluation point. -/
noncomputable def eE (p : SPoly6.Poly) : PS := SPoly6.evalP x6 p

/-- **Cayley–Hamilton for `Ψ`** (`Ψ = E(q)/E(q¹²¹)`). -/
theorem charpoly_Ψ : X ^ 55 * Ψd ^ 11 - eE CH_E1 * X ^ 5 * Ψd ^ 10 + eE CH_E2 * X ^ 10 * Ψd ^ 9 - eE CH_E3 * X ^ 15 * Ψd ^ 8 + eE CH_E4 * X ^ 20 * Ψd ^ 7 - eE CH_E5 * X ^ 25 * Ψd ^ 6 + eE CH_E6 * X ^ 30 * Ψd ^ 5 - eE CH_E7 * X ^ 35 * Ψd ^ 4 + eE CH_E8 * X ^ 40 * Ψd ^ 3 - eE CH_E9 * X ^ 45 * Ψd ^ 2 + eE CH_E10 * X ^ 50 * Ψd ^ 1 - eE CH_E11 * X ^ 55 * Ψd ^ 0 = 0 := by
  have h := SPoly6.certifyR_sound x6 _ _ CH_ok
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, eval_D, mul_zero] at h
  rw [horner _ _ _ _ _ CH_H11_ok (by norm_num), horner _ _ _ _ _ CH_H10_ok (by norm_num), horner _ _ _ _ _ CH_H9_ok (by norm_num), horner _ _ _ _ _ CH_H8_ok (by norm_num), horner _ _ _ _ _ CH_H7_ok (by norm_num), horner _ _ _ _ _ CH_H6_ok (by norm_num), horner _ _ _ _ _ CH_H5_ok (by norm_num), horner _ _ _ _ _ CH_H4_ok (by norm_num), horner _ _ _ _ _ CH_H3_ok (by norm_num), horner _ _ _ _ _ CH_H2_ok (by norm_num), horner _ _ _ _ _ CH_H1_ok (by norm_num), eval_H0] at h
  unfold eE
  push_cast at h
  linear_combination h

lemma φ_mul_Ψd : φ * Ψd = X ^ 5 := by
  rw [φ, show X ^ 5 * E121 * Ring.inverse E1 * Ψd = X ^ 5 * (E121 * Ψd) * Ring.inverse E1 by ring, ← E1_eq_Ψd,
    mul_assoc, Ring.mul_inverse_cancel _ isUnit_E1, mul_one]

/-- **the polynomial satisfied by `φ`.** -/
theorem charpoly_φ : X ^ 55 - eE CH_E1 * φ ^ 1 + eE CH_E2 * φ ^ 2 - eE CH_E3 * φ ^ 3 + eE CH_E4 * φ ^ 4 - eE CH_E5 * φ ^ 5 + eE CH_E6 * φ ^ 6 - eE CH_E7 * φ ^ 7 + eE CH_E8 * φ ^ 8 - eE CH_E9 * φ ^ 9 + eE CH_E10 * φ ^ 10 - eE CH_E11 * φ ^ 11 = 0 := by
  have h1 := charpoly_Ψ
  have h2 := φ_mul_Ψd
  have h3 : X ^ 55 * (X ^ 55 - eE CH_E1 * φ ^ 1 + eE CH_E2 * φ ^ 2 - eE CH_E3 * φ ^ 3 + eE CH_E4 * φ ^ 4 - eE CH_E5 * φ ^ 5 + eE CH_E6 * φ ^ 6 - eE CH_E7 * φ ^ 7 + eE CH_E8 * φ ^ 8 - eE CH_E9 * φ ^ 9 + eE CH_E10 * φ ^ 10 - eE CH_E11 * φ ^ 11) = 0 := by
    linear_combination φ ^ 11 * h1 + (-Ψd^10*X^55*φ^10 - Ψd^9*X^60*φ^9 + Ψd^9*X^5*eE CH_E1*φ^10 - Ψd^8*X^65*φ^8 + Ψd^8*X^10*eE CH_E1*φ^9 - Ψd^8*X^10*eE CH_E2*φ^10 - Ψd^7*X^70*φ^7 + Ψd^7*X^15*eE CH_E1*φ^8 - Ψd^7*X^15*eE CH_E2*φ^9 + Ψd^7*X^15*eE CH_E3*φ^10 - Ψd^6*X^75*φ^6 + Ψd^6*X^20*eE CH_E1*φ^7 - Ψd^6*X^20*eE CH_E2*φ^8 + Ψd^6*X^20*eE CH_E3*φ^9 - Ψd^6*X^20*eE CH_E4*φ^10 - Ψd^5*X^80*φ^5 + Ψd^5*X^25*eE CH_E1*φ^6 - Ψd^5*X^25*eE CH_E2*φ^7 + Ψd^5*X^25*eE CH_E3*φ^8 - Ψd^5*X^25*eE CH_E4*φ^9 + Ψd^5*X^25*eE CH_E5*φ^10 - Ψd^4*X^85*φ^4 + Ψd^4*X^30*eE CH_E1*φ^5 - Ψd^4*X^30*eE CH_E2*φ^6 + Ψd^4*X^30*eE CH_E3*φ^7 - Ψd^4*X^30*eE CH_E4*φ^8 + Ψd^4*X^30*eE CH_E5*φ^9 - Ψd^4*X^30*eE CH_E6*φ^10 - Ψd^3*X^90*φ^3 + Ψd^3*X^35*eE CH_E1*φ^4 - Ψd^3*X^35*eE CH_E2*φ^5 + Ψd^3*X^35*eE CH_E3*φ^6 - Ψd^3*X^35*eE CH_E4*φ^7 + Ψd^3*X^35*eE CH_E5*φ^8 - Ψd^3*X^35*eE CH_E6*φ^9 + Ψd^3*X^35*eE CH_E7*φ^10 - Ψd^2*X^95*φ^2 + Ψd^2*X^40*eE CH_E1*φ^3 - Ψd^2*X^40*eE CH_E2*φ^4 + Ψd^2*X^40*eE CH_E3*φ^5 - Ψd^2*X^40*eE CH_E4*φ^6 + Ψd^2*X^40*eE CH_E5*φ^7 - Ψd^2*X^40*eE CH_E6*φ^8 + Ψd^2*X^40*eE CH_E7*φ^9 - Ψd^2*X^40*eE CH_E8*φ^10 - Ψd*X^100*φ + Ψd*X^45*eE CH_E1*φ^2 - Ψd*X^45*eE CH_E2*φ^3 + Ψd*X^45*eE CH_E3*φ^4 - Ψd*X^45*eE CH_E4*φ^5 + Ψd*X^45*eE CH_E5*φ^6 - Ψd*X^45*eE CH_E6*φ^7 + Ψd*X^45*eE CH_E7*φ^8 - Ψd*X^45*eE CH_E8*φ^9 + Ψd*X^45*eE CH_E9*φ^10 - X^105 + X^50*eE CH_E1*φ - X^50*eE CH_E10*φ^10 - X^50*eE CH_E2*φ^2 + X^50*eE CH_E3*φ^3 - X^50*eE CH_E4*φ^4 + X^50*eE CH_E5*φ^5 - X^50*eE CH_E6*φ^6 + X^50*eE CH_E7*φ^7 - X^50*eE CH_E8*φ^8 + X^50*eE CH_E9*φ^9) * h2
  exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ X_ne_zero)

/-! ## coefficients are `V`-series -/

/-- `Ẽ_j` as a function of `j`. -/
def CHE : ℕ → SPoly6.Poly
  | 1 => CH_E1
  | 2 => CH_E2
  | 3 => CH_E3
  | 4 => CH_E4
  | 5 => CH_E5
  | 6 => CH_E6
  | 7 => CH_E7
  | 8 => CH_E8
  | 9 => CH_E9
  | 10 => CH_E10
  | 11 => CH_E11
  | _ => []

lemma qfree_1 : (CH_E1.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_2 : (CH_E2.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_3 : (CH_E3.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_4 : (CH_E4.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_5 : (CH_E5.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_6 : (CH_E6.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_7 : (CH_E7.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_8 : (CH_E8.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_9 : (CH_E9.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_10 : (CH_E10.all fun t => t.1 % 1024 == 0) = true := by decide +kernel
lemma qfree_11 : (CH_E11.all fun t => t.1 % 1024 == 0) = true := by decide +kernel

lemma qfree_CHE (j : ℕ) : ((CHE j).all fun t => t.1 % 1024 == 0) = true := by
  match j with
  | 0 => rfl
  | 1 => exact qfree_1
  | 2 => exact qfree_2
  | 3 => exact qfree_3
  | 4 => exact qfree_4
  | 5 => exact qfree_5
  | 6 => exact qfree_6
  | 7 => exact qfree_7
  | 8 => exact qfree_8
  | 9 => exact qfree_9
  | 10 => exact qfree_10
  | 11 => exact qfree_11
  | _ + 12 => rfl

lemma eE_V (p : SPoly6.Poly) (hq : (p.all fun t => t.1 % 1024 == 0) = true) : eE p = V (Et p) := by
  rw [Et, SPoly6.evalP_map V]
  simp only [List.map_cons, List.map_nil]
  rw [V_X', eE, x6]
  exact SPoly6.evalP_qfree _ _ _ _ hq

/-- the coefficients of `R`, before the `V`. -/
noncomputable def dZ (j : ℕ) : PS := if j = 0 then X ^ 5 else (-1) ^ j * Et (CHE j)

/-- `Σ_{j ≤ 11} V(d_j) φʲ = 0`. -/
theorem charpoly_sum : ∑ j ∈ Finset.range 12, V (dZ j) * φ ^ j = 0 := by
  have h := charpoly_φ
  simp only [eE_V CH_E1 qfree_1, eE_V CH_E2 qfree_2, eE_V CH_E3 qfree_3, eE_V CH_E4 qfree_4, eE_V CH_E5 qfree_5,
    eE_V CH_E6 qfree_6, eE_V CH_E7 qfree_7, eE_V CH_E8 qfree_8, eE_V CH_E9 qfree_9, eE_V CH_E10 qfree_10,
    eE_V CH_E11 qfree_11] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, dZ, CHE, map_mul, map_pow, map_neg, map_one, V_X']
  norm_num
  try rw [V_X']
  linear_combination h

/-! ## the conjugates -/

open Atkin11Conj MockTheta5.JTP

lemma ψC_V (g : PS) : ψC (V g) = expand 11 (by norm_num) (ψC g) := by
  ext n
  simp [ex, coeff_expand, coeff_map]

lemma rescale_ψC_V (k : ℕ) (g : PS) : rescale (ζ ^ k) (ψC (V g)) = ψC (V g) := by
  rw [ψC_V, rescale_expand]

/-- the polynomial `R(Y) = Σ_j ψC(V d_j) Yʲ` over `ℂ⟦q⟧`. -/
noncomputable def Rpoly : Polynomial (PowerSeries ℂ) :=
  ∑ j ∈ Finset.range 12, Polynomial.C (ψC (V (dZ j))) * Polynomial.X ^ j

lemma Rpoly_eval (y : PowerSeries ℂ) : Rpoly.eval y = ∑ j ∈ Finset.range 12, ψC (V (dZ j)) * y ^ j := by
  simp [Rpoly, Polynomial.eval_finsetSum]

lemma Rpoly_coeff (n : ℕ) : Rpoly.coeff n = if n < 12 then ψC (V (dZ n)) else 0 := by
  simp only [Rpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma Rpoly_natDegree : Rpoly.natDegree ≤ 11 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Rpoly_coeff, if_neg (by omega)]

/-- the conjugates `φ(ζᵏq)`. -/
noncomputable def rC (k : Fin 11) : PowerSeries ℂ := rescale (ζ ^ (k : ℕ)) (ψC φ)

lemma Rpoly_root (k : Fin 11) : Rpoly.eval (rC k) = 0 := by
  have h : rescale (ζ ^ (k : ℕ)) (ψC (∑ j ∈ Finset.range 12, V (dZ j) * φ ^ j)) = 0 := by
    rw [charpoly_sum, map_zero, map_zero]
  rw [map_sum, map_sum] at h
  simp only [map_mul, map_pow, rescale_ψC_V] at h
  rw [Rpoly_eval]
  exact h

lemma isUnit_φ_div : IsUnit (E121 * Ring.inverse E1) := isUnit_E121.mul (isUnit_inverse isUnit_E1)

lemma coeff5_φ_ne : coeff 5 (ψC φ) ≠ 0 := by
  rw [coeff_map, φ, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff]
  have hu := (isUnit_iff_constantCoeff.mp isUnit_φ_div)
  have : constantCoeff (E121 * Ring.inverse E1) ≠ 0 := hu.ne_zero
  simpa using this

lemma ζ5_prim : IsPrimitiveRoot (ζ ^ 5) 11 := ζ_prim.pow_of_coprime 5 (by norm_num)

lemma rC_injective : Function.Injective rC := by
  intro k k' h
  have h5 := congrArg (coeff 5) h
  simp only [rC, coeff_rescale] at h5
  have h6 : (ζ ^ 5) ^ (k : ℕ) = (ζ ^ 5) ^ (k' : ℕ) := by
    rw [← pow_mul, ← pow_mul, mul_comm 5, mul_comm 5, pow_mul, pow_mul]
    exact mul_right_cancel₀ coeff5_φ_ne h5
  exact Fin.ext (ζ5_prim.pow_inj k.2 k'.2 h6)

/-- `X⁵⁵ = Ẽ₁₁(q¹¹) · ∏_k φ(ζᵏq)`. -/
theorem norm_roots : ψC (X ^ 55) = ψC (V (Et CH_E11)) * ∏ k, rC k := by
  have h := Atkin11Roots.coeff_zero_of_roots (by norm_num : 1 ≤ 11) Rpoly Rpoly_natDegree rC rC_injective Rpoly_root
  rw [Rpoly_coeff, Rpoly_coeff, if_pos (by norm_num), if_pos (by norm_num)] at h
  simp only [dZ, if_true, show (11 : ℕ) ≠ 0 from by norm_num, if_false, CHE] at h
  rw [Finset.prod_neg] at h
  simp only [map_mul, map_pow, map_neg, map_one, V_X', Finset.card_univ, Fintype.card_fin] at h ⊢
  rw [show ψC X ^ 55 = (ψC X ^ 11) ^ 5 by ring, h]
  ring

lemma E121_expand : E121 = expand 121 (by norm_num) qfacInf :=
  (expand_mul 11 (by norm_num) 11 (by norm_num) qfacInf).symm

lemma φ_mul_E1 : φ * E1 = X ^ 5 * E121 := by
  rw [φ, mul_assoc, mul_assoc, Ring.inverse_mul_cancel _ isUnit_E1, mul_one]

lemma prod_ζ5 : ∏ k : Fin 11, (ζ ^ (k : ℕ)) ^ 5 = 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun k => (ζ ^ k) ^ 5) 11]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, ← pow_mul, ← pow_add]
  rw [show (0 * 5 + 1 * 5 + 2 * 5 + 3 * 5 + 4 * 5 + 5 * 5 + 6 * 5 + 7 * 5 + 8 * 5 + 9 * 5 + 10 * 5) = 11 * 25 by
    norm_num, pow_mul, ζ_pow11, one_pow]

/-- **`∏_k φ(ζᵏq) = z(q¹¹)`**. -/
theorem prod_rC : ∏ k, rC k = ψC (V z) := by
  have hE := prod_conj_E
  rw [← Fin.prod_univ_eq_prod_range (fun j => rescale (ζ ^ j) (ψC qfacInf)) 11] at hE
  have hk : ∀ k : Fin 11, rC k * rescale (ζ ^ (k : ℕ)) (ψC E1)
      = PowerSeries.C ((ζ ^ (k : ℕ)) ^ 5) * X ^ 5 * ψC E121 := by
    intro k
    have e1 : rescale (ζ ^ (k : ℕ)) (ψC E121) = ψC E121 := rescale_ψC_V _ (V E1)
    calc rC k * rescale (ζ ^ (k : ℕ)) (ψC E1) = rescale (ζ ^ (k : ℕ)) (ψC (φ * E1)) := by
          rw [rC, map_mul ψC, map_mul (rescale _)]
      _ = rescale (ζ ^ (k : ℕ)) (ψC X ^ 5) * rescale (ζ ^ (k : ℕ)) (ψC E121) := by
          rw [φ_mul_E1, map_mul, map_mul, map_pow]
      _ = _ := by rw [e1, map_X, map_pow, rescale_X, mul_pow, ← map_pow]
  have hprod : (∏ k, rC k) * (∏ k : Fin 11, rescale (ζ ^ (k : ℕ)) (ψC E1)) = X ^ 55 * ψC E121 ^ 11 := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← map_prod, prod_ζ5, map_one, one_mul]
    simp [Finset.prod_const, ← pow_mul]
  have hE' : (∏ k : Fin 11, rescale (ζ ^ (k : ℕ)) (ψC E1)) * ψC E121 = ψC E11 ^ 12 := by
    rw [E121_expand]; exact hE
  have hB : (∏ k, rC k) * ψC E11 ^ 12 = X ^ 55 * ψC E121 ^ 12 := by
    rw [← hE', ← mul_assoc, hprod]; ring
  have hz : ψC (V z) * ψC E11 ^ 12 = X ^ 55 * ψC E121 ^ 12 := by
    have h1 : E11 * Ring.inverse E11 = 1 := Ring.mul_inverse_cancel _ isUnit_E11
    have : V z * E11 ^ 12 = X ^ 55 * E121 ^ 12 := by
      simp only [z, map_mul, map_pow, V_X, V_inverse_E1, show V E11 = E121 from rfl]
      linear_combination (X ^ 11) ^ 5 * E121 ^ 12 * (1 + (E11 * Ring.inverse E11) + (E11 * Ring.inverse E11) ^ 2
        + (E11 * Ring.inverse E11) ^ 3 + (E11 * Ring.inverse E11) ^ 4 + (E11 * Ring.inverse E11) ^ 5
        + (E11 * Ring.inverse E11) ^ 6 + (E11 * Ring.inverse E11) ^ 7 + (E11 * Ring.inverse E11) ^ 8
        + (E11 * Ring.inverse E11) ^ 9 + (E11 * Ring.inverse E11) ^ 10 + (E11 * Ring.inverse E11) ^ 11) * h1
    have h2 := congrArg ψC this
    simpa [map_mul, map_pow] using h2
  have hne : ψC E11 ^ 12 ≠ 0 := pow_ne_zero _ ((isUnit_E11.map ψC).ne_zero)
  exact mul_right_cancel₀ hne (hB.trans hz.symm)

lemma V_injective : Function.Injective V := by
  intro f g h
  ext n
  have := congrArg (coeff (11 * n)) h
  simpa [coeff_ex] using this

/-- **The norm identity** `Ẽ₁₁ · z = q⁵`: `z = 1/e₁₁(ψ)`. -/
theorem norm_E11 : Et CH_E11 * z = X ^ 5 := by
  have h := norm_roots
  rw [prod_rC, ← map_mul, ← map_mul] at h
  have h2 := ψC_injective h
  apply V_injective
  rw [← h2, map_pow, V_X', ← pow_mul]

end Atkin11
