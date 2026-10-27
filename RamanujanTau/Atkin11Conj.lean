/-
# Atkin 11^k: the eleven conjugates `q ↦ ζʲq`

With `ζ = e^{2πi/11}`, for `F ∈ ℂ⟦q⟧`:
* `Σ_{j<11} F(ζʲq) = 11 · (U₁₁F)(q¹¹)` (`sum_conj`);
* the Euler factors: `∏_{j<11} (1 − (ζʲq)ⁿ) = 1 − q^{11n}` for `11 ∤ n` and `(1 − qⁿ)¹¹` for `11 ∣ n`.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.NormNum.Prime
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import RamanujanTau.RamanujanMostBeautiful

set_option autoImplicit false

namespace Atkin11Conj
open PowerSeries Finset

noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

lemma ζ_prim : IsPrimitiveRoot ζ 11 := Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma ζ_pow11 : ζ ^ 11 = 1 := ζ_prim.pow_eq_one

/-- `Σ_{j<11} (ζʲ)ⁿ = 11·[11 ∣ n]`. -/
lemma sum_roots (n : ℕ) : ∑ j ∈ range 11, (ζ ^ j) ^ n = if 11 ∣ n then 11 else 0 := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have : ∀ x : ℕ, (ζ ^ x) ^ (11 * m) = 1 := fun x => by
      rw [← pow_mul, show x * (11 * m) = 11 * (x * m) by ring, pow_mul, ζ_pow11, one_pow]
    simp only [this, sum_const, card_range]; norm_num
  · have hω : IsPrimitiveRoot (ζ ^ n) 11 := ζ_prim.pow_of_coprime n
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 11)).mpr h)))
    have := hω.geom_sum_eq_zero (by norm_num)
    rw [← this]
    refine sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]

/-- `U₁₁` on `ℂ⟦q⟧`. -/
noncomputable def UC (F : PowerSeries ℂ) : PowerSeries ℂ := mk fun n => coeff (11 * n) F

/-- **averaging over the conjugates**. -/
theorem sum_conj (F : PowerSeries ℂ) :
    ∑ j ∈ range 11, rescale (ζ ^ j) F = C (11 : ℂ) * expand 11 (by norm_num) (UC F) := by
  ext n
  rw [map_sum, coeff_C_mul, coeff_expand]
  simp only [coeff_rescale]
  rw [← sum_mul, sum_roots]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [UC, coeff_mk, Nat.mul_div_cancel_left _ (by norm_num)]
  · simp

lemma rescale_expand (j : ℕ) (G : PowerSeries ℂ) : rescale (ζ ^ j) (expand 11 (by norm_num) G) = expand 11 (by norm_num) G := by
  ext n
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [← pow_mul, show j * (11 * m) = 11 * (j * m) by ring, pow_mul, ζ_pow11, one_pow, one_mul]
  · simp

open Classical in
/-- the Euler factors over the conjugates. -/
lemma prod_factor (n : ℕ) :
    ∏ j ∈ range 11, (1 - C ((ζ ^ j) ^ n) * X ^ n : PowerSeries ℂ)
      = if 11 ∣ n then (1 - X ^ n) ^ 11 else 1 - X ^ (11 * n) := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hj : ∀ j : ℕ, (ζ ^ j) ^ (11 * m) = 1 := fun j => by
      rw [← pow_mul, show j * (11 * m) = 11 * (j * m) by ring, pow_mul, ζ_pow11, one_pow]
    simp [hj]
  · have hω : IsPrimitiveRoot (ζ ^ n) 11 := ζ_prim.pow_of_coprime n
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 11)).mpr h)))
    have hωC : IsPrimitiveRoot (C (ζ ^ n) : PowerSeries ℂ) 11 := hω.map_of_injective (C_injective)
    have key := hωC.pow_sub_pow_eq_prod_sub_mul (x := (1 : PowerSeries ℂ)) (y := X ^ n) (by norm_num)
    rw [one_pow, ← pow_mul, mul_comm n 11] at key
    rw [key]
    -- reindex the 11th roots of unity of `ℂ⟦q⟧` by powers of `C (ζⁿ)`
    have himg : Polynomial.nthRootsFinset 11 (1 : PowerSeries ℂ) = (range 11).image fun j => (C (ζ ^ n)) ^ j := by
      ext x
      rw [Polynomial.mem_nthRootsFinset (by norm_num), mem_image]
      constructor
      · intro hx
        obtain ⟨j, hj, rfl⟩ := hωC.eq_pow_of_pow_eq_one hx
        exact ⟨j, mem_range.mpr hj, rfl⟩
      · rintro ⟨j, -, rfl⟩
        rw [← pow_mul, mul_comm, pow_mul, hωC.pow_eq_one, one_pow]
    rw [himg, prod_image]
    · refine prod_congr rfl fun j _ => ?_
      rw [← map_pow, ← pow_mul, ← pow_mul, mul_comm n j]
    · intro a ha b hb hab
      exact hωC.pow_inj (mem_range.mp ha) (mem_range.mp hb) hab

/-! ### the product of the conjugates of `E` -/

local notation "ψC" => MockTheta5.JTP.ψC

noncomputable def Gfac (n : ℕ) : PowerSeries ℂ := if 11 ∣ n then (1 - X ^ n) ^ 11 else 1 - X ^ (11 * n)

lemma rescale_qfac_prod (N : ℕ) :
    ∏ j ∈ range 11, rescale (ζ ^ j) (ψC (MockTheta5.Bailey.qfac N)) = ∏ k ∈ range N, Gfac (k + 1) := by
  have h1 : ∀ j, rescale (ζ ^ j) (ψC (MockTheta5.Bailey.qfac N))
      = ∏ k ∈ range N, (1 - C ((ζ ^ j) ^ (k + 1)) * X ^ (k + 1)) := by
    intro j
    rw [MockTheta5.Bailey.qfac, map_prod, map_prod]
    refine prod_congr rfl fun k _ => ?_
    rw [map_sub, map_one, map_pow, PowerSeries.map_X, map_sub, map_one, map_pow, rescale_X, mul_pow, ← map_pow]
  simp only [h1]
  rw [prod_comm]
  refine prod_congr rfl fun k _ => ?_
  rw [prod_factor, Gfac]

lemma block_identity : ∀ M : ℕ,
    (∏ k ∈ range (11 * M), Gfac (k + 1)) * ∏ i ∈ range M, (1 - (X : PowerSeries ℂ) ^ (121 * (i + 1)))
      = (∏ k ∈ range (11 * M), (1 - (X : PowerSeries ℂ) ^ (11 * (k + 1))))
        * (∏ i ∈ range M, (1 - (X : PowerSeries ℂ) ^ (11 * (i + 1)))) ^ 11 := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [show 11 * (M + 1) = 11 * M + 11 by ring, prod_range_add (fun k => Gfac (k + 1)),
        prod_range_add (fun k => 1 - (X : PowerSeries ℂ) ^ (11 * (k + 1))),
        prod_range_succ (fun i => 1 - (X : PowerSeries ℂ) ^ (121 * (i + 1))) M,
        prod_range_succ (fun i => 1 - (X : PowerSeries ℂ) ^ (11 * (i + 1))) M,
        prod_range_succ (fun r => Gfac (11 * M + r + 1)) 10,
        prod_range_succ (fun r => 1 - (X : PowerSeries ℂ) ^ (11 * (11 * M + r + 1))) 10]
      have hg : ∏ r ∈ range 10, Gfac (11 * M + r + 1) = ∏ r ∈ range 10, (1 - (X : PowerSeries ℂ) ^ (11 * (11 * M + r + 1))) :=
        prod_congr rfl fun r hr => by rw [Gfac, if_neg (by have := mem_range.mp hr; omega)]
      have g10 : Gfac (11 * M + 10 + 1) = (1 - X ^ (11 * M + 10 + 1)) ^ 11 := by rw [Gfac, if_pos (by omega)]
      rw [hg, g10]
      have e1 : (X : PowerSeries ℂ) ^ (121 * (M + 1)) = X ^ (11 * (11 * M + 10 + 1)) := by ring
      have e2 : (X : PowerSeries ℂ) ^ (11 * (M + 1)) = X ^ (11 * M + 10 + 1) := by ring
      rw [e1, e2]
      linear_combination (∏ r ∈ range 10, (1 - (X : PowerSeries ℂ) ^ (11 * (11 * M + r + 1))))
        * (1 - X ^ (11 * M + 10 + 1)) ^ 11 * (1 - X ^ (11 * (11 * M + 10 + 1))) * ih

open MockTheta5.JTP (qfacInf X_pow_dvd_qfacInf_sub X_pow_dvd_ψC X_pow_dvd_rescale dvd_sub_mul' dvd_sub_pow')

lemma X_pow_dvd_expand {K p : ℕ} (hp : p ≠ 0) {f : PowerSeries ℤ} (h : X ^ K ∣ f) :
    (X : PowerSeries ℤ) ^ K ∣ PowerSeries.expand p hp f := by
  obtain ⟨d, rfl⟩ := h
  refine ⟨X ^ ((p - 1) * K) * PowerSeries.expand p hp d, ?_⟩
  rw [map_mul, map_pow, PowerSeries.expand_X, ← pow_mul, ← mul_assoc, ← pow_add]
  congr 2
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  simp; ring

lemma dvd_sub_prod_range {K : ℕ} (F G : ℕ → PowerSeries ℂ) (h : ∀ j, (X : PowerSeries ℂ) ^ K ∣ F j - G j) :
    ∀ n, (X : PowerSeries ℂ) ^ K ∣ ∏ j ∈ range n, F j - ∏ j ∈ range n, G j
  | 0 => by simp
  | n + 1 => by rw [prod_range_succ, prod_range_succ]; exact dvd_sub_mul' (dvd_sub_prod_range F G h n) (h n)

lemma ψC_expand_qfac (p : ℕ) (hp : p ≠ 0) (N : ℕ) :
    ψC (PowerSeries.expand p hp (MockTheta5.Bailey.qfac N)) = ∏ i ∈ range N, (1 - (X : PowerSeries ℂ) ^ (p * (i + 1))) := by
  rw [MockTheta5.Bailey.qfac, map_prod, map_prod]
  refine prod_congr rfl fun i _ => ?_
  simp only [map_sub, map_one, map_pow, PowerSeries.expand_X, PowerSeries.map_X, ← pow_mul]

/-- **the product of the eleven conjugates of `E`**: `∏_j E(ζʲq) · E(q¹²¹) = E(q¹¹)¹²`. -/
theorem prod_conj_E :
    (∏ j ∈ range 11, rescale (ζ ^ j) (ψC qfacInf)) * ψC (PowerSeries.expand 121 (by norm_num) qfacInf)
      = ψC (PowerSeries.expand 11 (by norm_num) qfacInf) ^ 12 := by
  rw [← sub_eq_zero]
  ext k
  rw [map_zero]
  set K := k + 1
  have hfin : (∏ j ∈ range 11, rescale (ζ ^ j) (ψC (MockTheta5.Bailey.qfac (11 * K))))
        * ψC (PowerSeries.expand 121 (by norm_num) (MockTheta5.Bailey.qfac K))
      = ψC (PowerSeries.expand 11 (by norm_num) (MockTheta5.Bailey.qfac (11 * K)))
        * ψC (PowerSeries.expand 11 (by norm_num) (MockTheta5.Bailey.qfac K)) ^ 11 := by
    rw [rescale_qfac_prod, ψC_expand_qfac, ψC_expand_qfac, ψC_expand_qfac, block_identity]
  have hL : (X : PowerSeries ℂ) ^ K ∣ (∏ j ∈ range 11, rescale (ζ ^ j) (ψC qfacInf))
        * ψC (PowerSeries.expand 121 (by norm_num) qfacInf)
      - (∏ j ∈ range 11, rescale (ζ ^ j) (ψC (MockTheta5.Bailey.qfac (11 * K))))
        * ψC (PowerSeries.expand 121 (by norm_num) (MockTheta5.Bailey.qfac K)) := by
    refine dvd_sub_mul' (dvd_sub_prod_range _ _ (fun j => ?_) 11) ?_
    · rw [← map_sub]; exact X_pow_dvd_rescale _ (by rw [← map_sub]; exact X_pow_dvd_ψC (X_pow_dvd_qfacInf_sub K _ (by omega)))
    · rw [← map_sub]; exact X_pow_dvd_ψC (by rw [← map_sub]; exact X_pow_dvd_expand _ (X_pow_dvd_qfacInf_sub K K le_rfl))
  have hR : (X : PowerSeries ℂ) ^ K ∣ ψC (PowerSeries.expand 11 (by norm_num) qfacInf) ^ 12
      - ψC (PowerSeries.expand 11 (by norm_num) (MockTheta5.Bailey.qfac (11 * K)))
        * ψC (PowerSeries.expand 11 (by norm_num) (MockTheta5.Bailey.qfac K)) ^ 11 := by
    rw [show ψC (PowerSeries.expand 11 (by norm_num) qfacInf) ^ 12
        = ψC (PowerSeries.expand 11 (by norm_num) qfacInf) * ψC (PowerSeries.expand 11 (by norm_num) qfacInf) ^ 11 by ring]
    refine dvd_sub_mul' ?_ (dvd_sub_pow' 11 ?_)
    · rw [← map_sub]; exact X_pow_dvd_ψC (by rw [← map_sub]; exact X_pow_dvd_expand _ (X_pow_dvd_qfacInf_sub K _ (by omega)))
    · rw [← map_sub]; exact X_pow_dvd_ψC (by rw [← map_sub]; exact X_pow_dvd_expand _ (X_pow_dvd_qfacInf_sub K K le_rfl))
  have htot := dvd_sub hL hR
  rw [hfin, show ∀ a b c : PowerSeries ℂ, a - c - (b - c) = a - b by intros; ring] at htot
  obtain ⟨d, hd⟩ := htot
  rw [hd, coeff_X_pow_mul', if_neg (by omega)]

end Atkin11Conj
