/-
# The Tate point at `u = w ∈ K^×` and its `θ`-derivatives, as series in `K⟦q⟧`

`evA w : ℤ[a]⟦b⟧ → K⟦q⟧` is `a ↦ w`, `b ↦ q/w`. `tx m w = θ^m x |_{u = w}`:
`tx m w = θ^m(u/(1−u)²)|_w + Σ_N Σ_{d∣N} d^{m+1} (w^d + (−1)^m w^{−d} − 2[m=0]) qᴺ`, and
* `tx_weier`: `(θx)² = 4x³ + x² + 4a₄x + 4a₆` (Tate's equation at `u = w`, `θx = 2y + x`),
* `tx_two`: `θ²x = 6x² + x + 2a₄`, `tx_four`: `θ⁴x = 120x³ + 30x² + (72a₄+1)x + 48a₆ + 2a₄`.
-/
import RamanujanTau.TateQuot.Cyclo

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

local notation "aX" => (Polynomial.X : P)

variable {K : Type*} [Field K]

/-- `a ↦ w`, `b ↦ q/w`. -/
def evA (w : K) : R2 →+* PowerSeries K :=
  (rescale w⁻¹).comp (PowerSeries.map (Polynomial.eval₂RingHom (Int.castRingHom K) w))

lemma coeff_evA (w : K) (F : R2) (N : ℕ) :
    coeff N (evA w F) = w⁻¹ ^ N * Polynomial.eval₂ (Int.castRingHom K) w (coeff N F) := by
  simp [evA, coeff_rescale]

lemma evA_C (w : K) (c : P) : evA w (C c) = C (Polynomial.eval₂ (Int.castRingHom K) w c) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, coeff_C, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

/-- `a₄` over `K`. -/
def a4K : PowerSeries K := PowerSeries.map (Int.castRingHom K) TateCurve.a4
/-- `a₆` over `K`. -/
def a6K : PowerSeries K := PowerSeries.map (Int.castRingHom K) TateCurve.a6

lemma evA_resc {w : K} (hw : w ≠ 0) (f : PowerSeries ℤ) :
    evA w (rescale aX (PowerSeries.map (Int.castRingHom P) f)) =
      PowerSeries.map (Int.castRingHom K) f := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, coeff_rescale, coeff_map, coeff_map]
  have hc : ∀ c : ℤ, Polynomial.eval₂ (Int.castRingHom K) w ((Int.castRingHom P) c) =
      (Int.castRingHom K) c := fun c => by
    rw [eq_intCast, ← Polynomial.C_eq_intCast, Polynomial.eval₂_C]; simp
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, hc]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hw, one_pow, one_mul]

lemma evA_a4B {w : K} (hw : w ≠ 0) : evA w a4B = a4K := evA_resc hw _
lemma evA_a6B {w : K} (hw : w ≠ 0) : evA w a6B = a6K := evA_resc hw _

/-- The `N`-th coefficient of `θ^m x` (non-constant part) at `u = w`. -/
def txc (m : ℕ) (w : K) (N : ℕ) : K :=
  ∑ d ∈ N.divisors, (d : K) ^ (m + 1) * (w ^ d + (-1) ^ m * w⁻¹ ^ d - if m = 0 then 2 else 0)

lemma evA_mk_Rm {w : K} (hw : w ≠ 0) (m : ℕ) : evA w (mk (Rm m)) = mk (txc m w) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_evA, coeff_mk, coeff_mk, Rm, txc, Polynomial.eval₂_finsetSum, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  have e1 : w ^ (N + d) = w ^ N * w ^ d := pow_add _ _ _
  have e2 : w ^ N = w ^ (N - d) * w ^ d := by rw [← pow_add, Nat.sub_add_cancel hdN]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_natCast, Polynomial.eval₂_neg, Polynomial.eval₂_one,
    apply_ite (Polynomial.eval₂ (Int.castRingHom K) w), Polynomial.eval₂_ofNat,
    Polynomial.eval₂_zero]
  rw [e1, e2]
  have hwd : w ^ d ≠ 0 := pow_ne_zero _ hw
  have hwNd : w ^ (N - d) ≠ 0 := pow_ne_zero _ hw
  rw [inv_pow, inv_pow, e2]
  field_simp

/-- `tx m w = θ^m x` at `u = w` (`= evA w (zB m) / (w−1)^{m+2}`). -/
def tx (m : ℕ) (w : K) : PowerSeries K := evA w (zB m) * C (((w - 1) ^ (m + 2))⁻¹)

lemma tx_eq {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) (m : ℕ) :
    tx m w = C (cK m w) + mk (txc m w) := by
  have h : ((w - 1) ^ (m + 2)) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw1)
  rw [tx, zB, map_add, map_mul, evA_C, evA_C, evA_mk_Rm hw, add_mul, mul_comm (C _) (mk _),
    mul_assoc, ← map_mul, ← map_mul, cK]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [mul_inv_cancel₀ h, map_one, mul_one, div_eq_mul_inv]

lemma evA_zB {w : K} (hw1 : w ≠ 1) (m : ℕ) :
    evA w (zB m) = tx m w * C (w - 1) ^ (m + 2) := by
  have h : ((w - 1) ^ (m + 2)) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw1)
  rw [tx, mul_assoc, ← map_pow, ← map_mul, inv_mul_cancel₀ h, map_one, mul_one]

lemma evA_vB (w : K) : evA w vB = C (w - 1) := by
  rw [evA_C]; simp
lemma evA_wB (w : K) : evA w wB = C w := by
  rw [evA_C]; simp

lemma Cw1_ne {w : K} (hw1 : w ≠ 1) : (C (w - 1) : PowerSeries K) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (C_injective)]; exact sub_ne_zero.mpr hw1

/-- Tate's equation at `u = w`: `(θx)² = 4x³ + x² + 4a₄x + 4a₆`. -/
theorem tx_weier {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) :
    tx 1 w ^ 2 = 4 * tx 0 w ^ 3 + tx 0 w ^ 2 + 4 * a4K * tx 0 w + 4 * a6K := by
  have h := congrArg (evA w) EB_v
  simp only [map_add, map_mul, map_pow, map_ofNat, evA_zB hw1, evA_vB, evA_a4B hw, evA_a6B hw] at h
  have hW := pow_ne_zero 6 (Cw1_ne hw1)
  apply mul_right_cancel₀ hW
  linear_combination h

/-- `θ²x = 6x² + x + 2a₄` at `u = w`. -/
theorem tx_two {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) :
    tx 2 w = 6 * tx 0 w ^ 2 + tx 0 w + 2 * a4K := by
  have h := congrArg (evA w) zB2_eq
  simp only [map_add, map_mul, map_pow, map_ofNat, evA_zB hw1, evA_vB, evA_a4B hw] at h
  have hW := pow_ne_zero 4 (Cw1_ne hw1)
  apply mul_right_cancel₀ hW
  linear_combination h

/-- `θ⁴x = 120x³ + 30x² + (72a₄+1)x + 48a₆ + 2a₄` at `u = w`. -/
theorem tx_four {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) :
    tx 4 w = 120 * tx 0 w ^ 3 + 30 * tx 0 w ^ 2 + (72 * a4K + 1) * tx 0 w + 48 * a6K + 2 * a4K := by
  have h := congrArg (evA w) zB4_eq
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, evA_zB hw1, evA_vB, evA_a4B hw,
    evA_a6B hw] at h
  have hW := pow_ne_zero 6 (Cw1_ne hw1)
  apply mul_right_cancel₀ hW
  linear_combination h

end TateQuot
