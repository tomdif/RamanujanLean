import RamanujanTau.Velu.Jets
import RamanujanTau.Velu.Sums
import Mathlib.Algebra.BigOperators.Field

/-!
# Vélu: Taylor coefficients of the regular part at a kernel point

For `Q₀ ∈ S`, the regular part `R(x) = x + Σ_{Q ∈ S, Q ≠ Q₀} φ_Q(x)` of Vélu's `X` at
`x₀ = x(Q₀)` has Taylor coefficients `R₀,…,R₃` given in closed form by the coordinates of
`Q₀` and `2Q₀` and by `t` — this is where the group structure of `G` enters.
-/

set_option linter.unusedSimpArgs false

namespace Velu

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

/-- Taylor coefficient of order `k` of `R = x + Σ_{Q≠Q₀} φ_Q` at `x(Q₀)`. -/
def Rj (Q0 : (short A B).Point) (k : ℕ) : K :=
  (if k = 0 then xc Q0 else if k = 1 then 1 else 0) +
    ∑ Q ∈ κ.S.erase Q0, jet k (xc Q0 - xc Q) (tQ Q) (uQ Q)

lemma jet_sum {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) (k : ℕ)
    (hk : k ≤ 3) :
    ∑ Q ∈ κ.S.erase Q0, jet k (xc Q0 - xc Q) (tQ Q) (uQ Q) =
      ∑ Q ∈ κ.S, (cj A (xc Q0) (yc Q0) k (xc Q) (yc Q) + cj A (xc Q0) (yc Q0) k (xc Q) (-yc Q))
        - cj A (xc Q0) (yc Q0) k (xc Q0) (yc Q0)
        - cj A (xc Q0) (yc Q0) k (xc (Q0 + Q0)) (yc (Q0 + Q0))
        - (if k = 0 then 2 * ∑ Q ∈ κ.S.erase Q0, xc Q else 0) := by
  have h0 : Q0 ≠ 0 := κ.ne_zero_of_mem_S hQ0
  have hy : yc Q0 ≠ 0 := κ.yc_ne_zero hQ0
  rw [Finset.sum_congr rfl (fun Q hQ => jet_point h0 (κ.ne_zero_of_mem_S (Finset.mem_of_mem_erase hQ))
    (κ.xc_ne_of_mem_S hQ0 (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm) hy h2 k hk)]
  rw [Finset.sum_sub_distrib]
  have hp := κ.sum_pairs (fun V => cj A (xc Q0) (yc Q0) k (xc V) (yc V)) hQ0
  simp only [xc_neg, yc_neg] at hp
  rw [hp]
  congr 1
  split_ifs with hk0
  · rw [Finset.mul_sum]
  · simp

variable {κ}

lemma Rj_zero {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) :
    κ.Rj Q0 0 = 2 * xc Q0 - xc (Q0 + Q0) := by
  rw [Rj, κ.jet_sum hQ0 h2 0 (by norm_num)]
  simp only [if_true, cj]
  rw [← Finset.add_sum_erase _ _ hQ0]
  rw [show ∑ x ∈ κ.S.erase Q0, (xc x + xc x) = 2 * ∑ x ∈ κ.S.erase Q0, xc x by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  ring

lemma Rj_one {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) :
    κ.Rj Q0 1 = -(yc (Q0 + Q0) / yc Q0) := by
  have hy : yc Q0 ≠ 0 := κ.yc_ne_zero hQ0
  rw [Rj, κ.jet_sum hQ0 h2 1 (by norm_num)]
  simp only [one_ne_zero, if_false, if_true, cj, sub_zero]
  rw [Finset.sum_eq_zero (fun Q _ => by ring), div_self hy]
  ring

lemma Rj_two {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) :
    κ.Rj Q0 2 = (κ.t - (3 * xc (Q0 + Q0) ^ 2 + A)) / (4 * yc Q0 ^ 2) +
      yc (Q0 + Q0) * (3 * xc Q0 ^ 2 + A) / (4 * yc Q0 ^ 3) := by
  have hy : yc Q0 ≠ 0 := κ.yc_ne_zero hQ0
  rw [Rj, κ.jet_sum hQ0 h2 2 (by norm_num)]
  simp only [show (2:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 0 by decide,
    show (3:ℕ) ≠ 1 by decide, if_false, cj, sub_zero, zero_add]
  rw [Finset.sum_congr rfl (fun Q _ => show
      (3 * xc Q ^ 2 + A) / (4 * yc Q0 ^ 2) - yc Q * (3 * xc Q0 ^ 2 + A) / (4 * yc Q0 ^ 3) +
        ((3 * xc Q ^ 2 + A) / (4 * yc Q0 ^ 2) - -yc Q * (3 * xc Q0 ^ 2 + A) / (4 * yc Q0 ^ 3)) =
      tQ Q / (4 * yc Q0 ^ 2) by rw [tQ]; ring), ← Finset.sum_div, t]
  field_simp
  ring

lemma Rj_three {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) :
    κ.Rj Q0 3 = -(κ.t * (3 * xc Q0 ^ 2 + A)) / (8 * yc Q0 ^ 4) -
      (xc (Q0 + Q0) * yc (Q0 + Q0) / (2 * yc Q0 ^ 3) -
        (3 * xc (Q0 + Q0) ^ 2 + A) * (3 * xc Q0 ^ 2 + A) / (8 * yc Q0 ^ 4)
        - yc (Q0 + Q0) * xc Q0 / (2 * yc Q0 ^ 3) +
        yc (Q0 + Q0) * (3 * xc Q0 ^ 2 + A) ^ 2 / (8 * yc Q0 ^ 5)) := by
  have hy : yc Q0 ≠ 0 := κ.yc_ne_zero hQ0
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h2 h4
  rw [Rj, κ.jet_sum hQ0 h2 3 (by norm_num)]
  simp only [show (2:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 0 by decide,
    show (3:ℕ) ≠ 1 by decide, if_false, cj, sub_zero, zero_add]
  rw [Finset.sum_congr rfl (fun Q _ => show
      xc Q * yc Q / (2 * yc Q0 ^ 3) - (3 * xc Q ^ 2 + A) * (3 * xc Q0 ^ 2 + A) / (8 * yc Q0 ^ 4) -
            yc Q * xc Q0 / (2 * yc Q0 ^ 3) + yc Q * (3 * xc Q0 ^ 2 + A) ^ 2 / (8 * yc Q0 ^ 5) +
        (xc Q * -yc Q / (2 * yc Q0 ^ 3) -
            (3 * xc Q ^ 2 + A) * (3 * xc Q0 ^ 2 + A) / (8 * yc Q0 ^ 4) -
            -yc Q * xc Q0 / (2 * yc Q0 ^ 3) + -yc Q * (3 * xc Q0 ^ 2 + A) ^ 2 / (8 * yc Q0 ^ 5)) =
      -(tQ Q * (3 * xc Q0 ^ 2 + A)) / (8 * yc Q0 ^ 4) by rw [tQ]; ring),
    ← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul, t]
  field_simp
  ring

end Kernel

end Velu
