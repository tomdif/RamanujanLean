/-
# Stabilized residue-class q-Pochhammer products

This module defines `(q^a;q^d)_inf = prod_{k>=0}(1-q^(a+dk))` as a formal power series by
coefficient stabilization.  Lists of `(a,d)` pairs give finite products with multiplicity,
which is convenient for collecting the five factors in specialized quintuple products.
No analytic convergence and no `sorry`.
-/
import RamanujanTau.MockTheta5JacobiTriple
import Mathlib.RingTheory.PowerSeries.Expand

namespace Ramanujan.MultiQuintuple
open PowerSeries
open MockTheta5.JTP
open MockTheta5.Bailey

/-- Finite truncation of `(q^a;q^d)_inf`. -/
noncomputable def pochhammerFinite (a d N : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range N, (1 - X ^ (a + d * k))

lemma pochhammerFinite_succ (a d N : ℕ) :
    pochhammerFinite a d (N + 1)
      = pochhammerFinite a d N * (1 - X ^ (a + d * N)) := by
  rw [pochhammerFinite, pochhammerFinite, Finset.prod_range_succ]

/-- A diagonal residue product is an expanded finite Euler product. -/
lemma pochhammerFinite_diag (d N : ℕ) (hd : 0 < d) :
    pochhammerFinite d d N = PowerSeries.expand d hd.ne' (qfac N) := by
  rw [pochhammerFinite, qfac, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  congr 2
  ring

/-- Coefficients stabilize once every newly added exponent is above the coefficient degree. -/
lemma coeff_pochhammerFinite_stable {a d k : ℕ} (ha : 0 < a) (hd : 0 < d) :
    ∀ {M N : ℕ}, k < M → M ≤ N →
      coeff k (pochhammerFinite a d N) = coeff k (pochhammerFinite a d M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [pochhammerFinite_succ, mul_sub, mul_one, map_sub]
        have hN : N ≤ d * N := Nat.le_mul_of_pos_left N hd
        have hz : coeff k (pochhammerFinite a d N * X ^ (a + d * N)) = 0 := by
          rw [mul_comm]
          exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ k (by omega)
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- `(q^a;q^d)_inf`, defined coefficientwise from a stable finite truncation. -/
noncomputable def pochhammerInf (a d : ℕ) : PowerSeries ℤ :=
  mk fun k => coeff k (pochhammerFinite a d (k + 1))

/-- Any sufficiently long truncation computes a coefficient of `(q^a;q^d)_inf`. -/
lemma coeff_pochhammerInf {a d k N : ℕ} (ha : 0 < a) (hd : 0 < d) (hN : k + 1 ≤ N) :
    coeff k (pochhammerInf a d) = coeff k (pochhammerFinite a d N) := by
  rw [pochhammerInf, coeff_mk,
    coeff_pochhammerFinite_stable ha hd (Nat.lt_succ_self k) hN]

@[simp] lemma coeff_zero_pochhammerInf {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    coeff 0 (pochhammerInf a d) = 1 := by
  rw [coeff_pochhammerInf ha hd (le_refl 1), pochhammerFinite, Finset.prod_range_one]
  simp [ha.ne']

lemma isUnit_pochhammerInf {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    IsUnit (pochhammerInf a d) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    coeff_zero_pochhammerInf ha hd]
  exact isUnit_one

/-- A list product of residue-class Pochhammer factors; lists retain repeated factors. -/
noncomputable def pochhammerProductInf (factors : List (ℕ × ℕ)) : PowerSeries ℤ :=
  (factors.map fun factor => pochhammerInf factor.1 factor.2).prod

/-- The matching product of finite truncations. -/
noncomputable def pochhammerProductFinite (factors : List (ℕ × ℕ)) (N : ℕ) : PowerSeries ℤ :=
  (factors.map fun factor => pochhammerFinite factor.1 factor.2 N).prod

/-- Coefficientwise stabilization for a finite list of Pochhammer products. -/
lemma coeff_pochhammerProductInf {factors : List (ℕ × ℕ)}
    (hvalid : ∀ factor ∈ factors, 0 < factor.1 ∧ 0 < factor.2) {k N : ℕ}
    (hN : k + 1 ≤ N) :
    coeff k (pochhammerProductInf factors)
      = coeff k (pochhammerProductFinite factors N) := by
  induction factors generalizing k with
  | nil => simp [pochhammerProductInf, pochhammerProductFinite]
  | cons factor factors ih =>
      have hfactor : 0 < factor.1 ∧ 0 < factor.2 := hvalid factor (by simp)
      have hfactors : ∀ entry ∈ factors, 0 < entry.1 ∧ 0 < entry.2 := by
        intro entry hentry
        exact hvalid entry (by simp [hentry])
      change coeff k (pochhammerInf factor.1 factor.2 * pochhammerProductInf factors)
        = coeff k (pochhammerFinite factor.1 factor.2 N * pochhammerProductFinite factors N)
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun pair hpair => ?_
      have hpair_sum : pair.1 + pair.2 = k := Finset.mem_antidiagonal.mp hpair
      rw [coeff_pochhammerInf hfactor.1 hfactor.2 (show pair.1 + 1 ≤ N by omega),
        ih hfactors (show pair.2 + 1 ≤ N by omega)]

/-- The product attached to the paper's specialization `Q(q^i,q^p)`:
`(q^i,q^(p-i),q^p;q^p)_inf (q^(p+2i),q^(p-2i);q^(2p))_inf`. -/
noncomputable def quintupleSpecialized (p i : ℕ) : PowerSeries ℤ :=
  pochhammerProductInf
    [(i, p), (p - i, p), (p, p), (p + 2 * i, 2 * p), (p - 2 * i, 2 * p)]

end Ramanujan.MultiQuintuple
