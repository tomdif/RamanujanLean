/-
# The diagonal `R⟦s⟧⟦b⟧ → R⟦s⟧`, `b ↦ s`

`diag F = Σ_j F_j(s) s^j`, i.e. `[s^m] diag F = Σ_{j ≤ m} [s^{m−j}] F_j`. It is a ring homomorphism
(`diagHom`): the `m`-th coefficient only sees the truncation `F mod b^{m+1}`, on which `diag` is
polynomial evaluation at `b = s`.
-/
import Mathlib

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

variable {R : Type*} [CommRing R]

/-- `Σ_j F_j(s) s^j`. -/
def diag (F : PowerSeries (PowerSeries R)) : PowerSeries R :=
  mk fun m => ∑ j ∈ range (m + 1), coeff (m - j) (coeff j F)

lemma coeff_diag (F : PowerSeries (PowerSeries R)) (m : ℕ) :
    coeff m (diag F) = ∑ j ∈ range (m + 1), coeff (m - j) (coeff j F) := coeff_mk _ _

/-- `[s^m] P(s) = Σ_{j ≤ m} [s^{m−j}] P_j` for a polynomial `P ∈ R⟦s⟧[b]`. -/
lemma coeff_eval_X (P : Polynomial (PowerSeries R)) (m : ℕ) :
    coeff m (P.eval X) = ∑ j ∈ range (m + 1), coeff (m - j) (P.coeff j) := by
  set n := max (P.natDegree + 1) (m + 1)
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < n), map_sum]
  simp only [coeff_mul_X_pow']
  rw [← sum_range_add_sum_Ico _ (by omega : m + 1 ≤ n)]
  rw [sum_eq_zero (s := Ico (m + 1) n) fun j hj => by rw [mem_Ico] at hj; rw [if_neg (by omega)],
    add_zero]
  exact sum_congr rfl fun j hj => by rw [mem_range] at hj; rw [if_pos (by omega)]

lemma coeff_diag_eq (F : PowerSeries (PowerSeries R)) {m a : ℕ} (ha : a ≤ m) :
    coeff a ((trunc (m + 1) F).eval X) = coeff a (diag F) := by
  rw [coeff_eval_X, coeff_diag]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [coeff_trunc, if_pos (by omega)]

lemma diag_mul (F G : PowerSeries (PowerSeries R)) : diag (F * G) = diag F * diag G := by
  refine PowerSeries.ext fun m => ?_
  have h1 : coeff m (diag (F * G)) = coeff m ((trunc (m + 1) F * trunc (m + 1) G).eval X) := by
    rw [coeff_diag, coeff_eval_X]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    congr 1
    have := congrArg (fun P => Polynomial.coeff P j) (trunc_trunc_mul_trunc (n := m + 1) F G)
    simp only [coeff_trunc, if_pos hj] at this
    rw [← this, ← Polynomial.coeff_coe, Polynomial.coe_mul]
  rw [h1, Polynomial.eval_mul, coeff_mul, coeff_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  rw [coeff_diag_eq F (by omega), coeff_diag_eq G (by omega)]

lemma diag_add (F G : PowerSeries (PowerSeries R)) : diag (F + G) = diag F + diag G := by
  refine PowerSeries.ext fun m => ?_
  simp only [coeff_diag, map_add, sum_add_distrib]

lemma diag_C (g : PowerSeries R) : diag (C g) = g := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_diag, sum_range_succ', sum_eq_zero fun j _ => by rw [coeff_C, if_neg (by omega),
    map_zero]]
  simp

/-- The diagonal as a ring homomorphism. -/
def diagHom : PowerSeries (PowerSeries R) →+* PowerSeries R where
  toFun := diag
  map_one' := by rw [← map_one C, diag_C]
  map_mul' := diag_mul
  map_zero' := by rw [← map_zero C, diag_C]
  map_add' := diag_add

lemma diagHom_apply (F : PowerSeries (PowerSeries R)) : diagHom F = diag F := rfl

end TateQuot
