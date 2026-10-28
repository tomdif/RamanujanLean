/-
# The derivation `D = a∂_a − (1+X)∂_X` on `T = ℚ⟦a⟧⟦X⟧⟦b⟧` and uniqueness

`k1 = ℚ⟦a⟧`, `k2 = k1⟦X⟧`, `T = k2⟦b⟧`. `D` acts coefficientwise in `b`. Under `c = 1 + X` it is
`a∂_a − c∂_c`, which fixes `q = acb`. (Derivations are plain additive Leibniz maps `IsDer`.)

`eq_zero_of_D`: if `D g = 0` and `g` vanishes at `X = 0` then `g = 0`.
-/
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries

/-! ### Additive Leibniz maps -/

section IsDer

variable {R : Type*} [CommRing R]

/-- `δ` is additive and satisfies Leibniz. -/
structure IsDer (δ : R → R) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x

variable {δ : R → R} (hδ : IsDer δ)
include hδ

lemma IsDer.zero : δ 0 = 0 := by
  have := hδ.add 0 0; simp only [add_zero] at this
  linear_combination -this

lemma IsDer.one : δ 1 = 0 := by
  have := hδ.mul 1 1; simp only [mul_one, one_mul] at this
  linear_combination -this

lemma IsDer.neg (x : R) : δ (-x) = -δ x := by
  have := hδ.add x (-x); rw [add_neg_cancel, hδ.zero] at this
  linear_combination -this

lemma IsDer.sub (x y : R) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, hδ.add, hδ.neg, ← sub_eq_add_neg]

lemma IsDer.natCast (n : ℕ) : δ (n : R) = 0 := by
  induction n with
  | zero => simpa using hδ.zero
  | succ n ih => rw [Nat.cast_succ, hδ.add, ih, hδ.one, add_zero]

lemma IsDer.ofNat (n : ℕ) [n.AtLeastTwo] : δ (OfNat.ofNat n : R) = 0 := hδ.natCast n

lemma IsDer.pow (x : R) (n : ℕ) : δ (x ^ (n + 1)) = ((n : R) + 1) * x ^ n * δ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hδ.mul, ih]; push_cast; ring

lemma IsDer.sq (x : R) : δ (x ^ 2) = 2 * x * δ x := by
  rw [hδ.pow x 1]; norm_num

lemma IsDer.cube (x : R) : δ (x ^ 3) = 3 * x ^ 2 * δ x := by
  rw [hδ.pow x 2]; norm_num

lemma IsDer.inv {x y : R} (h : x * y = 1) : δ y = -(y ^ 2 * δ x) := by
  have := hδ.mul x y; rw [h, hδ.one] at this
  linear_combination (-y) * this - δ y * h

end IsDer

/-! ### Coefficientwise lift -/

section Lift

variable {R : Type*} [CommRing R]

/-- coefficientwise application of a map. -/
def liftF (δ : R → R) (f : PowerSeries R) : PowerSeries R := mk fun n => δ (coeff n f)

lemma coeff_liftF (δ : R → R) (f : PowerSeries R) (n : ℕ) :
    coeff n (liftF δ f) = δ (coeff n f) := coeff_mk _ _

lemma IsDer.lift {δ : R → R} (hδ : IsDer δ) : IsDer (liftF δ) where
  add f g := by ext n; simp [coeff_liftF, hδ.add]
  mul f g := by
    refine PowerSeries.ext fun N => ?_
    rw [map_add, coeff_liftF, coeff_mul, coeff_mul, coeff_mul]
    rw [show (∑ x ∈ Finset.antidiagonal N, coeff x.1 g * coeff x.2 (liftF δ f)) =
        ∑ x ∈ Finset.antidiagonal N, coeff x.2 g * coeff x.1 (liftF δ f) from
      Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (by simp [add_comm]) (by simp)]
    rw [← Finset.sum_add_distrib]
    have hs : ∀ (s : Finset (ℕ × ℕ)) (h : ℕ × ℕ → R), δ (∑ x ∈ s, h x) = ∑ x ∈ s, δ (h x) := by
      intro s h
      induction s using Finset.induction_on with
      | empty => simpa using hδ.zero
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hδ.add, ih]
    rw [hs]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [coeff_liftF, coeff_liftF, hδ.mul]

lemma liftF_C {δ : R → R} (hδ : IsDer δ) (r : R) : liftF δ (C r) = C (δ r) := by
  ext n; rw [coeff_liftF, coeff_C, coeff_C]; split_ifs <;> simp [hδ.zero]

end Lift

/-! ### The rings and the derivation -/

/-- `ℚ⟦a⟧`. -/
abbrev k1 := PowerSeries ℚ
/-- `ℚ⟦a⟧⟦X⟧`. -/
abbrev k2 := PowerSeries k1
/-- `T = ℚ⟦a⟧⟦X⟧⟦b⟧`. -/
abbrev T := PowerSeries k2

lemma isDer_derivative {R : Type*} [CommRing R] : IsDer (derivative R) where
  add := map_add _
  mul x y := by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-- `a d/da` on `ℚ⟦a⟧`. -/
def aδ (f : k1) : k1 := X * derivative ℚ f

lemma isDer_aδ : IsDer aδ where
  add f g := by simp [aδ, mul_add]
  mul f g := by simp only [aδ, Derivation.leibniz, smul_eq_mul]; ring

lemma aδ_X : aδ (X : k1) = X := by simp [aδ]

/-- `D' = a∂_a − (1+X)∂_X` on `ℚ⟦a⟧⟦X⟧`. -/
def D' (g : k2) : k2 := liftF aδ g - (1 + X) * derivative k1 g

lemma isDer_D' : IsDer D' where
  add f g := by simp only [D', isDer_aδ.lift.add, map_add]; ring
  mul f g := by
    simp only [D', isDer_aδ.lift.mul, Derivation.leibniz, smul_eq_mul]; ring

/-- `D` on `T`, coefficientwise in `b`. -/
def D (g : T) : T := liftF D' g

lemma isDer_D : IsDer D := isDer_D'.lift

/-- `a ∈ k2`. -/
abbrev ca : k2 := C (X : k1)

lemma D'_ca : D' ca = ca := by
  rw [D', liftF_C isDer_aδ, aδ_X, derivative_C, mul_zero, sub_zero]

lemma D'_X : D' (X : k2) = -(1 + X) := by
  rw [D', derivative_X, mul_one]
  have : liftF aδ (X : k2) = 0 := by
    ext n; rw [coeff_liftF, coeff_X, map_zero]; split_ifs <;> simp [isDer_aδ.zero, isDer_aδ.one]
  rw [this, zero_sub]

lemma D'_one_add_X : D' (1 + X : k2) = -(1 + X) := by
  rw [isDer_D'.add, isDer_D'.one, zero_add, D'_X]

lemma D'_C (r : k1) : D' (C r) = C (aδ r) := by
  rw [D', liftF_C isDer_aδ, derivative_C, mul_zero, sub_zero]

lemma coeff_D' (g : k2) (n : ℕ) :
    coeff n (D' g) = aδ (coeff n g) - ((n + 1 : k1) * coeff (n + 1) g + (n : k1) * coeff n g) := by
  rw [D', map_sub, coeff_liftF, add_mul, one_mul, map_add, coeff_derivative]
  congr 1
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

lemma D_C (g : k2) : D (C g) = C (D' g) := liftF_C isDer_D' _

lemma coeff_D (g : T) (N : ℕ) : coeff N (D g) = D' (coeff N g) := coeff_liftF _ _ _

/-- **Uniqueness in `k2`**: `D' g = 0` and `g(X = 0) = 0` force `g = 0`. -/
lemma eq_zero_of_D' {g : k2} (hg : D' g = 0) (h0 : constantCoeff g = 0) : g = 0 := by
  have key : ∀ n, coeff n g = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have h := coeff_D' g n
      rw [hg, map_zero, ih, isDer_aδ.zero, mul_zero, add_zero, zero_sub, eq_comm,
        neg_eq_zero] at h
      have hn : (n + 1 : k1) ≠ 0 := by
        intro h1
        have h2 := congrArg (constantCoeff (R := ℚ)) h1
        simp only [map_add, map_natCast, map_one, map_zero] at h2
        norm_cast at h2
      exact (mul_eq_zero.mp h).resolve_left hn
  ext n; simp [key n]

/-- `X ↦ 0`, coefficientwise in `b`. -/
def ev0 : T →+* PowerSeries k1 := PowerSeries.map (constantCoeff (R := k1))

lemma coeff_ev0 (g : T) (N : ℕ) : coeff N (ev0 g) = constantCoeff (coeff N g) := by
  simp [ev0]

/-- **Uniqueness in `T`**: `D g = 0` and `ev0 g = 0` force `g = 0`. -/
theorem eq_zero_of_D {g : T} (hg : D g = 0) (h0 : ev0 g = 0) : g = 0 := by
  refine PowerSeries.ext fun N => ?_
  rw [map_zero]
  refine eq_zero_of_D' ?_ ?_
  · rw [← coeff_D, hg, map_zero]
  · rw [← coeff_ev0, h0, map_zero]

end TateAdd
