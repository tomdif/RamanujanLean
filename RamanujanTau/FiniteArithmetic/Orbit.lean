import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite certificates for arithmetic operator orbits

A proved finite-state realization transfers a checked orbit relation to every
iterate in the actual arithmetic space. Linear observations (for example,
q-series coefficients) inherit the recurrence.

Over a field, survival through the dimension is equivalent to survival forever.
Recurrence propagation also works over rings such as ZMod (p^m).

These are algebraic interfaces. An application must separately prove the
synthesis/intertwining identity, and any truncation or valuation bounds used to
construct it. In particular this file does not identify the experimental Theta
matrices with partition operators or prove the proposed sharpness theorems.
-/

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic

section Ring
variable {R V M : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]

/-- A finite-state realization of the orbit starting at `f` under `T`.
The synthesis map lands in the actual arithmetic space. Its intertwining
identity must be proved; matching a finite prefix alone does not provide it. -/
structure OrbitModel (T : Module.End R M) (f : M) where
  dimension : ℕ
  transition : Module.End R (Fin dimension → R)
  initial : Fin dimension → R
  synthesize : (Fin dimension → R) →ₗ[R] M
  seed : synthesize initial = f
  intertwines : T.comp synthesize = synthesize.comp transition

/-- An actual eigenvector supplies a one-coordinate realization. Its identity
must hold in the target space, rather than only in a truncated approximation. -/
def eigenlineModel (T : Module.End R M) (v : M) (c a : R)
    (hv : T v = a • v) : OrbitModel T (c • v) where
  dimension := 1
  transition := a • LinearMap.id
  initial := fun _ => c
  synthesize := (LinearMap.id : R →ₗ[R] R).smulRight v |>.comp (LinearMap.proj 0)
  seed := rfl
  intertwines := by
    ext x
    simp [hv, smul_smul, mul_comm]

/-- One intertwining identity identifies every iterate. -/
theorem intertwine_pow (T : Module.End R M) (A : Module.End R V)
    (E : V →ₗ[R] M) (h : T.comp E = E.comp A) (v : V) (n : ℕ) :
    (T ^ n) (E v) = E ((A ^ n) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact LinearMap.congr_fun h ((A ^ n) v)

/-- One finite relation among orbit vectors propagates to every later step.
This works over rings, including `ZMod (p^m)`, without a field assumption. -/
theorem relation_for_all_iterates (A : Module.End R V) (v : V)
    (r : ℕ) (c : Fin r → R)
    (h : (A ^ r) v = ∑ i : Fin r, c i • (A ^ (i : ℕ)) v) (n : ℕ) :
    (A ^ (n + r)) v = ∑ i : Fin r, c i • (A ^ (n + (i : ℕ))) v := by
  have hn := congrArg (A ^ n) h
  simpa only [map_sum, map_smul, pow_add, Module.End.mul_apply] using hn

/-- Given a certified recurrence, vanishing of its first `r` observations is
an exact finite test for vanishing at every iterate. The zero-order case is
included: its orbit relation already forces the initial vector to be zero. -/
theorem observed_zero_iff (A : Module.End R V) (v : V) (observe : V →ₗ[R] R)
    (r : ℕ) (c : Fin r → R)
    (h : (A ^ r) v = ∑ i : Fin r, c i • (A ^ (i : ℕ)) v) :
    (∀ n : ℕ, observe ((A ^ n) v) = 0) ↔
      (∀ i : Fin r, observe ((A ^ (i : ℕ)) v) = 0) := by
  constructor
  · exact fun hzero i => hzero i
  · intro hzero n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnr : n < r
      · exact hzero ⟨n, hnr⟩
      · have hle : r ≤ n := Nat.le_of_not_gt hnr
        have hr := relation_for_all_iterates A v r c h (n - r)
        rw [Nat.sub_add_cancel hle] at hr
        rw [hr, map_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [map_smul, ih (n - r + (i : ℕ)) (by have := i.isLt; omega), smul_zero]

namespace OrbitModel
variable {T : Module.End R M} {f : M}

theorem realizes (C : OrbitModel T f) (n : ℕ) :
    (T ^ n) f = C.synthesize ((C.transition ^ n) C.initial) := by
  exact (congrArg (T ^ n) C.seed).symm.trans
    (intertwine_pow T C.transition C.synthesize C.intertwines C.initial n)

/-- A checked relation on finite coordinates gives a recurrence in the
arithmetic space, hence simultaneously for every coefficient of a series. -/
theorem recurrence (C : OrbitModel T f) (r : ℕ) (c : Fin r → R)
    (h : (C.transition ^ r) C.initial =
      ∑ i : Fin r, c i • (C.transition ^ (i : ℕ)) C.initial) (n : ℕ) :
    (T ^ (n + r)) f = ∑ i : Fin r, c i • (T ^ (n + (i : ℕ))) f := by
  simp only [C.realizes]
  rw [relation_for_all_iterates C.transition C.initial r c h n, map_sum]
  simp only [map_smul]

/-- Any linear observation inherits the certified recurrence. -/
theorem observed_recurrence (C : OrbitModel T f) (observe : M →ₗ[R] R)
    (r : ℕ) (c : Fin r → R)
    (h : (C.transition ^ r) C.initial =
      ∑ i : Fin r, c i • (C.transition ^ (i : ℕ)) C.initial) (n : ℕ) :
    observe ((T ^ (n + r)) f) =
      ∑ i : Fin r, c i * observe ((T ^ (n + (i : ℕ))) f) := by
  rw [C.recurrence r c h n, map_sum]
  simp only [map_smul, smul_eq_mul]

end OrbitModel
end Ring

section Field
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Survival through the dimension is an exact certificate of survival forever.
The operator need not be invertible on the whole ambient space. -/
theorem orbit_nonzero_iff (A : Module.End K V) (v : V) :
    (∀ n : ℕ, (A ^ n) v ≠ 0) ↔ (A ^ Module.finrank K V) v ≠ 0 := by
  constructor
  · exact fun h => h _
  · intro h n hn
    exact h (Module.End.ker_pow_le_ker_pow_finrank A n hn)

/-- Equivalently, eventual death has a witness no later than the dimension. -/
theorem orbit_eventually_zero_iff (A : Module.End K V) (v : V) :
    (∃ n : ℕ, (A ^ n) v = 0) ↔ (A ^ Module.finrank K V) v = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    exact Module.End.ker_pow_le_ker_pow_finrank A n hn
  · exact fun h => ⟨_, h⟩

end Field

section ModelSurvival
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  {T : Module.End K M} {f : M}

/-- A finite survival certificate transfers to the arithmetic orbit when the
synthesis map is injective. No finite-dimensionality of `M` is needed. -/
theorem OrbitModel.nonzero_forever (C : OrbitModel T f)
    (hinj : Function.Injective C.synthesize)
    (h : (C.transition ^ C.dimension) C.initial ≠ 0) :
    ∀ n : ℕ, (T ^ n) f ≠ 0 := by
  have hc : ∀ n : ℕ, (C.transition ^ n) C.initial ≠ 0 :=
    (orbit_nonzero_iff C.transition C.initial).mpr (by
      simpa only [Module.finrank_pi, Fintype.card_fin] using h)
  intro n hn
  apply hc n
  apply hinj
  rw [map_zero]
  exact (C.realizes n).symm.trans hn

end ModelSurvival

end RamanujanTau.FiniteArithmetic
