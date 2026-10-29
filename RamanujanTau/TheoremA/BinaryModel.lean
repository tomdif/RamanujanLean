import RamanujanTau.TheoremA.BinarySeries
import RamanujanTau.TheoremA.EvenWeightSerre
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# A binary polynomial model for level-six forms in even weights

Evaluation at two explicit integer series identifies homogeneous binary
polynomials of degree 2n with the proved integral model of weight 2n.
Evaluation is injective in each even degree over every commutative ring.
This supplies the polynomial setting for the remaining Hasse-divisibility
and filtration arguments; those arguments are not assumed here.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial
open EtaSquared
open ModularForm CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

abbrev BinaryHomogeneous {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 2) R) (k : ℕ) : Prop :=
  P.IsWeightedHomogeneous (fun _ : Fin 2 => (1 : ℕ)) k

noncomputable def binaryEv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] PowerSeries R :=
  aeval ![PowerSeries.map (Int.castRingHom R) binaryX,
    PowerSeries.map (Int.castRingHom R) binaryY]

noncomputable def binaryExponent (n : ℕ) (i : Fin (2 * n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (2 * n - i.val) + Finsupp.single 1 i.val

@[simp] theorem binaryExponent_zero (n : ℕ) (i : Fin (2 * n + 1)) :
    binaryExponent n i 0 = 2 * n - i.val := by simp [binaryExponent]

@[simp] theorem binaryExponent_one (n : ℕ) (i : Fin (2 * n + 1)) :
    binaryExponent n i 1 = i.val := by simp [binaryExponent]

lemma binary_weight (s : Fin 2 →₀ ℕ) :
    Finsupp.weight (fun _ : Fin 2 => (1 : ℕ)) s = s 0 + s 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp

lemma binaryExponent_weight (n : ℕ) (i : Fin (2 * n + 1)) :
    Finsupp.weight (fun _ : Fin 2 => (1 : ℕ)) (binaryExponent n i) = 2 * n := by
  rw [binary_weight, binaryExponent_zero, binaryExponent_one]
  omega

noncomputable def binaryPolynomial {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : MvPolynomial (Fin 2) R :=
  ∑ i : Fin (2 * n + 1), monomial (binaryExponent n i) (c i)

theorem binaryPolynomial_homogeneous {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : BinaryHomogeneous (binaryPolynomial n c) (2 * n) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  exact isWeightedHomogeneous_monomial _ _ _ (binaryExponent_weight n i)

lemma binaryExponent_injective (n : ℕ) : Function.Injective (binaryExponent n) := by
  intro i j h
  apply Fin.ext
  simpa only [binaryExponent_one] using congrArg (fun s : Fin 2 →₀ ℕ => s 1) h

theorem binaryPolynomial_coeff {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) (i : Fin (2 * n + 1)) :
    (binaryPolynomial n c).coeff (binaryExponent n i) = c i := by
  classical
  simp only [binaryPolynomial, coeff_sum, coeff_monomial, (binaryExponent_injective n).eq_iff]
  simp

/-- Every even-degree homogeneous polynomial has exactly these coefficients. -/
theorem homogeneous_eq_binaryPolynomial {R : Type*} [CommRing R]
    (n : ℕ) (P : MvPolynomial (Fin 2) R) (hP : BinaryHomogeneous P (2 * n)) :
    P = binaryPolynomial n (fun i => P.coeff (binaryExponent n i)) := by
  classical
  ext s
  by_cases hs : s 0 + s 1 = 2 * n
  · let i : Fin (2 * n + 1) := ⟨s 1, by omega⟩
    have he : binaryExponent n i = s := by
      ext j
      fin_cases j
      · change binaryExponent n i 0 = s 0
        rw [binaryExponent_zero]
        dsimp [i]
        omega
      · change binaryExponent n i 1 = s 1
        rw [binaryExponent_one]
    rw [← he, binaryPolynomial_coeff]
  · have hp : P.coeff s = 0 := by
      by_contra h
      exact hs (by simpa only [binary_weight] using hP h)
    rw [hp, binaryPolynomial, coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_monomial, if_neg]
    intro he
    apply hs
    rw [← he, binaryExponent_zero, binaryExponent_one]
    omega

theorem binaryEv_monomial {R : Type*} [CommRing R]
    (n : ℕ) (i : Fin (2 * n + 1)) (c : R) :
    binaryEv R (monomial (binaryExponent n i) c) =
      c • PowerSeries.map (Int.castRingHom R) (evenSeries n i.val) := by
  have he := congrArg (PowerSeries.map (Int.castRingHom R))
    (binary_monomial_even n i.val (by omega))
  rw [map_mul, map_pow, map_pow] at he
  rw [binaryEv, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    binaryExponent_zero, binaryExponent_one]
  rw [he]
  exact (Algebra.smul_def c _).symm

theorem binaryEv_binaryPolynomial {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) :
    binaryEv R (binaryPolynomial n c) = evenCombination n c := by
  simp only [binaryPolynomial, map_sum, binaryEv_monomial, evenCombination]

/-- The single-weight q-expansion principle, valid in every residue characteristic. -/
theorem binaryEv_injective_on_homogeneous {R : Type*} [CommRing R]
    (n : ℕ) {P Q : MvPolynomial (Fin 2) R}
    (hP : BinaryHomogeneous P (2 * n)) (hQ : BinaryHomogeneous Q (2 * n))
    (he : binaryEv R P = binaryEv R Q) : P = Q := by
  have hp := homogeneous_eq_binaryPolynomial n P hP
  have hq := homogeneous_eq_binaryPolynomial n Q hQ
  rw [hp, hq, binaryEv_binaryPolynomial, binaryEv_binaryPolynomial] at he
  have hc := evenCombination_injective n he
  exact hp.trans ((congrArg (binaryPolynomial n) hc).trans hq.symm)

/-- A nonzero homogeneous polynomial cannot have identically zero q-expansion. -/
theorem binaryEv_eq_zero_iff {R : Type*} [CommRing R]
    (n : ℕ) (P : MvPolynomial (Fin 2) R) (hP : BinaryHomogeneous P (2 * n)) :
    binaryEv R P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply binaryEv_injective_on_homogeneous n hP
      (isWeightedHomogeneous_zero R _ _)
    rw [map_zero]
    exact h
  · intro h
    rw [h, map_zero]

/-- Every actual even-weight form has a homogeneous binary polynomial expansion. -/
theorem exists_binaryPolynomial_qExpansion (n : ℕ)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ)) :
    ∃ P : MvPolynomial (Fin 2) ℂ, BinaryHomogeneous P (2 * n) ∧
      binaryEv ℂ P = qExpansion 1 f := by
  refine ⟨binaryPolynomial n (evenCoordinates n (LevelSix.firstCoefficients (2 * n) f)),
    binaryPolynomial_homogeneous _ _, ?_⟩
  rw [binaryEv_binaryPolynomial]
  exact (even_reconstruct_qExpansion n f).symm

/-- Conversely, every even-degree homogeneous polynomial represents an actual modular form. -/
theorem exists_modularForm_binaryEv (n : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : BinaryHomogeneous P (2 * n)) :
    ∃ f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ),
      qExpansion 1 f = binaryEv ℂ P := by
  refine ⟨evenFormCombination n (fun i => P.coeff (binaryExponent n i)), ?_⟩
  have he := congrArg (binaryEv ℂ) (homogeneous_eq_binaryPolynomial n P hP)
  rw [binaryEv_binaryPolynomial] at he
  exact (qExpansion_evenFormCombination _ _).trans he.symm

/-- The homogeneous polynomial description descends to any embedded coefficient ring. -/
theorem exists_binaryPolynomial_descent {R : Type*} [CommRing R] (φ : R →+* ℂ)
    (hφ : Function.Injective φ) (n : ℕ) (a : PowerSeries R)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ))
    (ha : PowerSeries.map φ a = qExpansion 1 f) :
    ∃ P : MvPolynomial (Fin 2) R, BinaryHomogeneous P (2 * n) ∧ binaryEv R P = a := by
  refine ⟨binaryPolynomial n (evenCoordinates n (fun i => a.coeff i.val)),
    binaryPolynomial_homogeneous _ _, ?_⟩
  rw [binaryEv_binaryPolynomial]
  exact (even_expansion_descent φ hφ n a f ha).symm

noncomputable def binarySerre {R : Type*} [CommRing R]
    (n : ℕ) (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  binaryPolynomial (n + 1) (evenSerreCoordinates n (fun i => P.coeff (binaryExponent n i)))

theorem binarySerre_homogeneous {R : Type*} [CommRing R]
    (n : ℕ) (P : MvPolynomial (Fin 2) R) : BinaryHomogeneous (binarySerre n P) (2 * (n + 1)) :=
  binaryPolynomial_homogeneous _ _

/-- The polynomial operator is the actual scaled Serre derivative on q-expansions. -/
theorem binaryEv_binarySerre {R : Type*} [CommRing R]
    (n : ℕ) (P : MvPolynomial (Fin 2) R) (hP : BinaryHomogeneous P (2 * n)) :
    binaryEv R (binarySerre n P) = serreSeries (2 * n : ℕ) (binaryEv R P) := by
  have he := congrArg (binaryEv R) (homogeneous_eq_binaryPolynomial n P hP)
  rw [binaryEv_binaryPolynomial] at he
  rw [binarySerre, binaryEv_binaryPolynomial, ← serreSeries_evenCombination, ← he]

end RamanujanTau.TheoremA
