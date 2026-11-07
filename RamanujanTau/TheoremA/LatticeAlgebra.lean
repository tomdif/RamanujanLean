import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Integer lattices, reduction modulo a prime, and complex scalars

Linear algebra for comparing Hecke operators on integer lattices with complex
eigenvectors. Rationality of kernels is proved by expanding complex numbers in
a basis of ℂ over ℚ, so no matrix-rank base-change theorem is used.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LatticeAlgebra
open Polynomial

/-- A vector outside `ℓE` killed by `T` modulo `ℓ` forces `ℓ ∣ det T`. -/
theorem dvd_det_of_kernel {E : Type*} [AddCommGroup E] [Module ℤ E] [Module.Free ℤ E]
    [Module.Finite ℤ E] (ℓ : ℕ) [Fact ℓ.Prime] (T : E →ₗ[ℤ] E) (x y : E)
    (hx : ¬ ∃ z : E, x = (ℓ : ℤ) • z) (hT : T x = (ℓ : ℤ) • y) :
    (ℓ : ℤ) ∣ LinearMap.det T := by
  classical
  let b := Module.finBasis ℤ E
  let B := LinearMap.toMatrix b b T
  have hdet : LinearMap.det T = B.det := (LinearMap.det_toMatrix b T).symm
  rw [hdet, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  let Bbar : Matrix _ _ (ZMod ℓ) := B.map (Int.castRingHom (ZMod ℓ))
  have hBbar : Bbar.det = ((B.det : ℤ) : ZMod ℓ) := by
    have := (Int.castRingHom (ZMod ℓ)).map_det B
    simpa [Bbar, RingHom.mapMatrix_apply] using this.symm
  rw [← hBbar, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => ((b.repr x i : ℤ) : ZMod ℓ), ?_, ?_⟩
  · intro h0
    apply hx
    have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun h0 i)
    choose w hw using hd
    refine ⟨∑ i, w i • b i, ?_⟩
    apply b.repr.injective
    ext i
    simp [hw, Finsupp.single_apply, Finset.sum_ite_eq']
  · ext j
    have hrep := congrArg (fun v : E => b.repr v j) hT
    have hmul : (B.mulVec (fun i => b.repr x i)) j = b.repr (T x) j := by
      have := LinearMap.toMatrix_mulVec_repr b b T x
      exact congrFun this j
    have h2 : ((B.mulVec (fun i => b.repr x i)) j : ZMod ℓ) = 0 := by
      rw [hmul, hT]
      simp
    have h3 := congrArg (Int.castRingHom (ZMod ℓ)) (rfl :
      (B.mulVec (fun i => b.repr x i)) j = (B.mulVec (fun i => b.repr x i)) j)
    simpa [Bbar, Matrix.mulVec, dotProduct, Matrix.map_apply] using h2

/-- Conversely, `ℓ ∣ det T` produces a vector outside `ℓE` killed by `T` modulo `ℓ`. -/
theorem exists_kernel_of_dvd_det {E : Type*} [AddCommGroup E] [Module ℤ E] [Module.Free ℤ E]
    [Module.Finite ℤ E] (ℓ : ℕ) [Fact ℓ.Prime] (T : E →ₗ[ℤ] E)
    (h : (ℓ : ℤ) ∣ LinearMap.det T) :
    ∃ x y : E, (¬ ∃ z : E, x = (ℓ : ℤ) • z) ∧ T x = (ℓ : ℤ) • y := by
  classical
  let b := Module.finBasis ℤ E
  let B := LinearMap.toMatrix b b T
  have hdet : LinearMap.det T = B.det := (LinearMap.det_toMatrix b T).symm
  let Bbar : Matrix _ _ (ZMod ℓ) := B.map (Int.castRingHom (ZMod ℓ))
  have hBbar : Bbar.det = ((B.det : ℤ) : ZMod ℓ) := by
    have := (Int.castRingHom (ZMod ℓ)).map_det B
    simpa [Bbar, RingHom.mapMatrix_apply] using this.symm
  have h0 : Bbar.det = 0 := by
    rw [hBbar, ZMod.intCast_zmod_eq_zero_iff_dvd, ← hdet]
    exact h
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  let w : _ → ℤ := fun i => ((v i).val : ℤ)
  have hwv : ∀ i, ((w i : ℤ) : ZMod ℓ) = v i := fun i => by simp [w]
  let x : E := ∑ i, w i • b i
  have hrep : ∀ i, b.repr x i = w i := by
    intro i
    simp [x, Finsupp.single_apply]
  have hdvd : ∀ j, (ℓ : ℤ) ∣ b.repr (T x) j := by
    intro j
    have hmul : (B.mulVec (fun i => b.repr x i)) j = b.repr (T x) j :=
      congrFun (LinearMap.toMatrix_mulVec_repr b b T x) j
    rw [← hmul, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun hBv j
    simpa [Bbar, Matrix.mulVec, dotProduct, Matrix.map_apply, hrep, hwv] using this
  choose y hy using hdvd
  refine ⟨x, ∑ j, y j • b j, ?_, ?_⟩
  · rintro ⟨z, hz⟩
    apply hv
    funext i
    have := congrArg (fun u : E => b.repr u i) hz
    simp only [hrep, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    rw [← hwv, this]
    simp
  · apply b.repr.injective
    ext j
    rw [hy]
    simp [Finsupp.single_apply]

/-- A complex-root comparison transfers invertibility modulo `ℓ`. -/
theorem not_dvd_coeff_zero_of_roots (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (c e : ℤ[X])
    (hc : c.Monic) (he : e.Monic)
    (hroot : ∀ α : ℂ, (c.map (Int.castRingHom ℂ)).IsRoot α →
      (e.map (Int.castRingHom ℂ)).IsRoot α)
    (hunit : ¬ (ℓ : ℤ) ∣ e.coeff 0) : ¬ (ℓ : ℤ) ∣ c.coeff 0 := by
  have hdvdC : c.map (Int.castRingHom ℂ) ∣
      (e ^ (c.map (Int.castRingHom ℂ)).roots.card).map (Int.castRingHom ℂ) := by
    have hs := IsAlgClosed.splits (c.map (Int.castRingHom ℂ))
    have hprod := hs.eq_prod_roots_of_monic (hc.map _)
    rw [hprod, Polynomial.map_pow]
    have hgen : ∀ s : Multiset ℂ,
        (∀ a ∈ s, (e.map (Int.castRingHom ℂ)).IsRoot a) →
        (s.map fun a => X - C a).prod ∣ (e.map (Int.castRingHom ℂ)) ^ Multiset.card s := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        intro h
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
        exact mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s)))
          (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))
    simpa [← hprod] using hgen _ fun a ha =>
      hroot a (isRoot_of_mem_roots ha)
  have hdvd := (map_dvd_map (Int.castRingHom ℂ) Int.cast_injective hc).mp hdvdC
  intro hd
  have h0 : c.coeff 0 ∣ (e ^ (c.map (Int.castRingHom ℂ)).roots.card).coeff 0 := by
    rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
    exact eval_dvd hdvd
  have hl : (ℓ : ℤ) ∣ (e.coeff 0) ^ (c.map (Int.castRingHom ℂ)).roots.card := by
    have := hd.trans h0
    rwa [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero] at this
  exact hunit ((Nat.prime_iff_prime_int.mp hℓ.out).dvd_of_dvd_pow hl)

/-- A basis of ℂ over ℚ. -/
noncomputable def qBasis := Module.Basis.ofVectorSpace ℚ ℂ

/-- Coordinates with respect to `qBasis`. -/
noncomputable def coord (e : Module.Basis.ofVectorSpaceIndex ℚ ℂ) : ℂ →ₗ[ℚ] ℚ :=
  qBasis.coord e

lemma coord_int_mul (e : Module.Basis.ofVectorSpaceIndex ℚ ℂ) (n : ℤ) (z : ℂ) :
    coord e ((n : ℂ) * z) = (n : ℚ) * coord e z := by
  have h : (n : ℂ) * z = (n : ℚ) • z := by simp [Rat.smul_def]
  rw [h, map_smul, smul_eq_mul]

lemma eq_of_coord_eq {z w : ℂ}
    (h : ∀ e, coord e z = coord e w) : z = w := by
  apply qBasis.ext_elem
  exact h

/-- Integer power series independent over ℤ remain independent over ℂ. -/
theorem complex_independent {r : ℕ} (a : Fin r → PowerSeries ℤ)
    (ha : LinearIndependent ℤ a) (v : Fin r → ℂ)
    (h0 : ∑ i, v i • PowerSeries.map (Int.castRingHom ℂ) (a i) = 0) : v = 0 := by
  funext i
  apply eq_of_coord_eq
  intro e
  rw [show (0 : Fin r → ℂ) i = (0 : ℂ) from rfl, map_zero]
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors ℤ) (Finset.univ.image fun i => coord e (v i))
  have hD' : ∀ i, ∃ w : ℤ, (w : ℚ) = (D : ℤ) * coord e (v i) := by
    intro i
    obtain ⟨w, hw⟩ := hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact ⟨w, by simpa [Submonoid.smul_def] using hw⟩
  choose w hw using hD'
  have hsum : ∑ j, w j • a j = 0 := by
    ext m
    have hm := congrArg (PowerSeries.coeff m) h0
    have hc := congrArg (coord e) hm
    simp only [map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul, map_zero,
      eq_intCast] at hc
    have hcq : ∑ j, ((PowerSeries.coeff m (a j) : ℤ) : ℚ) * coord e (v j) = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (v j), coord_int_mul]
    have : ((∑ j, w j * PowerSeries.coeff m (a j) : ℤ) : ℚ) = 0 := by
      push_cast
      simp_rw [hw]
      calc _ = ((D : ℤ) : ℚ) * ∑ j, ((PowerSeries.coeff m (a j) : ℤ) : ℚ) * coord e (v j) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hcq, mul_zero]
    have hz : ∑ j, w j * PowerSeries.coeff m (a j) = 0 := by exact_mod_cast this
    simp only [map_sum, map_zsmul, smul_eq_mul, map_zero]
    exact hz
  have hw0 := Fintype.linearIndependent_iff.mp ha w hsum i
  have hne : ((D : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero D.2
  have := hw i
  rw [hw0] at this
  simpa [hne] using this.symm

/-- A complex vector satisfying a family of integer linear equations is a complex combination
of integer solutions. -/
theorem exists_integer_solutions {N : ℕ} {ι : Type*} (r : ι → Fin N → ℤ) (x : Fin N → ℂ)
    (hx : ∀ m, ∑ i, (r m i : ℂ) * x i = 0) :
    ∃ (s : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ))
      (c : Module.Basis.ofVectorSpaceIndex ℚ ℂ → Fin N → ℤ)
      (w : Module.Basis.ofVectorSpaceIndex ℚ ℂ → ℂ),
      (∀ e, ∀ m, ∑ i, r m i * c e i = 0) ∧
      x = ∑ e ∈ s, w e • (fun i => ((c e i : ℤ) : ℂ)) := by
  classical
  have hden : ∀ e, ∃ (D : ℤ) (c : Fin N → ℤ), D ≠ 0 ∧
      ∀ i, (c i : ℚ) = D * coord e (x i) := by
    intro e
    obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors ℤ) (Finset.univ.image fun i => coord e (x i))
    have h : ∀ i, ∃ w : ℤ, (w : ℚ) = (D : ℤ) * coord e (x i) := by
      intro i
      obtain ⟨w, hw⟩ := hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      exact ⟨w, by simpa [Submonoid.smul_def] using hw⟩
    choose c hc using h
    exact ⟨D, c, nonZeroDivisors.ne_zero D.2, hc⟩
  choose D c hD hc using hden
  let s : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ) :=
    Finset.univ.biUnion fun i => (qBasis.repr (x i)).support
  refine ⟨s, c, fun e => (D e : ℂ)⁻¹ * (qBasis e : ℂ), ?_, ?_⟩
  · intro e m
    have h := congrArg (coord e) (hx m)
    simp only [map_sum, map_zero, coord_int_mul] at h
    have hq : ((∑ i, r m i * c e i : ℤ) : ℚ) = 0 := by
      push_cast
      simp_rw [hc]
      calc _ = (D e : ℚ) * ∑ i, (r m i : ℚ) * coord e (x i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h, mul_zero]
    exact_mod_cast hq
  · funext i
    have hsum : x i = ∑ e ∈ s, (coord e (x i) : ℚ) • (qBasis e : ℂ) := by
      conv_lhs => rw [← qBasis.linearCombination_repr (x i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _
        (Finset.subset_biUnion_of_mem (fun i => (qBasis.repr (x i)).support)
          (Finset.mem_univ i)) _ (by simp)]
      rfl
    rw [Finset.sum_apply, hsum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hDc : (D e : ℂ) ≠ 0 := by exact_mod_cast hD e
    have hci : ((c e i : ℤ) : ℂ) = (D e : ℂ) * ((coord e (x i) : ℚ) : ℂ) := by
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) (hc e i)
    simp only [Pi.smul_apply, smul_eq_mul, Rat.smul_def]
    rw [hci]
    field_simp

end RamanujanTau.TheoremA.LatticeAlgebra
