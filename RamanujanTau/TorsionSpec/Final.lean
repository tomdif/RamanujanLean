import RamanujanTau.TorsionSpec.Count

/-!
# Full `n`-torsion and the unconditional `R2`

* **`fullTorsion`**: for `F` algebraically closed of characteristic `0` and `n ≥ 2`, every
  nonsingular short curve over `F` has exactly `n²` points of order dividing `n`.
* **`R2'`**: the statement of `SubgroupSum.WIP.R2`, with no extra hypotheses.
-/

set_option autoImplicit false

namespace TorsionSpec

open Velu SubgroupSum Polynomial

variable {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] [DecidableEq F]

/-- `t ∈ (F(t))^alg` is transcendental over `F`. -/
lemma transc_X : Transc F (algebraMap (RatFunc F) (AlgebraicClosure (RatFunc F)) RatFunc.X) := by
  intro A hA h
  rw [← aeval_def, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply,
    show algebraMap F[X] (AlgebraicClosure (RatFunc F)) =
      (algebraMap (RatFunc F) (AlgebraicClosure (RatFunc F))).comp (algebraMap F[X] (RatFunc F))
      from IsScalarTower.algebraMap_eq _ _ _] at h
  rw [RingHom.comp_apply, aeval_algebraMap_apply, aeval_algebraMap_apply, aeval_X_left_apply] at h
  rw [map_eq_zero_iff _ (algebraMap (RatFunc F) _).injective,
    map_eq_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))] at h
  exact hA h

/-- **`E[n] ≅ (ℤ/n)²` (cardinality)** over an algebraically closed field of characteristic `0`. -/
theorem fullTorsion {n : ℕ} (hn : 2 ≤ n) : FullTorsion n F := by
  classical
  intro a b hΔ
  set L := AlgebraicClosure (RatFunc F)
  obtain ⟨hfin, hcard⟩ := tors_ncard (F := F) (L := L) hΔ transc_X hn
  set SL := {P : (VL (L := L) a b).Point | n • P = 0}
  set SF := {P : (short a b).Point | n • P = 0}
  have himg : liftPt (L := L) a b '' SF = SL := by
    ext P
    constructor
    · rintro ⟨P₀, hP₀, rfl⟩
      show n • liftPt a b P₀ = 0
      have := (liftHom (L := L) a b).map_nsmul n P₀
      simp only [liftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [← this, show n • P₀ = 0 from hP₀]; rfl
    · intro hP
      have hP' : n • P = 0 := hP
      obtain ⟨hx, hy⟩ := tors_mem_range a b (show 1 ≤ n by omega) hP'
      obtain ⟨P₀, rfl⟩ := mem_range_lift a b hx hy
      refine ⟨P₀, ?_, rfl⟩
      show n • P₀ = 0
      apply liftPt_injective (L := L) a b
      have := (liftHom (L := L) a b).map_nsmul n P₀
      simp only [liftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this, hP']; rfl
  have hinj : Set.InjOn (liftPt (L := L) a b) SF := (liftPt_injective a b).injOn
  have hfinF : SF.Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj
  refine ⟨hfinF.toFinset, fun P => by simp [SF], ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfinF, ← Set.InjOn.ncard_image hinj, himg, hcard]

/-- **R2** (unconditional): the universal subgroup sum specializes to every nonsingular short curve
over an algebraically closed field of characteristic `0`. Exactly `SubgroupSum.WIP.R2`. -/
theorem R2' {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K] [DecidableEq LU]
    (p : ℕ) [hp : Fact p.Prime] (Φ : MvPolynomial (Fin 2) ℚ) (s : RU)
    (hs : algebraMap RU LU s = subSum p (fun x y => MvPolynomial.aeval
      (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)))
    (a b : K) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) Φ) a b =
      MvPolynomial.aeval ![a, b] s :=
  have : CharZero LU := charZero_of_injective_algebraMap (algebraMap ℚ LU).injective
  R2 p (fullTorsion hp.out.two_le) (fullTorsion hp.out.two_le) Φ s hs a b hΔ

end TorsionSpec
