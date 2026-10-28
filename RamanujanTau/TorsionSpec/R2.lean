import RamanujanTau.TorsionSpec.SpecSum
import RamanujanTau.TorsionSpec.Lift

/-!
# `R2`: specialization of the universal subgroup sum, given full `p`-torsion

`FullTorsion n F`: for every nonsingular short curve over `F`, `E[n](F)` is a finite set of exactly
`n²` points. This is the standard fact `E[n] ≅ (ℤ/n)²` over an algebraically closed field of
characteristic `0` (separability of `[n]`); it is **not** proved here and enters as a hypothesis,
for `F = LU = (ℚ(A,B))^alg` and for `F = K`.

**`R2`**: with that hypothesis, the statement of `SubgroupSum.WIP.R2`.

Proof: `ψ : integralClosure ℚ[A,B] LU → K` extending `(A, B) ↦ (a, b)` (`exists_lift_of_isIntegral`);
torsion abscissae are integral (`R1`); specialization of torsion points is injective and additive
(`Spec.lean`) hence, by counting, a bijection `E[p](LU) → Ē[p](K)`, so it matches the subgroups of
order `p` and specializes the subgroup sum (`SpecSum.lean`).
-/

set_option autoImplicit false

namespace TorsionSpec

open Velu SubgroupSum

/-- `E[n](F)` has exactly `n²` points for every nonsingular short curve over `F`. -/
def FullTorsion (n : ℕ) (F : Type*) [Field F] [DecidableEq F] : Prop :=
  ∀ a b : F, 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∃ T : Finset (short a b).Point, (∀ P, P ∈ T ↔ n • P = 0) ∧ T.card = n ^ 2

lemma algebraMap_RU_LU_injective : Function.Injective (algebraMap RU LU) := by
  rw [IsScalarTower.algebraMap_eq RU (FractionRing RU) LU]
  exact (algebraMap (FractionRing RU) LU).injective.comp (IsFractionRing.injective RU _)

lemma disc_RU_ne_zero :
    4 * algebraMap RU LU (MvPolynomial.X 0) ^ 3 + 27 * algebraMap RU LU (MvPolynomial.X 1) ^ 2 ≠ 0 := by
  intro h
  have e : algebraMap RU LU (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2) = 0 := by
    rw [← h]; simp [map_ofNat]
  have e2 := congrArg (MvPolynomial.eval ![(1 : ℚ), 0])
    (algebraMap_RU_LU_injective (e.trans (map_zero _).symm))
  simp at e2

/-- **R2** (conditional on full `p`-torsion over `LU` and over `K`). -/
theorem R2 {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K] [DecidableEq LU]
    (p : ℕ) [hp : Fact p.Prime] (hLU : FullTorsion p LU) (hK : FullTorsion p K)
    (Φ : MvPolynomial (Fin 2) ℚ) (s : RU)
    (hs : algebraMap RU LU s = subSum p (fun x y => MvPolynomial.aeval
      (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)))
    (a b : K) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) Φ) a b =
      MvPolynomial.aeval ![a, b] s := by
  set φ : RU →+* K := (MvPolynomial.aeval ![a, b]).toRingHom with hφ
  set O := integralClosure RU LU
  have hinj : Function.Injective (algebraMap RU O) := by
    intro r r' h
    apply algebraMap_RU_LU_injective
    have := congrArg Subtype.val h
    exact this
  obtain ⟨ψ, hψ⟩ := exists_lift_of_isIntegral (S := O) φ hinj
  have hψr : ∀ r : RU, ψ ⟨algebraMap RU LU r, Subalgebra.algebraMap_mem O r⟩ = φ r := by
    intro r
    rw [← hψ]; rfl
  set A := algebraMap RU LU (MvPolynomial.X 0)
  set B := algebraMap RU LU (MvPolynomial.X 1)
  let D : SpecData LU K A B a b :=
    { O := O.toSubring
      ψ := ψ
      hA := Subalgebra.algebraMap_mem O _
      hB := Subalgebra.algebraMap_mem O _
      ψA := by rw [hψr, hφ]; simp
      ψB := by rw [hψr, hφ]; simp
      sq := fun z hz => by
        have : IsIntegral RU (z ^ 2) := hz
        exact this.of_pow two_pos
      tors := fun P ⟨n, hn, hnP⟩ => isIntegral_xc_of_nsmul_eq_zero (R := RU) (L := LU)
        (MvPolynomial.X 0) (MvPolynomial.X 1) hn hnP
      hΔ := hΔ }
  have hrat : ∀ q : ℚ, algebraMap ℚ LU q ∈ D.O := by
    intro q
    have : algebraMap ℚ LU q = algebraMap RU LU (algebraMap ℚ RU q) := by
      rw [eq_ratCast (algebraMap ℚ LU), ← RingHom.comp_apply, eq_ratCast]
    rw [this]; exact Subalgebra.algebraMap_mem O _
  obtain ⟨TL, hTL, hTLc⟩ := hLU A B disc_RU_ne_zero
  obtain ⟨TK, hTK, hTKc⟩ := hK a b hΔ
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨-, hev⟩ := D.ev_subSum hp0 hTL hTK (by rw [hTLc, hTKc]) hrat Φ
  rw [← hev, ← hs, D.ev_of (Subalgebra.algebraMap_mem O s)]
  exact hψr s

end TorsionSpec
