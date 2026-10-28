/-
# `hT` for the canonical subgroup `μ_p`: Vélu's quotient is `tateQuot p ζ 0`

Over `K⟦t⟧` (`q = t^p`), `tateBase p = Tate(q)`; its short model is `y² = x³ + A x + B` with
`A = −c₄/48`, `B = −c₆/864` (`ptR_shortW_base`). The Vélu curve of the kernel `μ_p`,
`shortW A' B'` (`A', B'` from `velu_mu_A/B`, transported by `q = t^p`), has the same `ptR` as
`tateQuot p ζ 0 = (Tate(q^p), ω_can/p)` (`ptR_velu_mu`), hence the same value of every `P`
(`aeval_velu_mu`).
-/
import RamanujanTau.TateQuot.MuQuot
import RamanujanTau.HeckeQExp.Geom

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset MvPolynomial

/-- The short Weierstrass curve `y² = x³ + A x + B` over a commutative ring. -/
def shortW {L : Type*} [CommRing L] (A B : L) : WeierstrassCurve L := ⟨0, 0, 0, A, B⟩

lemma ptR_shortW {L : Type*} [CommRing L] (A B : L) :
    HeckeQExp.ptR (shortW A B) = ![-48 * A, 864 * B] := by
  funext i; fin_cases i
  · simp [HeckeQExp.ptR, shortW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  · simp [HeckeQExp.ptR, shortW, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}

/-- `q ↦ t^p`. -/
abbrev eP (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime] : PowerSeries K →ₐ[K] PowerSeries K :=
  PowerSeries.expand p hp.out.ne_zero

lemma ptR_TateAt_expand (n : ℕ) (hn : n ≠ 0) :
    HeckeQExp.ptR (HeckeQExp.TateAt (PowerSeries.expand (R := K) n hn)) =
      ![PowerSeries.expand n hn (ModP.E4 K), PowerSeries.expand n hn (ModP.E6 K)] := by
  rw [HeckeQExp.ptR_TateAt]
  funext i; fin_cases i <;> simp [ModP.evVec]

/-- **The short model of `tateBase`**: `ptR (tateBase) = ptR (y² = x³ + A x + B)`. -/
theorem ptR_shortW_base :
    HeckeQExp.ptR (HeckeQExp.tateBase (K := K) p) =
      HeckeQExp.ptR (shortW (eP K p (Ash K)) (eP K p (Bsh K))) := by
  rw [ptR_shortW, HeckeQExp.tateBase, ptR_TateAt_expand]
  have h4 : ModP.E4 K = -48 * Ash K := by
    rw [Ash, E4_eq, a4K_eq]
    apply ιL_inj
    simp only [map_add, map_mul, map_sub, map_neg, map_ofNat, map_one, ιL_C, map_div₀]
    ring
  have h6 : ModP.E6 K = 864 * Bsh K := by
    have ha6 := congrArg (ιL K) (a6K_eq (K := K))
    rw [Bsh, E6_eq, a4K_eq]
    apply ιL_inj
    simp only [map_add, map_mul, map_sub, map_neg, map_ofNat, map_one, ιL_C, map_div₀] at ha6 ⊢
    linear_combination (-72 : LaurentSeries K) * ha6
  rw [h4, h6]
  funext i; fin_cases i <;> simp [map_mul, map_ofNat]

lemma c4_tateQuot_zero :
    (HeckeQExp.tateQuot p ζ 0).c₄ = (p : PowerSeries K) ^ 4 * eP K p (eP K p (ModP.E4 K)) := by
  have h := congrFun (ptR_TateAt_expand (K := K) (p * p)
    (p.mul_ne_zero hp.out.ne_zero hp.out.ne_zero)) 0
  simp only [HeckeQExp.ptR, Matrix.cons_val_zero] at h
  simp only [HeckeQExp.tateQuot, Fin.cases_zero]
  rw [WeierstrassCurve.variableChange_c₄, h, HeckeQExp.expand_mul_apply]
  simp only [HeckeQExp.scaleChange, HeckeQExp.coe_invP_inv]

lemma c6_tateQuot_zero :
    -(HeckeQExp.tateQuot p ζ 0).c₆ = (p : PowerSeries K) ^ 6 * eP K p (eP K p (ModP.E6 K)) := by
  have h := congrFun (ptR_TateAt_expand (K := K) (p * p)
    (p.mul_ne_zero hp.out.ne_zero hp.out.ne_zero)) 1
  simp only [HeckeQExp.ptR, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  simp only [HeckeQExp.tateQuot, Fin.cases_zero]
  rw [WeierstrassCurve.variableChange_c₆, ← mul_neg, h, HeckeQExp.expand_mul_apply]
  simp only [HeckeQExp.scaleChange, HeckeQExp.coe_invP_inv]

lemma ptR_tateQuot_zero :
    HeckeQExp.ptR (HeckeQExp.tateQuot p ζ 0) =
      ![(p : PowerSeries K) ^ 4 * eP K p (eP K p (ModP.E4 K)),
        (p : PowerSeries K) ^ 6 * eP K p (eP K p (ModP.E6 K))] := by
  funext i; fin_cases i
  · simp [HeckeQExp.ptR, c4_tateQuot_zero]
  · simp [HeckeQExp.ptR, c6_tateQuot_zero]

/-- **`hT` for `C = μ_p`**: the Vélu curve `y² = x³ + A'x + B'` of the kernel `μ_p` (points
`X_k = x(ζ^k) + 1/12`, `Y_k = θx(ζ^k)/2`, representatives `k = 1, …, (p−1)/2`) has the `ptR` of
`tateQuot p ζ 0 = (Tate(q^p), ω_can/p)`. -/
theorem ptR_velu_mu (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    HeckeQExp.ptR (shortW (eP K p (veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ)))
        (eP K p (veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ)))) =
      HeckeQExp.ptR (HeckeQExp.tateQuot p ζ 0) := by
  rw [ptR_shortW, ptR_tateQuot_zero]
  have hA := congrArg (eP K p) (velu_mu_A hζ hp2)
  have hB := congrArg (eP K p) (velu_mu_B hζ hp2)
  simp only [map_mul, map_neg, map_ofNat, PowerSeries.expand_C, map_pow, map_natCast] at hA hB
  funext i; fin_cases i
  · simpa using hA
  · simpa using hB

/-- The form needed by `HeckeQExp.classical_hU`: every `P` takes the same value on Vélu's quotient
by `μ_p` and on `tateQuot p ζ 0`. -/
theorem aeval_velu_mu (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (P : MvPolynomial (Fin 2) K) :
    aeval (HeckeQExp.ptR (shortW (eP K p (veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ)))
        (eP K p (veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ))))) P =
      aeval (HeckeQExp.ptR (HeckeQExp.tateQuot p ζ 0)) P := by
  rw [ptR_velu_mu hζ hp2]

end TateQuot
