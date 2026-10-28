/-
# `hT`: the Vélu quotients of the Tate curve are `tateQuot`

For every `c : Fin (p+1)` the Vélu curve `veluQuot p ζ c` (short Weierstrass form `y² = x³ + A'x + B'`
computed by Vélu's formulas from the kernel points) has the same `ptR = (c₄, −c₆)` as
`HeckeQExp.tateQuot p ζ c` (`ptR_veluQuot`), so every isobaric `P` takes the same value on both
(`aeval_veluQuot`, `sum_aeval_veluQuot`). The hypothesis `hT` of `HeckeQExp.classical_hU` is then
equivalent to the statement about Vélu's quotients (`hT_iff_velu`).

* `c = 0`, kernel `μ_p`: points `X_k = x(ζ^k) + 1/12`, `Y_k = θx(ζ^k)/2` (`MuQuot`).
* `c = j+1`, kernel `⟨ζ^j t⟩`: points `X_k = x((ζ^j t)^k) + 1/12`, obtained from the `⟨s⟩`-points
  `XB` of `Tate(s^p)` by `s ↦ ζ^j t` (`rescale (ζ^j)`), which fixes `Tate(t^p)`.
-/
import RamanujanTau.TateQuot.MuBridge
import RamanujanTau.TateQuot.SubQuot

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}

/-- `s ↦ ζ^j t` fixes series in `t^p`. -/
lemma rescale_expand (hζ : IsPrimitiveRoot ζ p) (j : ℕ) (F : PowerSeries K) :
    rescale (ζ ^ j) (PowerSeries.expand p hp.out.ne_zero F) = PowerSeries.expand p hp.out.ne_zero F := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    rw [← pow_mul, mul_comm j, mul_assoc, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  · rw [mul_zero]

lemma AshS_eq : AshS K p = eP K p (Ash K) := by
  rw [AshS, Ash, a4s, map_sub, PowerSeries.expand_C]

lemma BshS_eq : BshS K p = eP K p (Bsh K) := by
  rw [BshS, Bsh, a4s, a6s, map_add, map_sub, map_mul, PowerSeries.expand_C, PowerSeries.expand_C]

/-- The Vélu data of `⟨ζ^j t⟩`: `x`-coordinates `x((ζ^j t)^k) + 1/12`. -/
def Xsub (ζ : K) (p j k : ℕ) : PowerSeries K := rescale (ζ ^ j) (XB K p k)
/-- `y`-coordinates `θx((ζ^j t)^k)/2`. -/
def Ysub (ζ : K) (p j k : ℕ) : PowerSeries K := rescale (ζ ^ j) (YB K p k)

/-- The points of `⟨ζ^j t⟩` lie on the short model of `tateBase`. -/
theorem sub_on_curve_j (hζ : IsPrimitiveRoot ζ p) (j : ℕ) {k : ℕ} (hk : k ∈ Ico 1 p) :
    Ysub ζ p j k ^ 2 = Xsub ζ p j k ^ 3 + eP K p (Ash K) * Xsub ζ p j k + eP K p (Bsh K) := by
  have h := congrArg (rescale (ζ ^ j)) (sub_on_curve (K := K) (p := p) hk)
  simp only [map_add, map_mul, map_pow, AshS_eq, BshS_eq, rescale_expand hζ] at h
  exact h

lemma veluA_map {L L' : Type*} [CommRing L] [CommRing L'] (f : L →+* L') (A : L) (S : Finset ℕ)
    (x : ℕ → L) : f (veluA A S x) = veluA (f A) S (fun k => f (x k)) := by
  simp only [veluA, map_sub, map_mul, map_sum, map_add, map_pow, map_ofNat]

lemma veluB_map {L L' : Type*} [CommRing L] [CommRing L'] (f : L →+* L') (A B : L) (S : Finset ℕ)
    (x y : ℕ → L) : f (veluB A B S x y) = veluB (f A) (f B) S (fun k => f (x k)) (fun k => f (y k)) := by
  simp only [veluB, map_sub, map_mul, map_sum, map_add, map_pow, map_ofNat]

/-- **`hT` for `C = ⟨ζ^j t⟩`**: Vélu's quotient is `tateQuot p ζ (j+1) = Tate(ζ^j t)`. -/
theorem ptR_velu_sub (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (j : Fin p) :
    HeckeQExp.ptR (shortW (veluA (eP K p (Ash K)) (Icc 1 (p / 2)) (Xsub ζ p j))
        (veluB (eP K p (Ash K)) (eP K p (Bsh K)) (Icc 1 (p / 2)) (Xsub ζ p j) (Ysub ζ p j))) =
      HeckeQExp.ptR (HeckeQExp.tateQuot p ζ j.succ) := by
  have hA := congrArg (rescale (ζ ^ (j : ℕ))) (velu_sub_A (K := K) (p := p) hp2)
  have hB := congrArg (rescale (ζ ^ (j : ℕ))) (velu_sub_B (K := K) (p := p) hp2)
  rw [map_mul, veluA_map, map_neg, map_ofNat] at hA
  rw [map_mul, veluB_map, map_ofNat] at hB
  simp only [AshS_eq, BshS_eq, rescale_expand hζ] at hA hB
  rw [ptR_shortW]
  simp only [HeckeQExp.tateQuot, Fin.cases_succ, HeckeQExp.ptR_TateAt, HeckeQExp.rescaleAlgHom_apply]
  funext i; fin_cases i
  · simpa [ModP.evVec, Xsub] using hA
  · simpa [ModP.evVec, Xsub, Ysub] using hB

/-- **The Vélu quotients of `tateBase`**, one for each order-`p` subgroup. -/
def veluQuot (ζ : K) (p : ℕ) [Fact p.Prime] : Fin (p + 1) → WeierstrassCurve (PowerSeries K) :=
  Fin.cases (shortW (eP K p (veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ)))
      (eP K p (veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ))))
    fun j => shortW (veluA (eP K p (Ash K)) (Icc 1 (p / 2)) (Xsub ζ p j))
      (veluB (eP K p (Ash K)) (eP K p (Bsh K)) (Icc 1 (p / 2)) (Xsub ζ p j) (Ysub ζ p j))

/-- **`hT`, curve by curve**: `ptR (W/C) = ptR (tateQuot C)` for all `p + 1` subgroups. -/
theorem ptR_veluQuot (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (c : Fin (p + 1)) :
    HeckeQExp.ptR (veluQuot ζ p c) = HeckeQExp.ptR (HeckeQExp.tateQuot p ζ c) := by
  refine Fin.cases ?_ (fun j => ?_) c
  · exact ptR_velu_mu hζ hp2
  · exact ptR_velu_sub hζ hp2 j

theorem aeval_veluQuot (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (c : Fin (p + 1))
    (P : MvPolynomial (Fin 2) K) :
    aeval (HeckeQExp.ptR (veluQuot ζ p c)) P = aeval (HeckeQExp.ptR (HeckeQExp.tateQuot p ζ c)) P := by
  rw [ptR_veluQuot hζ hp2]

theorem sum_aeval_veluQuot (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (P : MvPolynomial (Fin 2) K) :
    ∑ c, aeval (HeckeQExp.ptR (veluQuot ζ p c)) P =
      ∑ c, aeval (HeckeQExp.ptR (HeckeQExp.tateQuot p ζ c)) P :=
  Finset.sum_congr rfl fun c _ => aeval_veluQuot hζ hp2 c P

/-- The base curve: `tateBase` and its short model `y² = x³ + A x + B` have the same `ptR`. -/
theorem aeval_tateBase_short (P : MvPolynomial (Fin 2) K) :
    aeval (HeckeQExp.ptR (HeckeQExp.tateBase (K := K) p)) P =
      aeval (HeckeQExp.ptR (shortW (eP K p (Ash K)) (eP K p (Bsh K)))) P := by
  rw [ptR_shortW_base]

/-- **`hT` of `HeckeQExp.classical_hU`, restated through Vélu's quotients**: it is equivalent to
`S(short Tate) = Σ_C P(Vélu quotient by C)`. -/
theorem hT_iff_velu (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (P S : MvPolynomial (Fin 2) K) :
    (aeval (HeckeQExp.ptR (HeckeQExp.tateBase (K := K) p)) S =
        ∑ c, aeval (HeckeQExp.ptR (HeckeQExp.tateQuot p ζ c)) P) ↔
      (aeval (HeckeQExp.ptR (shortW (eP K p (Ash K)) (eP K p (Bsh K)))) S =
        ∑ c, aeval (HeckeQExp.ptR (veluQuot ζ p c)) P) := by
  rw [aeval_tateBase_short, sum_aeval_veluQuot hζ hp2]

end TateQuot
