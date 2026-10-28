/-
# Bridge to `UpContraction.hU`: the classical-form version in the `KatzForms.pt` notation

`UpContraction.thmB` uses `hU : ∀ W, IsTest W → Brk W → kval E a (pt W) = Σ_{c : Fin p} kval E b (pt (Q W c))`,
with `Q W : Fin p → WeierstrassCurve K` the non-canonical quotients. For classical forms (a single
isobaric `P`, no `E`-denominators) the matching statement is `hU_classical` below. Its quotient family is
`Qall W : Fin (p+1) → WeierstrassCurve K`; index `0` is the canonical quotient `W/H`, and
`Q W c = Qall W c.succ`:

  `Σ_{c : Fin p} P(pt (Q W c)) = p · (T_p P)(pt W) − P(pt (W/H))`,

conditional on the (Alg) and (Tate) hypotheses of `HeckeQExp.classical_hU`.
-/
import RamanujanTau.HeckeQExp.Geom
import RamanujanTau.KatzForms.Concrete

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeQExp
open MvPolynomial ModP

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma ptR_eq_pt (W : WeierstrassCurve K) : ptR W = KatzForms.pt W := rfl

variable [CharZero K] (p : ℕ) [Fact p.Prime]

/-- **Classical `hU`** in the notation of `UpContraction` (`Good = IsTest`). -/
theorem hU_classical {ζ : K} (hζ : IsPrimitiveRoot ζ p) {k : ℕ} {P S : MvPolynomial (Fin 2) K}
    (hP : Iso P k) (hS : Iso S k) (Qall : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K)
    (hAlg : ∀ W, KatzForms.IsTest W → ∑ c, eval (KatzForms.pt (Qall W c)) P = eval (KatzForms.pt W) S)
    (hT : aeval (ptR (tateBase (K := K) p)) S = ∑ c, aeval (ptR (tateQuot p ζ c)) P) :
    ∀ W, KatzForms.IsTest W →
      ∑ c : Fin p, eval (KatzForms.pt (Qall W c.succ)) P =
        (p : K) * eval (KatzForms.pt W) (heckePoly p P) - eval (KatzForms.pt (Qall W 0)) P :=
  classical_hU_noncanonical p hζ hP hS KatzForms.IsTest Qall hAlg hT

end HeckeQExp
