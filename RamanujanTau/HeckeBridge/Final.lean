import RamanujanTau.HeckeBridge.Tate
import RamanujanTau.HeckeQExp.Bridge

/-!
# The classical q-expansion principle for `U_p`, modulo only `TateKernels` (`hKer`)

Both hypotheses of `HeckeQExp.classical_hU` are discharged:
* `hAlg` by `HeckeBridge.hAlg` (short curves, `Good W := IsQuotEnum p W (Q W)`),
* `hT` by `HeckeBridge.hT_of_kernels`, from `hKer : TateKernels p L ι ζ`
  (the Tate addition theorem, being proved separately in `RamanujanTau/TateAdd/`).

Results (`p` an odd prime, `ζ ∈ K` a primitive `p`-th root of unity, `P` isobaric of weight `k`):
* **`Siso_eq_hecke`** — the subgroup-sum polynomial is `p · T_p P`.
* **`subSum_hecke`** — over *every* algebraically closed `L ⊇ K` of characteristic `0`:
  `Σ_{|G| = p} P(ptR(E/G)) = p · (T_p P)(ptR E)` for all nonsingular short `E/L`.
* **`classical_hU_short`** — the conclusion of `classical_hU` for quotient enumerations
  (obtained by applying `HeckeQExp.classical_hU`).
* **`hU_classical_unconditional`** — the `U`-shaped form in the `KatzForms.pt` notation of
  `HeckeQExp.hU_classical`, for test curves in short form.

The restriction to short models: `classical_hU` quantifies over general Weierstrass `W`, but the
Vélu quotients `veluC G` are defined for short curves. In characteristic `0` (residue char. `p ≥ 5`)
every curve is isomorphic to a short one and `ptR` transforms by `aeval_ptR_scale`, so nothing is
lost downstream; here `Good` simply requires `W` to be short (`IsQuotEnum`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial ModP

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

/-- **The subgroup-sum polynomial is `p · T_p P`** (q-expansion principle, modulo `hKer`). -/
theorem Siso_eq_hecke {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {L : Type*} [Field L]
    [CharZero L] [IsAlgClosed L] [DecidableEq L] (ι : PowerSeries K →+* L)
    (hι : Function.Injective ι) (hKer : TateKernels p L ι ζ) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : Iso P k) : Siso p k P = C (p : K) * HeckeQExp.heckePoly p P :=
  HeckeQExp.hecke_of_tate p hζ hP (iso_Siso p k P) (hT_of_kernels p hζ hp2 ι hι hKer hP)

/-- **The classical `hU` over every algebraically closed field** (modulo `hKer`): for every
`f : K →+* L'`, `L'` algebraically closed of characteristic `0`, and every nonsingular short curve
`E = short a b` over `L'`, `Σ_{G ≤ E, |G| = p} (fP)(ptR(E/G)) = p · (f T_p P)(ptR E)`. -/
theorem subSum_hecke {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {L : Type*} [Field L]
    [CharZero L] [IsAlgClosed L] [DecidableEq L] (ι : PowerSeries K →+* L)
    (hι : Function.Injective ι) (hKer : TateKernels p L ι ζ) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : Iso P k) {L' : Type*} [Field L'] [CharZero L'] [IsAlgClosed L'] [DecidableEq L']
    (f : K →+* L') (a b : L') (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve L')) (map f P)) a b =
      (p : L') * eval (HeckeQExp.ptR (short a b : WeierstrassCurve L')) (map f (HeckeQExp.heckePoly p P)) := by
  rw [subSum_Siso p f hP a b hΔ, Siso_eq_hecke p hζ hp2 ι hι hKer hP, map_mul, map_C, eval_mul,
    eval_C, map_natCast]

/-- **Classical `hU` for short curves** (modulo `hKer`), by `HeckeQExp.classical_hU` with
`hAlg := HeckeBridge.hAlg`, `hT := HeckeBridge.hT_of_kernels`. -/
theorem classical_hU_short [DecidableEq K] [IsAlgClosed K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp2 : p ≠ 2) {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels p L ι ζ) {k : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (Q : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K) :
    ∀ W, IsQuotEnum p W (Q W) →
      ∑ c, eval (HeckeQExp.ptR (Q W c)) P = (p : K) * eval (HeckeQExp.ptR W) (HeckeQExp.heckePoly p P) :=
  HeckeQExp.classical_hU p hζ hP (iso_Siso p k P) (fun W => IsQuotEnum p W (Q W)) Q
    (hAlg p hP Q) (hT_of_kernels p hζ hp2 ι hι hKer hP)

end HeckeBridge

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial ModP

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [IsAlgClosed K]
  [DecidableEq K] (p : ℕ) [hp : Fact p.Prime]

/-- **`hU_classical` without `hAlg`/`hT`** (modulo `hKer` only), in the `KatzForms.pt` notation of
`HeckeQExp.hU_classical`: for every test curve `W` in short form and every enumeration `Qall W`
of its `p + 1` Vélu quotients (index `0` = the canonical quotient `W/H`, which may be prescribed by
`exists_quotEnum`), the sum over the `p` non-canonical quotients is `p · T_pP(W) − P(W/H)`. -/
theorem hU_classical_unconditional {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L] (ι : PowerSeries K →+* L)
    (hι : Function.Injective ι) (hKer : TateKernels p L ι ζ) {k : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (Qall : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K) :
    ∀ W, KatzForms.IsTest W → IsQuotEnum p W (Qall W) →
      ∑ c : Fin p, eval (KatzForms.pt (Qall W c.succ)) P =
        (p : K) * eval (KatzForms.pt W) (HeckeQExp.heckePoly p P) - eval (KatzForms.pt (Qall W 0)) P :=
  fun W hW hQ => HeckeQExp.classical_hU_noncanonical p hζ hP (iso_Siso p k P)
    (fun W => KatzForms.IsTest W ∧ IsQuotEnum p W (Qall W)) Qall
    (fun W hW => hAlg p hP Qall W hW.2) (hT_of_kernels p hζ hp2 ι hι hKer hP) W ⟨hW, hQ⟩

end HeckeBridge
