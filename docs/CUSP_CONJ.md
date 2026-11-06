# The conjugate cusp form `f^ρ` and subconvexity for every level-one cusp form

**Status (2026-11-06): evidence level 1 (Lean, axiom-clean, no hypotheses).**

    nice -n 10 lake build RamanujanTau.CuspConj.Main      # exit 0

* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom`.
* Directory `RamanujanTau/CuspConj/`: 3 files, about 320 lines. No existing file was modified.

Neither Mathlib nor the repo had this construction. A grep of `Mathlib/NumberTheory/ModularForms` finds no conjugate form. There is also no complex scalar multiplication beyond `CuspForm.IsGLPos.instSMul`.

## Headlines (`RamanujanTau.CuspConj`)

```lean
noncomputable def cuspConj (f : CuspForm 𝒮ℒ (k : ℤ)) : CuspForm 𝒮ℒ (k : ℤ)  -- z ↦ conj (f (−z̄))
theorem coef_cuspConj (f) (n) : coef (cuspConj f) n = conj (coef f n)
theorem eq_reF_add_imF (f) : f = reF f + I • imF f
    -- reF f = (1/2)•(f + f^ρ),  imF f = (−I/2)•(f − f^ρ)
theorem reF_real (f) (n) : (coef (reF f) n).im = 0     -- coef = Re a_f(n)
theorem imF_real (f) (n) : (coef (imF f) n).im = 0     -- coef = Im a_f(n)
theorem fL_add (f g) (hk : 1 ≤ k) (s) : fL (f + g) s = fL f s + fL g s
theorem fL_smul (f) (c : ℂ) (s) : fL (c • f) s = c * fL f s
theorem fL_subconvex_all (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ C, 0 ≤ C ∧ ∀ t : ℝ,
    ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ)
```

`fL_subconvex_all` removes the reality hypothesis from `SubconvexGeneral3.fL_subconvex_general134`. The constant is `C_{Re f} + C_{Im f}`.

## Proof sketch

The four properties of `f^ρ` are proved as follows.

* **Invariance** (`refl_smul`, `conjFun_slash`):
  * `−conj(γz) = γ'(−z̄)` with `γ' = [[a,−b],[−c,d]] ∈ SL₂(ℤ)` (`gConj`). This is conjugation by `diag(−1,1)`.
  * `f(γ'w) = (−cw+d)^k f(w)` and `−c(−z̄)+d = conj(cz+d)`. So `f^ρ(γz) = (cz+d)^k f^ρ(z)`, which gives `f^ρ ∣[k] γ = f^ρ` through `SL_slash_apply`.
* **Holomorphy** (`mdiff_conjFun`): on `Im z > 0` the function is `conj ∘ (u ↦ F(−u)) ∘ conj` with `F = f ∘ ofComplex`, which is differentiable by `DifferentiableAt.conj_conj`.
* **Cusps:** `‖f^ρ(z)‖ = ‖f(−z̄)‖` and `Im(−z̄) = Im z`, so `IsZeroAtImInfty` transfers from `f`. Every cusp of `SL₂(ℤ)` is then handled through `OnePoint.isZeroAt_iff_forall_SL2Z` and invariance, following the pattern of `TauBound.poincareCuspForm`.
* **Coefficients:**
  * `conj(q(−z̄)) = q(z)`, so conjugating `f(−z̄) = Σ a_n q(−z̄)^n` gives `f^ρ(z) = Σ conj(a_n) q(z)^n`.
  * `ModularFormClass.qExpansion_coeff_unique` then identifies the coefficients.
  * `coef_add` and `coef_smul` are proved the same way.

**Linearity of `L(f,s)`.**
* `heckeLambda = mellin ∘ heckeF` and `heckeF` is linear.
* Mellin is additive via `integral_add`, with integrability from `(heckePair f hk).hasMellin s`.
* Scalars pull out via `mellin_const_smul`.

## Other repo results stated with `hreal : ∀ n, (coef f n).im = 0`

These are not formalized here. Each one now extends to every `f` by applying it to `reF f` and `imF f`, but only when its conclusion is **linear** in `f`, or is a bound closed under sums. Asymptotics, sign results and zero counts do **not** transfer this way.

| directory | what `hreal` is used for | extends to all `f` via `f^ρ`? |
|---|---|---|
| `SubconvexGeneral`, `SubconvexGeneral2`, `SubconvexGeneral3` | `fL_conj`, real mean-value expansion | **yes, done** (`fL_subconvex_all`) |
| `VoronoiTruncGeneral`, `VoronoiTruncComplete` | truncated Voronoi formula / error bounds for `Σ a(n)` | yes for error **bounds**, since the main terms are linear in `a`. Needs `coef_add`/`coef_smul` (done) and the triangle inequality |
| `HardyZerosGeneral`, `HafnerGeneral` | Hardy `Z_f(t)` real-valued, so zeros on the critical line | **no**: needs `Λ(f, s̄) = conj Λ(f, s)`, which fails for non-real `f`. The zeros of `L(Re f) + i L(Im f)` are not controlled by those of the parts |
| `EigenformEdge` | normalized eigenforms (real by Hecke theory) | not applicable (statement is about eigenforms) |
| `LandauSigns`, `TauOmegaPM` | sign changes / Ω± of real coefficients | **no** (sign statements need real values). The real and imaginary parts separately are covered |

Also note that `HeckeConvexGeneral.fL_convexity` never needed reality.
