/-
# The geometric Hecke operator: normalization, the Tate comparison, and the q-expansion principle

Classical forms of weight `k` are isobaric `P ∈ K[X₀,X₁]`, evaluated on a Weierstrass model `W` at
`ptR W = (c₄(W), −c₆(W))` (the same point as `KatzForms.pt`). This is `f(W, ω_W)`, where `ω_W` is the
invariant differential of the model.

* `aeval_scale`, `aeval_ptR_scale` — **the differential normalization.** For the model change with
  `u` (`x = u²x'`, so `ω' = u·ω`), `P(ptR (C•W)) = u^{−k} P(ptR W)`, i.e. `f(E, uω) = u^{−k} f(E, ω)`.
* `TateAt φ` — the Tate curve over a `K`-algebra `L`, at the parameter `φ(q)`;
  `aeval_ptR_TateAt`: `P(ptR (TateAt φ)) = φ(P(E₄,E₆))`.
* `tateBase` — `Tate(q)` over `L = K⟦t⟧` with `q = t^p`. `tateQuot` gives its `p + 1` quotients, each
  with the differential `ω_C` satisfying `π^*ω_C = ω` (Vélu's normalization):
  * `tateQuot 0`: `Tate(q^p)` with `ω_can/p` (the model change `u = 1/p`), the canonical quotient by `μ_p`;
  * `tateQuot (j+1)`: `Tate(ζ^j t)`, the quotient by `⟨ζ^j t⟩`.
* **`tate_sum_eval`** — `Σ_C P(Tate/C, ω_C) = (p · T_p P)(Tate, ω)`.
* **`hecke_of_tate`** (the q-expansion principle step): if an isobaric `S` of weight `k` takes, at the
  Tate curve, the value `Σ_C P(Tate/C, ω_C)`, then `S = p · T_p P` (`T_p P = heckePoly p P`).
* **`classical_hU`** — the classical-form version of `hU`. Let `Q W : Fin (p+1) → WeierstrassCurve K`
  be the quotient family. Assume (Alg): there is an isobaric `S` with `Σ_c P(Q W c) = S(W)` on the
  good curves; and (Tate): the same `S` satisfies the Tate-curve identity. Then for every good `W`,
  `Σ_c P(ptR (Q W c)) = p · (T_p P)(ptR W)`.
  `classical_hU_noncanonical` gives the `U`-shaped form: `Σ_{c ≠ 0} P(Q W c) = p·T_pP(W) − P(Q W 0)`.
-/
import RamanujanTau.HeckeQExp.Poly
import RamanujanTau.TateCurve.Basic

set_option autoImplicit false

namespace HeckeQExp
open MvPolynomial ModP

/-- `(c₄, −c₆)` of a Weierstrass curve over any commutative ring (`= KatzForms.pt`). -/
def ptR {L : Type*} [CommRing L] (W : WeierstrassCurve L) : Fin 2 → L := ![W.c₄, -W.c₆]

/-! ### The differential normalization -/

section Scale
variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]

/-- **Isobaric scaling**: `P(λ⁴x₀, λ⁶x₁) = λ^k P(x₀, x₁)`. -/
theorem aeval_scale {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k) (l : L) (x : Fin 2 → L) :
    aeval ![l ^ 4 * x 0, l ^ 6 * x 1] P = l ^ k * aeval x P := by
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP (mem_support_iff.mp hd)
  rw [monomial_eq_two]
  simp only [map_mul, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← hw, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
  ring

/-- The model change `x = u²x'`, `y = u³y'` (`ω' = u·ω`). -/
def scaleChange (u : Lˣ) : WeierstrassCurve.VariableChange L := ⟨u, 0, 0, 0⟩

/-- **`f(E, uω) = u^{−k} f(E, ω)`**: `P(ptR (u•W)) = (u⁻¹)^k P(ptR W)`. -/
theorem aeval_ptR_scale {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k) (u : Lˣ)
    (W : WeierstrassCurve L) :
    aeval (ptR (scaleChange u • W)) P = ((u⁻¹ : Lˣ) : L) ^ k * aeval (ptR W) P := by
  have h : ptR (scaleChange u • W) = ![((u⁻¹ : Lˣ) : L) ^ 4 * ptR W 0, ((u⁻¹ : Lˣ) : L) ^ 6 * ptR W 1] := by
    funext i; fin_cases i
    · simp [ptR, scaleChange, WeierstrassCurve.variableChange_c₄]
    · simp [ptR, scaleChange, WeierstrassCurve.variableChange_c₆]
  rw [h, aeval_scale hP]

end Scale

/-! ### Tate curves over `K`-algebras -/

section Tate
variable {K : Type*} [CommRing K] {L : Type*} [CommRing L] [Algebra K L]

/-- The Tate curve over `L` with parameter `φ(q)`: `Tate.map (φ ∘ (ℤ⟦q⟧ → K⟦q⟧))`. -/
noncomputable def TateAt (φ : PowerSeries K →ₐ[K] L) : WeierstrassCurve L :=
  TateCurve.Tate.map (φ.toRingHom.comp (PowerSeries.map (Int.castRingHom K)))

lemma ptR_TateAt (φ : PowerSeries K →ₐ[K] L) : ptR (TateAt φ) = fun i => φ (evVec K i) := by
  funext i; fin_cases i
  · simp [ptR, TateAt, WeierstrassCurve.map_c₄, TateCurve.c₄_Tate_eq_p4, evVec, E4]
  · simp [ptR, TateAt, WeierstrassCurve.map_c₆, TateCurve.c₆_Tate_eq_neg_p6, evVec, E6]

/-- **Evaluation at the Tate curve is the q-expansion**: `P(ptR (TateAt φ)) = φ(P(E₄,E₆))`. -/
theorem aeval_ptR_TateAt (φ : PowerSeries K →ₐ[K] L) (P : MvPolynomial (Fin 2) K) :
    aeval (ptR (TateAt φ)) P = φ (ev K P) := by
  rw [ptR_TateAt, ev, comp_aeval_apply]

end Tate

section Quot
variable {K : Type*} [Field K] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime]

local notation "L" => PowerSeries K

/-- `Tate(q)` over `K⟦t⟧`, `q = t^p`. -/
noncomputable def tateBase : WeierstrassCurve L := TateAt (PowerSeries.expand p hp.out.ne_zero)

/-- The unit `1/p` of `K⟦t⟧`. -/
noncomputable def invP : Lˣ :=
  Units.map (algebraMap K L).toMonoidHom (Units.mk0 (p : K) (Nat.cast_ne_zero.mpr hp.out.ne_zero))⁻¹

lemma coe_invP_inv : (((invP (K := K) p)⁻¹ : Lˣ) : L) = (p : L) := by
  simp [invP]

/-- **The `p + 1` quotients of `Tate(q)`** over `K⟦t⟧` (`t^p = q`), each with `π^*ω_C = ω`:
`0 ↦ (Tate(q^p), ω_can/p)` (canonical subgroup `μ_p`), `j+1 ↦ (Tate(ζ^j t), ω_can)`. -/
noncomputable def tateQuot (ζ : K) : Fin (p + 1) → WeierstrassCurve L :=
  Fin.cases (scaleChange (invP (K := K) p) • TateAt (PowerSeries.expand (R := K) (p * p)
      (p.mul_ne_zero hp.out.ne_zero hp.out.ne_zero)))
    fun j => TateAt (PowerSeries.rescaleAlgHom (ζ ^ (j : ℕ)))

omit [CharZero K] in
lemma rescaleAlgHom_apply (r : K) (F : PowerSeries K) :
    PowerSeries.rescaleAlgHom r F = PowerSeries.rescale r F := by
  rw [← PowerSeries.coe_rescaleAlgHom]; rfl

omit [CharZero K] in
lemma expand_mul_apply (F : PowerSeries K) :
    PowerSeries.expand (p * p) (p.mul_ne_zero hp.out.ne_zero hp.out.ne_zero) F =
      PowerSeries.expand p hp.out.ne_zero (PowerSeries.expand p hp.out.ne_zero F) :=
  PowerSeries.expand_mul p hp.out.ne_zero p hp.out.ne_zero F

/-- **The Tate-curve sum**: `Σ_C P(Tate/C, ω_C) = (p · T_p P)(Tate, ω)` in `K⟦t⟧`. -/
theorem tate_sum_eval {ζ : K} (hζ : IsPrimitiveRoot ζ p) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : Iso P k) :
    ∑ c, aeval (ptR (tateQuot p ζ c)) P =
      aeval (ptR (tateBase p)) (C (p : K) * heckePoly p P) := by
  have hc : (p : K) ^ k = p * algebraMap ℚ K (mulQ p k) := by
    have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    rw [mulQ, map_zpow₀, map_natCast, ← zpow_one_add₀ hp0, add_sub_cancel, zpow_natCast]
  rw [Fin.sum_univ_succ, tateBase, aeval_ptR_TateAt, map_mul, ev_C, ev_heckePoly p hP]
  simp only [tateQuot, Fin.cases_zero, Fin.cases_succ]
  rw [aeval_ptR_scale hP, coe_invP_inv, aeval_ptR_TateAt]
  simp only [aeval_ptR_TateAt, rescaleAlgHom_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.rescale (ζ ^ j) (ev K P)),
    ← tate_geom_sum' hp.out hζ hc, map_mul, PowerSeries.expand_C, expand_mul_apply]
  simp only [map_pow, map_natCast]

omit [CharZero K] in
lemma expand_injective : Function.Injective (PowerSeries.expand p hp.out.ne_zero (R := K)) := by
  intro F G h
  ext n
  have := congrArg (PowerSeries.coeff (p * n)) h
  simpa using this

/-- **The q-expansion principle for `T_p`**: an isobaric `S` of weight `k` whose value at the Tate
curve is `Σ_C P(Tate/C, ω_C)` is `p · T_p P`. -/
theorem hecke_of_tate {ζ : K} (hζ : IsPrimitiveRoot ζ p) {k : ℕ} {P S : MvPolynomial (Fin 2) K}
    (hP : Iso P k) (hS : Iso S k)
    (hT : aeval (ptR (tateBase p)) S = ∑ c, aeval (ptR (tateQuot p ζ c)) P) :
    S = C (p : K) * heckePoly p P := by
  rw [tate_sum_eval p hζ hP, tateBase, aeval_ptR_TateAt, aeval_ptR_TateAt] at hT
  exact ev_injOn_iso isUnit_1728 hS ((iso_heckePoly p hP).C_mul _) (expand_injective p hT)

/-- **The classical-form `hU`** (sum over all `p + 1` subgroups). For a quotient family
`Q W : Fin (p+1) → WeierstrassCurve K` on the curves satisfying `Good`, assume:
* (Alg) `S` is isobaric of weight `k` and `Σ_c P(ptR (Q W c)) = S(ptR W)` for every good `W`;
* (Tate) `S` satisfies the Tate-curve identity `S(Tate) = Σ_C P(Tate/C, ω_C)`.
Then `Σ_c P(ptR (Q W c)) = p · (T_p P)(ptR W)` for every good `W`. -/
theorem classical_hU {ζ : K} (hζ : IsPrimitiveRoot ζ p) {k : ℕ} {P S : MvPolynomial (Fin 2) K}
    (hP : Iso P k) (hS : Iso S k) (Good : WeierstrassCurve K → Prop)
    (Q : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K)
    (hAlg : ∀ W, Good W → ∑ c, eval (ptR (Q W c)) P = eval (ptR W) S)
    (hT : aeval (ptR (tateBase p)) S = ∑ c, aeval (ptR (tateQuot p ζ c)) P) :
    ∀ W, Good W → ∑ c, eval (ptR (Q W c)) P = (p : K) * eval (ptR W) (heckePoly p P) := by
  intro W hW
  rw [hAlg W hW, hecke_of_tate p hζ hP hS hT, map_mul, eval_C]

/-- The `U`-shaped form: the sum over the `p` quotients other than `Q W 0`. -/
theorem classical_hU_noncanonical {ζ : K} (hζ : IsPrimitiveRoot ζ p) {k : ℕ}
    {P S : MvPolynomial (Fin 2) K} (hP : Iso P k) (hS : Iso S k) (Good : WeierstrassCurve K → Prop)
    (Q : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K)
    (hAlg : ∀ W, Good W → ∑ c, eval (ptR (Q W c)) P = eval (ptR W) S)
    (hT : aeval (ptR (tateBase p)) S = ∑ c, aeval (ptR (tateQuot p ζ c)) P) :
    ∀ W, Good W → ∑ j : Fin p, eval (ptR (Q W j.succ)) P =
      (p : K) * eval (ptR W) (heckePoly p P) - eval (ptR (Q W 0)) P := by
  intro W hW
  rw [← classical_hU p hζ hP hS Good Q hAlg hT W hW, Fin.sum_univ_succ]
  ring

/-- On the Tate curve, the non-canonical quotients give `p · U_p`:
`Σ_{j<p} P(Tate(ζ^j t)) = (p · U_p F)(t^p)`, `F = P(E₄,E₆)`. -/
theorem tate_noncanonical_eval {ζ : K} (hζ : IsPrimitiveRoot ζ p) (P : MvPolynomial (Fin 2) K) :
    ∑ j : Fin p, aeval (ptR (tateQuot p ζ j.succ)) P =
      PowerSeries.expand p hp.out.ne_zero
        (PowerSeries.C (p : K) * UpContraction.Up p (ev K P)) := by
  simp only [tateQuot, Fin.cases_succ, aeval_ptR_TateAt, rescaleAlgHom_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.rescale (ζ ^ j) (ev K P)),
    tate_noncanonical_sum hp.out hζ]

end Quot

end HeckeQExp
