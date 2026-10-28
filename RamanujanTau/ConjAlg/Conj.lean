import RamanujanTau.ConjAlg.Main

/-!
# The algebraicity half of `SharpHQ.HConj`

For an arbitrary nonsingular Weierstrass curve `W` over an algebraically closed field `K` of
characteristic `0`, let `Wₛ = short (−c₄/48) (−c₆/864)`: the short model with `u = 1` (so
`ptR Wₛ = ptR W` exactly, `shortModel_ptR`, and `ω` is preserved).

* **`algebraicity_general`**: for every order-`ℓ` subgroup `H₀` of `Wₛ` there is an enumeration
  `G : Fin (ℓ+1) → subgroups` of all `ℓ + 1` order-`ℓ` subgroups, bijective, with `G 0 = H₀`, such
  that for **all** `k`

    `f_k(c₄(W), −c₆(W)) = e_k( Δ(veluC (G c)) : c )`   (`none ↦ G 0`, `some j ↦ G (j+1)`),

  `Δ` being Mathlib's discriminant of the Vélu quotient curve `Wₛ/G_c`.
* **`algebraicity_conj`**: the same in exactly the shape of the first conjunct of
  `SharpHQ.ConjBound` (`KatzForms.pt`, `k ≤ ℓ`), for every test curve `W` (`IsTest W`), with
  hypotheses on `f` exactly those of `SharpHQ.HConj`.
* **`algebraicity_conj_C`**: over `ℂ_ℓ` with `φ = SharpHQ.φC ℓ`.

All modulo the Tate addition theorem only (`hKer : HeckeBridge.TateKernels ℓ L ι ζK`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConjAlg
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal DBound HeckeBridge SubgroupSum Velu

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

section Short
variable {K : Type*} [Field K] [CharZero K]

/-- `a(W) = −c₄/48`. -/
noncomputable def sa (W : WeierstrassCurve K) : K := -W.c₄ / 48
/-- `b(W) = −c₆/864`. -/
noncomputable def sb (W : WeierstrassCurve K) : K := -W.c₆ / 864

/-- **The short model with `u = 1` has the same `(c₄, −c₆)`.** -/
theorem shortModel_ptR (W : WeierstrassCurve K) :
    ptR (short (sa W) (sb W) : WeierstrassCurve K) = ptR W := by
  rw [ptR_short]
  funext i; fin_cases i
  · simp [ptR, sa]; field_simp
  · simp [ptR, sb]; field_simp

lemma shortModel_Δ (W : WeierstrassCurve K) :
    (short (sa W) (sb W) : WeierstrassCurve K).Δ = W.Δ := by
  have h1 := (short (sa W) (sb W) : WeierstrassCurve K).c_relation
  have h2 := W.c_relation
  have h4 := congrFun (shortModel_ptR W) 0
  have h6 := congrFun (shortModel_ptR W) 1
  simp only [ptR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    neg_inj] at h4 h6
  have h1728 : (1728 : K) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h1728
  rw [h1, h2, h4, h6]

lemma shortModel_disc_ne {W : WeierstrassCurve K} (hW : W.Δ ≠ 0) :
    4 * sa W ^ 3 + 27 * sb W ^ 2 ≠ 0 := by
  intro h
  apply hW
  rw [← shortModel_Δ, short_Δ, h, mul_zero]

end Short

variable (hℓ : 5 ≤ ℓ)

section Field
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

/-- **Algebraicity of the `Δ`-modular equation at any nonsingular curve** (modulo `hKer`). -/
theorem algebraicity_general (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hJ : IsModEqCoeffs hℓ f ζ)
    (W : WeierstrassCurve K) (hW : W.Δ ≠ 0) {H₀ : Finset (short (sa W) (sb W)).Point}
    (hH₀ : H₀ ∈ subs (sa W) (sb W) ℓ) :
    ∃ G : Fin (ℓ + 1) → Finset (short (sa W) (sb W)).Point, (∀ c, G c ∈ subs (sa W) (sb W) ℓ) ∧
      Function.Injective G ∧ (∀ H ∈ subs (sa W) (sb W) ℓ, ∃ c, G c = H) ∧ G 0 = H₀ ∧
      ∀ k, eval (ptR W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f k)) =
        eval (fun i : Option (Fin ℓ) => (veluC (G (i.elim 0 Fin.succ))).Δ)
          (esymm (Option (Fin ℓ)) K k) := by
  have hΔ := shortModel_disc_ne hW
  obtain ⟨G, hmem, hinj, hsurj, h0⟩ := exists_enum_algClosed ℓ hΔ hH₀
  refine ⟨G, hmem, hinj, hsurj, h0, fun k => ?_⟩
  have hQ : IsQuotEnum ℓ (short (sa W) (sb W) : WeierstrassCurve K) (fun c => veluC (G c)) :=
    ⟨sa W, sb W, hΔ, rfl, G, hmem, hinj, hsurj, fun _ => rfl⟩
  have h := algebraicity_short ψ hζK ι hι hKer hf hζ hJ _ _ hQ k
  rw [shortModel_ptR] at h
  exact h

end Field

section Normed
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [IsAlgClosed K]
  [DecidableEq K]

/-- **The algebraicity half of `ConjBound`**, in its exact shape: for `f` as in `SharpHQ.HConj`
and every test curve `W`, the conjugates `y_C = Δ(Wₛ/C)` (`none` = the prescribed `H₀`) satisfy
`f_k(pt W) = e_k(y)` for `k ≤ ℓ`. -/
theorem algebraicity_conj (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∃ ζ : PadicAlgCl ℓ, IsPrimitiveRoot ζ ℓ ∧ ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (W : WeierstrassCurve K) (hW : KatzForms.IsTest W) {H₀ : Finset (short (sa W) (sb W)).Point}
    (hH₀ : H₀ ∈ subs (sa W) (sb W) ℓ) :
    ∃ G : Fin (ℓ + 1) → Finset (short (sa W) (sb W)).Point, (∀ c, G c ∈ subs (sa W) (sb W) ℓ) ∧
      Function.Injective G ∧ (∀ H ∈ subs (sa W) (sb W) ℓ, ∃ c, G c = H) ∧ G 0 = H₀ ∧
      ∀ k, k ≤ ℓ → MvPolynomial.eval (KatzForms.pt W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f k)) =
        MvPolynomial.eval (fun i : Option (Fin ℓ) => (veluC (G (i.elim 0 Fin.succ))).Δ)
          (MvPolynomial.esymm (Option (Fin ℓ)) K k) := by
  obtain ⟨ζ, hζ, hJ'⟩ := hJ
  have hW0 : W.Δ ≠ 0 := by
    intro h; have := hW.2.2.2.2.2; rw [h, norm_zero] at this; exact zero_ne_one this
  obtain ⟨G, hmem, hinj, hsurj, h0, hk⟩ :=
    algebraicity_general hℓ ψ hζK ι hι hKer hf hζ hJ' W hW0 hH₀
  exact ⟨G, hmem, hinj, hsurj, h0, fun k _ => hk k⟩

/-- The existential first conjunct of `ConjBound`, for every test curve. -/
theorem conj_first (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∃ ζ : PadicAlgCl ℓ, IsPrimitiveRoot ζ ℓ ∧ ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (W : WeierstrassCurve K) (hW : KatzForms.IsTest W) :
    ∃ y : Option (Fin ℓ) → K, ∀ k, k ≤ ℓ →
      MvPolynomial.eval (KatzForms.pt W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f k)) =
        MvPolynomial.eval y (MvPolynomial.esymm (Option (Fin ℓ)) K k) := by
  have hW0 : W.Δ ≠ 0 := by
    intro h; have := hW.2.2.2.2.2; rw [h, norm_zero] at this; exact zero_ne_one this
  obtain ⟨H₀, hH₀⟩ := subs_nonempty ℓ (shortModel_disc_ne hW0)
  obtain ⟨G, -, -, -, -, hk⟩ := algebraicity_conj hℓ ψ hζK ι hι hKer f hf hJ W hW hH₀
  exact ⟨_, hk⟩

end Normed

/-- **Over `ℂ_ℓ`, with `φ = SharpHQ.φC ℓ`** (the `φ` of the final theorems). -/
theorem algebraicity_conj_C [DecidableEq ℂ_[ℓ]] {ζK : ℂ_[ℓ]} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries ℂ_[ℓ] →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∃ ζ : PadicAlgCl ℓ, IsPrimitiveRoot ζ ℓ ∧ ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (W : WeierstrassCurve ℂ_[ℓ]) (hW : KatzForms.IsTest W)
    {H₀ : Finset (short (sa W) (sb W)).Point} (hH₀ : H₀ ∈ subs (sa W) (sb W) ℓ) :
    ∃ G : Fin (ℓ + 1) → Finset (short (sa W) (sb W)).Point, (∀ c, G c ∈ subs (sa W) (sb W) ℓ) ∧
      Function.Injective G ∧ (∀ H ∈ subs (sa W) (sb W) ℓ, ∃ c, G c = H) ∧ G 0 = H₀ ∧
      ∀ k, k ≤ ℓ → MvPolynomial.eval (KatzForms.pt W) (MvPolynomial.map (SharpHQ.φC ℓ) (f k)) =
        MvPolynomial.eval (fun i : Option (Fin ℓ) => (veluC (G (i.elim 0 Fin.succ))).Δ)
          (MvPolynomial.esymm (Option (Fin ℓ)) ℂ_[ℓ] k) :=
  algebraicity_conj hℓ (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hζK ι hι hKer f hf hJ W hW hH₀

end ConjAlg
