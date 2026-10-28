import RamanujanTau.ConjAlg.Newton

/-!
# Algebraicity of the `Δ`-modular equation at a short test curve

Let `K` be an algebraically closed field of characteristic `0`, `ψ : ℚ_ℓ → K`, `φ = ψ ∘ (ℤ_ℓ → ℚ_ℓ)`,
and let `f_k` be the coefficients of the `Δ`-modular equation (`IsModEqCoeffs`: `J(f_k) = e_k(ys)`).
For a nonsingular short curve `W` over `K` and an enumeration `Qs` of its `ℓ + 1` Vélu quotients
(`HeckeBridge.IsQuotEnum`; index `0` may be prescribed, `HeckeBridge.exists_quotEnum`):

  **`f_k(W) = e_k(Δ(W/C) : C)`** for every `k` (`algebraicity_short`),

where `Δ(W/C)` is Mathlib's discriminant of the Vélu curve `veluC G_C`
(`= (c₄³ − c₆²)/1728 = Pdisc(ptR (W/C))`, `eval_Pdisc`). This is modulo only the Tate addition
theorem `hKer : HeckeBridge.TateKernels` (through `HeckeBridge.classical_hU_short`).

Proof: power sums `Σ_C Δ(W/C)^m = ℓ·(T_ℓ Δ^m)(W)` (`classical_hU_short`, `P = Δ^m`); the polynomial
Newton identities `ConjAlg.newton_poly` evaluated at `W`; Newton's identities in `K`; induction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConjAlg
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal DBound HeckeBridge SubgroupSum Velu

/-! ### pointwise Newton -/

/-- If `F` satisfies Newton's recursion with the power sums of `y` (and `F 0 = 1`), then
`F k = e_k(y)`. -/
theorem eq_esymm_of_newton {K σ : Type*} [Field K] [CharZero K] [Fintype σ] (y : σ → K)
    (F p : ℕ → K) (hp : ∀ m, 1 ≤ m → ∑ i, y i ^ m = p m) (h0 : F 0 = 1)
    (hN : ∀ k : ℕ, (k : K) * F k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1) ^ a.1 * F a.1 * p a.2) :
    ∀ k, F k = eval y (esymm σ K k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [h0, esymm_zero, map_one]
  have hE := congrArg (eval y) (mul_esymm_eq_sum σ K k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hE
  have hS : ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1) ^ a.1 * F a.1 * p a.2 =
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * eval y (esymm σ K a.1) * eval y (psum σ K a.2) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    rw [ih a.1 ha2, ← hp a.2 (by omega)]
    simp [psum]
  have hk0 : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  apply mul_left_cancel₀ hk0
  rw [hN, hS, hE]

/-! ### `Δ = Pdisc(c₄, −c₆)` -/

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {hℓ : 5 ≤ ℓ}

/-- **`Pdisc` at `ptR E` is Mathlib's discriminant `E.Δ`.** -/
theorem eval_Pdisc (hℓ : 5 ≤ ℓ) {K : Type*} [CommRing K] (φ : ℤ_[ℓ] →+* K)
    (E : WeierstrassCurve K) : eval (ptR E) (MvPolynomial.map φ (Pdisc hℓ)) = E.Δ := by
  have hu : φ (↑(isUnit_1728_Zp (p := ℓ) hℓ).unit⁻¹ : ℤ_[ℓ]) * 1728 = 1 := by
    rw [show (1728 : K) = φ 1728 from (map_ofNat _ _).symm, ← map_mul,
      (isUnit_1728_Zp (p := ℓ) hℓ).val_inv_mul, map_one]
  simp only [Pdisc, map_mul, map_C, map_sub, map_pow, map_X, eval_mul, eval_C, eval_sub, eval_pow,
    eval_X]
  simp only [ptR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [neg_sq, ← E.c_relation, ← mul_assoc, hu, one_mul]

/-! ### the algebraicity theorem -/

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

/-- The conjugates `y_C = Δ(W/C)`, indexed by `Option (Fin ℓ)` (`none ↦ Qs 0`, `some j ↦ Qs (j+1)`). -/
def conjs (Qs : Fin (ℓ + 1) → WeierstrassCurve K) : Option (Fin ℓ) → K :=
  fun i => (Qs (i.elim 0 Fin.succ)).Δ

lemma sum_conjs (Qs : Fin (ℓ + 1) → WeierstrassCurve K) (g : K → K) :
    ∑ i, g (conjs Qs i) = ∑ c, g (Qs c).Δ := by
  rw [Fintype.sum_option, Fin.sum_univ_succ]; rfl

/-- **Algebraicity of the `Δ`-modular equation at a short test curve** (modulo `hKer`):
`f_k(W) = e_k(Δ(W/C))` for all `k`, over any algebraically closed `K` of characteristic `0`. -/
theorem algebraicity_short (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hJ : IsModEqCoeffs hℓ f ζ)
    (W : WeierstrassCurve K) (Qs : Fin (ℓ + 1) → WeierstrassCurve K) (hQ : IsQuotEnum ℓ W Qs) :
    ∀ k, eval (ptR W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f k)) =
      eval (conjs Qs) (esymm (Option (Fin ℓ)) K k) := by
  have hp2 : ℓ ≠ 2 := by omega
  obtain ⟨D, hD⟩ : ∃ D : MvPolynomial (Fin 2) K, D = MvPolynomial.map (ψ.comp (ιz ℓ)) (Pdisc hℓ) :=
    ⟨_, rfl⟩
  have hD1 : Iso D 12 := by
    subst hD
    exact @iso_map _ _ _ _ (ψ.comp (ιz ℓ)) (Pdisc hℓ) 12 (iso_Pdisc hℓ)
  have hDm : ∀ m, Iso (D ^ m) (m * 12) := fun m =>
    iso_of_eq (hD1.pow m) (by rw [smul_eq_mul])
  obtain ⟨p, hp⟩ : ∃ p : ℕ → K, p = fun m => (ℓ : K) * eval (ptR W) (heckePoly ℓ (D ^ m)) :=
    ⟨_, rfl⟩
  -- power sums
  have hpow : ∀ m, 1 ≤ m → ∑ i, conjs Qs i ^ m = p m := by
    intro m _
    rw [sum_conjs Qs (· ^ m)]
    have h := classical_hU_short ℓ hζK hp2 ι hι hKer (hDm m) (fun _ => Qs) W hQ
    rw [hp]; beta_reduce; rw [← h]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eval_pow, hD, eval_Pdisc hℓ]
  -- the mapped polynomial Newton identities
  have hmapS : ∀ m, MvPolynomial.map ψ (sigP (Pdisc hℓ) m) = C (ℓ : K) * heckePoly ℓ (D ^ m) := by
    intro m
    rw [sigP, map_mul, map_C, map_natCast, map_heckePoly, map_pow, Pq, map_map, hD]
  have hN : ∀ k : ℕ, (k : K) * eval (ptR W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f k)) =
      (-1) ^ (k + 1) * ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * eval (ptR W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f a.1)) * p a.2 := by
    intro k
    have h := congrArg (fun P => eval (ptR W) (MvPolynomial.map ψ P)) (newton_poly hf hζ hJ k)
    simp only [map_mul, map_sum, map_C, eval_mul, eval_sum, eval_C, map_pow, map_neg, map_one,
      map_natCast, map_map, hmapS] at h
    rw [h, hp]
  have h0 : eval (ptR W) (MvPolynomial.map (ψ.comp (ιz ℓ)) (f 0)) = 1 := by
    rw [← map_map, f_zero hf hJ, map_one, map_one]
  exact eq_esymm_of_newton (conjs Qs) _ p hpow h0 hN

end ConjAlg
