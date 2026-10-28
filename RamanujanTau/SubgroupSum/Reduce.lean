import RamanujanTau.SubgroupSum.Scale

/-!
# From "some polynomial" to "an isobaric polynomial", and the `hAlg` shape

* `eval_component_eq` — if `S(u⁴x₀, u⁶x₁) = u^k S(x)` for all `u ≠ 0` (`K` infinite), then
  `S(x) = S_k(x)`, `S_k` the weight-`k` component of `S`.
* `eval_eq_component_of_scaling` — if a function `Σ(a, b)` scales like weight `k` and agrees with
  `S(−48a, 864b)` on a scale-stable set of `(a, b)`, it agrees there with `S_k(−48a, 864b)`.
* **`exists_iso_of_poly`** — for the subgroup sum of an isobaric `P` of weight `k`: if it is given by
  *some* polynomial `S` in `(c₄, −c₆)` on a scale-stable set of short curves, then by an isobaric one
  of weight `k`.
* `sum_kernels_eq_subSum` — the sum over an enumeration `κ : Fin m → Kernel A B` of all subgroups of
  order `n` of `P(ptR (κ c).curve)` is `subSum n _ A B` (the form appearing in `hAlg`).
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu MvPolynomial ModP

variable {K : Type*} [Field K]

/-- **Extraction of the weight-`k` component from the scaling law.** -/
theorem eval_component_eq [Infinite K] (S : MvPolynomial (Fin 2) K) (x : Fin 2 → K) (k : ℕ)
    (h : ∀ u : K, u ≠ 0 → eval ![u ^ 4 * x 0, u ^ 6 * x 1] S = u ^ k * eval x S) :
    eval x (weightedHomogeneousComponent wt k S) = eval x S := by
  classical
  set e : (Fin 2 →₀ ℕ) → K := fun d => eval x (monomial d (coeff d S)) with he
  have hmono : ∀ (u : K) (d : Fin 2 →₀ ℕ), eval ![u ^ 4 * x 0, u ^ 6 * x 1]
      (monomial d (coeff d S)) = u ^ (Finsupp.weight wt d) * e d := by
    intro u d
    have := HeckeQExp.aeval_scale (isWeightedHomogeneous_monomial wt d (coeff d S) rfl) u x
    simpa only [MvPolynomial.coe_aeval_eq_eval] using this
  have hsum : ∀ y : Fin 2 → K, eval y S = ∑ d ∈ S.support, eval y (monomial d (coeff d S)) := by
    intro y; conv_lhs => rw [S.as_sum]
    rw [map_sum]
  set Q : Polynomial K := ∑ d ∈ S.support, Polynomial.C (e d) * Polynomial.X ^ (Finsupp.weight wt d)
    - Polynomial.C (eval x S) * Polynomial.X ^ k with hQ
  have hroot : ∀ u : K, u ≠ 0 → Q.IsRoot u := by
    intro u hu
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_sub, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [sub_eq_zero, mul_comm (eval x S), ← h u hu, hsum]
    simp only [hmono]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact ((Set.finite_singleton (0 : K)).infinite_compl).mono fun u hu => hroot u hu
  have hk := congrArg (Polynomial.coeff · k) hQ0
  simp only [hQ, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero, sub_eq_zero, ↓reduceIte] at hk
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter, ← hk]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : Finsupp.weight wt d = k
  · rw [if_pos hd, if_pos hd.symm]
  · rw [if_neg hd, if_neg (Ne.symm hd)]

/-- **Isobaric reduction.** -/
theorem eval_eq_component_of_scaling [Infinite K] (k : ℕ) (Sig : K → K → K)
    (hscale : ∀ u : K, u ≠ 0 → ∀ a b, Sig (u ^ 4 * a) (u ^ 6 * b) = u ^ k * Sig a b)
    (Good : K → K → Prop) (hGood : ∀ u : K, u ≠ 0 → ∀ a b, Good a b → Good (u ^ 4 * a) (u ^ 6 * b))
    (S : MvPolynomial (Fin 2) K) (hS : ∀ a b, Good a b → Sig a b = eval ![-48 * a, 864 * b] S) :
    ∀ a b, Good a b → Sig a b = eval ![-48 * a, 864 * b] (weightedHomogeneousComponent wt k S) := by
  intro a b hab
  rw [eval_component_eq S _ k fun u hu => ?_, hS a b hab]
  have e : ![u ^ 4 * ![-48 * a, 864 * b] 0, u ^ 6 * ![-48 * a, 864 * b] 1] =
      ![-48 * (u ^ 4 * a), 864 * (u ^ 6 * b)] := by
    funext i; fin_cases i <;> simp <;> ring
  rw [e, ← hS _ _ (hGood u hu a b hab), hscale u hu, hS a b hab]

variable [DecidableEq K]

/-- **The subgroup sum of an isobaric form: polynomial ⇒ isobaric polynomial.** If on a
scale-stable set `Good` of short curves the subgroup sum `Σ_{|G|=n} P(ptR(E/G))` equals
`S(ptR E)` for *some* polynomial `S`, then it equals `S'(ptR E)` for an isobaric `S'` of weight `k`
(namely the weight-`k` component of `S`). -/
theorem exists_iso_of_poly [Infinite K] (n : ℕ) {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (Good : K → K → Prop) (hGood : ∀ u : K, u ≠ 0 → ∀ a b, Good a b → Good (u ^ 4 * a) (u ^ 6 * b))
    (S : MvPolynomial (Fin 2) K)
    (hS : ∀ a b, Good a b →
      subSum n (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) P) a b =
        eval (HeckeQExp.ptR (short a b : WeierstrassCurve K)) S) :
    ∃ S' : MvPolynomial (Fin 2) K, Iso S' k ∧ ∀ a b, Good a b →
      subSum n (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) P) a b =
        eval (HeckeQExp.ptR (short a b : WeierstrassCurve K)) S' := by
  refine ⟨weightedHomogeneousComponent wt k S,
    weightedHomogeneousComponent_isWeightedHomogeneous k S, fun a b hab => ?_⟩
  rw [ptR_short]
  refine eval_eq_component_of_scaling k _ (fun u hu a b => subSum_ptR_scale hu a b n hP) Good hGood
    S (fun a b hab => ?_) a b hab
  rw [hS a b hab, ptR_short]

omit [DecidableEq K] in
/-- Discriminant-nonzero short curves form a scale-stable set. -/
lemma disc_scale {u : K} (hu : u ≠ 0) {a b : K} (h : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    4 * (u ^ 4 * a) ^ 3 + 27 * (u ^ 6 * b) ^ 2 ≠ 0 := by
  have : 4 * (u ^ 4 * a) ^ 3 + 27 * (u ^ 6 * b) ^ 2 = u ^ 12 * (4 * a ^ 3 + 27 * b ^ 2) := by ring
  rw [this]; exact mul_ne_zero (pow_ne_zero _ hu) h

/-- **The `hAlg` shape.** If `G : Fin m → Finset E(K)` enumerates the subgroups of order `n`
bijectively, then `Σ_c f(A'_{G c}, B'_{G c}) = subSum n f A B`. -/
theorem sum_fin_eq_subSum {A B : K} {n m : ℕ} (f : K → K → K) (G : Fin m → Finset (short A B).Point)
    (hmem : ∀ c, G c ∈ subs A B n) (hinj : Function.Injective G)
    (hsurj : ∀ H ∈ subs A B n, ∃ c, G c = H) :
    ∑ c, f (aC (G c)) (bC (G c)) = subSum n f A B := by
  classical
  have hset : subs A B n = Set.range G := by
    ext H; exact ⟨fun h => hsurj H h, by rintro ⟨c, rfl⟩; exact hmem c⟩
  have hfin : (subs A B n).Finite := hset ▸ Set.finite_range G
  unfold subSum
  rw [dif_pos hfin]
  have : hfin.toFinset = Finset.univ.image G := by
    ext H; simp [hset]
  rw [this, Finset.sum_image fun x _ y _ h => hinj h]

/-- The same for Vélu kernel data: `Σ_c P(ptR (κ c).curve) = subSum n _ A B`. -/
theorem sum_kernels_eq_subSum (h2 : (2 : K) ≠ 0) {A B : K} {n m : ℕ} (P : MvPolynomial (Fin 2) K)
    (κ : Fin m → Kernel A B) (hmem : ∀ c, (κ c).G ∈ subs A B n)
    (hinj : Function.Injective fun c => (κ c).G) (hsurj : ∀ H ∈ subs A B n, ∃ c, (κ c).G = H) :
    ∑ c, eval (HeckeQExp.ptR ((κ c).curve : WeierstrassCurve K)) P =
      subSum n (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) P) A B := by
  rw [← sum_fin_eq_subSum _ (fun c => (κ c).G) hmem hinj hsurj]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Kernel.curve_eq_veluC h2]
  rfl

end SubgroupSum
