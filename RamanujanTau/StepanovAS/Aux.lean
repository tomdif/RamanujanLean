/-
# Stepanov's method with Hasse derivatives (abstract form)

`K` a finite field of characteristic `p`, `q = #K`, `Q = p^s ∣ q`, `Y = expand Q Y₀`.
Auxiliary polynomial (unknown coefficient polynomials `r_{jk}`, `deg r_{jk} < A`):

  `Φ = ∑_{j<J} ∑_{k<P} r_{jk} · X^{qj} · Y^k`.

* For `ℓ < Q`: `D^{(ℓ)} Φ = ∑ D^{(ℓ)}(r_{jk}) X^{qj} Y^k` (`X^{qj} Y^k` is a polynomial in `X^Q`).
* On a set `S` where `x ≠ 0` and `Y(x)·x^e = Z(x)`:
  `x^{e(P-1)} D^{(ℓ)}Φ(x) = Ψ_ℓ(x)`, `Ψ_ℓ = ∑ D^{(ℓ)}(r_{jk}) X^j Z^k X^{e(P-1-k)}`, `deg Ψ_ℓ < D`.
* Dimension count: `M·D < J·P·A` gives `r ≠ 0` with all `Ψ_ℓ = 0` (`ℓ < M ≤ Q`).
* Nonvanishing: `deg Y = q a + d`, `A ≤ d`, `(P-1) d + A ≤ q` make the degrees of the
  terms pairwise distinct, so `Φ ≠ 0`.
* Hence `M · |S| ≤ deg Φ ≤ A - 1 + q(J-1) + (P-1) deg Y`.
-/
import RamanujanTau.StepanovAS.Hasse

set_option autoImplicit false

namespace RamanujanTau.StepanovAS

open Polynomial Finset

variable {K : Type*} [Field K] [Fintype K]

/-! ### Coefficient vectors -/

/-- polynomial with coefficient vector `w` (degree `< A`). -/
noncomputable def coefPoly (A : ℕ) : (Fin A → K) →ₗ[K] K[X] :=
  ∑ a : Fin A, (monomial (a : ℕ)) ∘ₗ LinearMap.proj a

theorem coefPoly_apply (A : ℕ) (w : Fin A → K) :
    coefPoly A w = ∑ a : Fin A, monomial (a : ℕ) (w a) := by
  simp [coefPoly]

theorem coeff_coefPoly (A : ℕ) (w : Fin A → K) (a : Fin A) :
    (coefPoly A w).coeff a = w a := by
  rw [coefPoly_apply, finsetSum_coeff]
  simp only [coeff_monomial, Fin.val_inj]
  rw [Finset.sum_ite_eq']; simp

theorem natDegree_coefPoly_le (A : ℕ) (w : Fin A → K) : (coefPoly A w).natDegree ≤ A - 1 := by
  rw [coefPoly_apply]
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact (natDegree_monomial_le _).trans (by omega)

/-- unknowns: `v (j, k, a)` = coefficient of `X^a` in `r_{jk}`. -/
abbrev Unk (K : Type*) (J P A : ℕ) := Fin J × Fin P × Fin A → K

noncomputable def rPoly {J P A : ℕ} (v : Unk K J P A) (j : Fin J) (k : Fin P) : K[X] :=
  coefPoly A (fun a => v (j, k, a))

/-- the auxiliary polynomial `Φ`. -/
noncomputable def auxPhi (Y : K[X]) {J P A : ℕ} (v : Unk K J P A) : K[X] :=
  ∑ j : Fin J, ∑ k : Fin P, rPoly v j k * (X ^ (Fintype.card K * (j : ℕ)) * Y ^ (k : ℕ))

/-- the weight `X^j Z^k X^{e(P-1-k)}` of `D^{(ℓ)} r_{jk}` in `Ψ_ℓ`. -/
noncomputable def psiWeight (Z : K[X]) (e P : ℕ) (j k : ℕ) : K[X] :=
  X ^ j * Z ^ k * X ^ (e * (P - 1 - k))

/-- `Ψ_ℓ` as a linear map of the unknowns. -/
noncomputable def psiLin (Z : K[X]) (e : ℕ) (J P A ℓ : ℕ) : Unk K J P A →ₗ[K] K[X] :=
  ∑ j : Fin J, ∑ k : Fin P, LinearMap.mulRight K (psiWeight Z e P j k) ∘ₗ hasseDeriv ℓ ∘ₗ
    coefPoly A ∘ₗ LinearMap.funLeft K K (fun a => (j, k, a))

theorem psiLin_apply (Z : K[X]) (e : ℕ) (J P A ℓ : ℕ) (v : Unk K J P A) :
    psiLin Z e J P A ℓ v =
      ∑ j : Fin J, ∑ k : Fin P, hasseDeriv ℓ (rPoly v j k) * psiWeight Z e P j k := by
  simp [psiLin, rPoly, LinearMap.funLeft]
  rfl

/-! ### Hasse derivatives of `Φ` and evaluation on `S` -/

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem hasseDeriv_auxPhi (s : ℕ) (hQ : p ^ s ∣ Fintype.card K) (Y₀ : K[X]) {J P A : ℕ}
    (v : Unk K J P A) {ℓ : ℕ} (hℓ : ℓ < p ^ s) :
    hasseDeriv ℓ (auxPhi (expand K (p ^ s) Y₀) v) =
      ∑ j : Fin J, ∑ k : Fin P,
        hasseDeriv ℓ (rPoly v j k) * (X ^ (Fintype.card K * (j : ℕ)) *
          (expand K (p ^ s) Y₀) ^ (k : ℕ)) := by
  obtain ⟨q', hq'⟩ := hQ
  rw [auxPhi, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (X ^ (Fintype.card K * (j : ℕ)) * (expand K (p ^ s) Y₀) ^ (k : ℕ) : K[X]) =
      expand K (p ^ s) (X ^ (q' * (j : ℕ)) * Y₀ ^ (k : ℕ)) := by
    rw [map_mul, map_pow, map_pow, expand_X, ← pow_mul, hq', mul_assoc]
  rw [this, hasseDeriv_mul_expand p s _ _ hℓ]

theorem eval_hasseDeriv_auxPhi (s : ℕ) (hQ : p ^ s ∣ Fintype.card K) (Y₀ Z : K[X]) (e : ℕ)
    {J P A : ℕ} (v : Unk K J P A) {ℓ : ℕ} (hℓ : ℓ < p ^ s) (x : K)
    (hx : (expand K (p ^ s) Y₀).eval x * x ^ e = Z.eval x) :
    x ^ (e * (P - 1)) * (hasseDeriv ℓ (auxPhi (expand K (p ^ s) Y₀) v)).eval x =
      (psiLin Z e J P A ℓ v).eval x := by
  rw [hasseDeriv_auxPhi p s hQ Y₀ v hℓ, psiLin_apply, eval_finsetSum, eval_finsetSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) ≤ P - 1 := by omega
  have hsplit : e * (P - 1) = e * k + e * (P - 1 - k) := by
    rw [← Nat.mul_add]; congr 1; omega
  simp only [psiWeight, eval_mul, eval_pow, eval_X]
  rw [← hx, show x ^ (Fintype.card K * (j : ℕ)) = x ^ (j : ℕ) by
    rw [pow_mul, FiniteField.pow_card], hsplit, pow_add, mul_pow, ← pow_mul]
  ring

/-! ### Degree bounds -/

theorem natDegree_psiLin_lt (Z : K[X]) (e W : ℕ) (hZ : Z.natDegree ≤ W) (heW : e ≤ W)
    {J P A : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) (ℓ : ℕ) (v : Unk K J P A) :
    (psiLin Z e J P A ℓ v).natDegree < A + J + (P - 1) * W := by
  rw [psiLin_apply]
  have hle : (∑ j : Fin J, ∑ k : Fin P, hasseDeriv ℓ (rPoly v j k) * psiWeight Z e P j k).natDegree
      ≤ A - 1 + (J - 1) + (P - 1) * W := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    apply natDegree_sum_le_of_forall_le
    intro k _
    have hk : (k : ℕ) ≤ P - 1 := by omega
    have h1 : (hasseDeriv ℓ (rPoly v j k)).natDegree ≤ A - 1 :=
      (natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans (natDegree_coefPoly_le A _))
    have h2 : (psiWeight Z e P j k).natDegree ≤ (J - 1) + (P - 1) * W := by
      unfold psiWeight
      refine natDegree_mul_le.trans ?_
      have h3 : (X ^ (j : ℕ) * Z ^ (k : ℕ) : K[X]).natDegree ≤ (J - 1) + k * W := by
        refine natDegree_mul_le.trans ?_
        rw [natDegree_X_pow]
        have := (natDegree_pow_le (p := Z) (n := k)).trans (Nat.mul_le_mul_left (k : ℕ) hZ)
        omega
      rw [natDegree_X_pow]
      have h4 : e * (P - 1 - k) ≤ W * (P - 1 - k) := Nat.mul_le_mul_right _ heW
      have h5 : (k : ℕ) * W + W * (P - 1 - k) = (P - 1) * W := by
        rw [mul_comm W, ← add_mul]; congr 1; omega
      omega
    exact natDegree_mul_le.trans (by omega)
  omega

theorem natDegree_auxPhi_le (Y : K[X]) {J P A : ℕ} (v : Unk K J P A) :
    (auxPhi Y v).natDegree ≤ A - 1 + Fintype.card K * (J - 1) + (P - 1) * Y.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_sum_le_of_forall_le
  intro k _
  have hk : (k : ℕ) ≤ P - 1 := by omega
  have h1 := natDegree_coefPoly_le A (fun a => v (j, k, a))
  have hj : Fintype.card K * (j : ℕ) ≤ Fintype.card K * (J - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (Y ^ (k : ℕ)).natDegree ≤ (P - 1) * Y.natDegree :=
    natDegree_pow_le.trans (Nat.mul_le_mul_right _ hk)
  refine natDegree_mul_le.trans ?_
  have h3 := natDegree_mul_le (p := (X ^ (Fintype.card K * (j : ℕ)) : K[X])) (q := Y ^ (k : ℕ))
  rw [natDegree_X_pow] at h3
  simp only [rPoly]
  omega

/-! ### Nonvanishing -/

/-- uniqueness of base-`q` digits. -/
theorem digits_eq {q u u' w w' : ℕ} (hw : w < q) (hw' : w' < q) (h : q * u + w = q * u' + w') :
    u = u' ∧ w = w' := by
  have hq : 0 < q := by omega
  have e1 : (q * u + w) / q = u := by rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hw, add_zero]
  have e2 : (q * u' + w') / q = u' := by
    rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hw', add_zero]
  have hu : u = u' := by rw [← e1, ← e2, h]
  subst hu
  exact ⟨rfl, by omega⟩

/-- the exponents `q j + k (q a + d) + n` (`n < A ≤ d`, `k < P`, `(P-1)d + A ≤ q`) are distinct. -/
theorem exps_inj {q a d A P j j' k k' n n' : ℕ} (hAd : A ≤ d) (hPd : (P - 1) * d + A ≤ q)
    (hk : k < P) (hk' : k' < P) (hn : n < A) (hn' : n' < A)
    (h : n + (q * j + k * (q * a + d)) = n' + (q * j' + k' * (q * a + d))) :
    j = j' ∧ k = k' := by
  have hkd : k * d ≤ (P - 1) * d := Nat.mul_le_mul_right _ (by omega)
  have hkd' : k' * d ≤ (P - 1) * d := Nat.mul_le_mul_right _ (by omega)
  have e1 : n + (q * j + k * (q * a + d)) = q * (j + k * a) + (d * k + n) := by ring
  have e2 : n' + (q * j' + k' * (q * a + d)) = q * (j' + k' * a) + (d * k' + n') := by ring
  rw [e1, e2] at h
  obtain ⟨h1, h2⟩ := digits_eq (by rw [mul_comm]; omega) (by rw [mul_comm]; omega) h
  obtain ⟨h3, -⟩ := digits_eq (by omega) (by omega) h2
  subst h3
  exact ⟨by omega, rfl⟩

theorem auxPhi_ne_zero (Y : K[X]) (hY : Y ≠ 0) {J P A a d : ℕ}
    (hdeg : Y.natDegree = Fintype.card K * a + d) (hAd : A ≤ d)
    (hPd : (P - 1) * d + A ≤ Fintype.card K) (v : Unk K J P A) (hv : v ≠ 0) :
    auxPhi Y v ≠ 0 := by
  classical
  set q := Fintype.card K
  let f : Fin J × Fin P → K[X] := fun jk => rPoly v jk.1 jk.2 * (X ^ (q * (jk.1 : ℕ)) * Y ^ (jk.2 : ℕ))
  have hsum : auxPhi Y v = ∑ jk : Fin J × Fin P, f jk := by
    rw [auxPhi, ← Finset.univ_product_univ, Finset.sum_product]
  have hdegf : ∀ jk, f jk ≠ 0 → (f jk).natDegree =
      (rPoly v jk.1 jk.2).natDegree + (q * (jk.1 : ℕ) + jk.2 * (q * a + d)) := by
    intro jk hf
    have hr : rPoly v jk.1 jk.2 ≠ 0 := fun h => hf (by simp [f, h])
    simp only [f]
    rw [natDegree_mul hr (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hY)),
      natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hY), natDegree_X_pow,
      natDegree_pow, hdeg]
  have hlt : ∀ jk : Fin J × Fin P, (rPoly v jk.1 jk.2).natDegree < A := by
    intro jk
    have := natDegree_coefPoly_le A (fun a => v (jk.1, jk.2, a))
    have hA : 0 < A := by
      by_contra h0
      apply hv; funext ⟨_, _, ⟨x, hx⟩⟩; omega
    simp only [rPoly]; omega
  have hdisj : Set.Pairwise {i | i ∈ (Finset.univ : Finset (Fin J × Fin P)) ∧ f i ≠ 0}
      (Function.onFun Ne (natDegree ∘ f)) := by
    intro i hi i' hi' hne heq
    simp only [Function.comp, Set.mem_setOf_eq] at heq hi hi'
    rw [hdegf i hi.2, hdegf i' hi'.2] at heq
    obtain ⟨h1, h2⟩ := exps_inj hAd hPd i.2.isLt i'.2.isLt (hlt i) (hlt i') heq
    exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
  -- a nonzero term
  obtain ⟨⟨j, k, a0⟩, hv0⟩ : ∃ t, v t ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hr0 : rPoly v j k ≠ 0 := by
    intro h
    have := coeff_coefPoly A (fun a => v (j, k, a)) a0
    simp only [rPoly] at h
    rw [h, coeff_zero] at this
    exact hv0 this.symm
  have hf0 : f (j, k) ≠ 0 :=
    mul_ne_zero hr0 (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hY))
  intro h0
  rw [hsum] at h0
  have hdeg0 := degree_sum_eq_of_disjoint f Finset.univ (by
    intro i hi i' hi' hne heq
    apply hdisj hi hi' hne
    simp only [Function.comp] at heq ⊢
    rw [degree_eq_natDegree hi.2, degree_eq_natDegree hi'.2] at heq
    exact_mod_cast heq)
  rw [h0, degree_zero, eq_comm, Finset.sup_eq_bot_iff] at hdeg0
  exact hf0 (degree_eq_bot.mp (hdeg0 (j, k) (Finset.mem_univ _)))

/-! ### The bound -/

theorem eq_zero_of_natDegree_lt_of_coeff_eq_zero {f : K[X]} {D : ℕ} (hq : f.natDegree < D)
    (hc : ∀ d < D, f.coeff d = 0) : f = 0 := by
  ext d
  rw [coeff_zero]
  by_cases hd : d < D
  · exact hc d hd
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Stepanov's bound with Hasse derivatives** (abstract form). -/
theorem stepanov_hasse_card_le (s : ℕ) (hQ : p ^ s ∣ Fintype.card K) (Y₀ Z : K[X])
    (hY : expand K (p ^ s) Y₀ ≠ 0) {e W J P A M a d : ℕ}
    (hdeg : (expand K (p ^ s) Y₀).natDegree = Fintype.card K * a + d) (hAd : A ≤ d)
    (hPd : (P - 1) * d + A ≤ Fintype.card K) (hZ : Z.natDegree ≤ W) (heW : e ≤ W)
    (hA : 1 ≤ A) (hMQ : M ≤ p ^ s) (hdim : M * (A + J + (P - 1) * W) < J * P * A)
    (S : Finset K) (hS : ∀ x ∈ S, x ≠ 0 ∧ (expand K (p ^ s) Y₀).eval x * x ^ e = Z.eval x) :
    M * S.card ≤ A - 1 + Fintype.card K * (J - 1) + (P - 1) * (Fintype.card K * a + d) := by
  classical
  set D := A + J + (P - 1) * W
  set Y := expand K (p ^ s) Y₀
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp at hdim
    · exact h
  let L : Unk K J P A →ₗ[K] (Fin M × Fin D → K) :=
    LinearMap.pi (fun ld : Fin M × Fin D => (lcoeff K (ld.2 : ℕ)) ∘ₗ psiLin Z e J P A ld.1)
  have hrank : Module.finrank K (Fin M × Fin D → K) < Module.finrank K (Unk K J P A) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    calc M * D < J * P * A := hdim
      _ = J * (P * A) := by ring
  obtain ⟨v, hvker, hv0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank)
  have hPsi : ∀ ℓ < M, psiLin Z e J P A ℓ v = 0 := by
    intro ℓ hℓ
    apply eq_zero_of_natDegree_lt_of_coeff_eq_zero
    · exact natDegree_psiLin_lt Z e W hZ heW hA hJ1 ℓ v
    · intro d hd
      have := congrFun (LinearMap.mem_ker.mp hvker) (⟨ℓ, hℓ⟩, ⟨d, hd⟩)
      simpa [L] using this
  have hΦ0 : auxPhi Y v ≠ 0 := auxPhi_ne_zero Y hY hdeg hAd hPd v hv0
  have hmult : ∀ x ∈ S, M ≤ rootMultiplicity x (auxPhi Y v) := by
    intro x hx
    obtain ⟨hx0, hxe⟩ := hS x hx
    apply le_rootMultiplicity_of_hasseDeriv hΦ0 x M
    intro ℓ hℓ
    have h1 := eval_hasseDeriv_auxPhi p s hQ Y₀ Z e v (by omega) x hxe (ℓ := ℓ)
    rw [hPsi ℓ hℓ, eval_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hx0)
  have hle : M • S.val ≤ (auxPhi Y v).roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Multiset.count_nsmul, count_roots]
    by_cases hx : x ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup hx, mul_one]; exact hmult x hx
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using hx)]; simp
  have := Multiset.card_le_card hle
  rw [Multiset.card_nsmul] at this
  calc M * S.card = M * Multiset.card S.val := rfl
    _ ≤ Multiset.card (auxPhi Y v).roots := this
    _ ≤ (auxPhi Y v).natDegree := card_roots' _
    _ ≤ _ := by
      have := natDegree_auxPhi_le Y v
      rw [hdeg] at this; exact this

end RamanujanTau.StepanovAS

#print axioms RamanujanTau.StepanovAS.stepanov_hasse_card_le
