import RamanujanTau.KatzForms.Concrete

/-!
# The residue field of an ultrametric field

`K` ultrametric normed field, `𝒪 = ball1 = {‖x‖ ≤ 1}`, `𝔪 = {‖x‖ < 1}` (`mIdeal`, maximal),
`Res K = 𝒪 ⧸ 𝔪` (a field). `res : 𝒪 →+* Res K`.

* `res_eq_zero_iff`: `res x = 0 ↔ ‖x‖ < 1`.
* `norm_le_one_of_root`: roots of monic integral polynomials are integral.
* `isAlgClosed_res`: if `K` is algebraically closed, so is `Res K`.
* `charP_res`: if `‖(p : K)‖ < 1` (`p` prime) then `Res K` has characteristic `p`.
* `liftO P`: for `P ∈ K[X₀,X₁]` with integral coefficients, the polynomial over `𝒪`;
  `eval_liftO`, `res_eval_liftO`: evaluation commutes with `𝒪 → K` and with `res`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Igusa
open KatzForms

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => (ball1 (K := K))

lemma mem_ball1 {x : K} : x ∈ (ball1 (K := K)) ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- The maximal ideal `{‖x‖ < 1}`. -/
def mIdeal : Ideal 𝒪 where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, norm_mul] at *
    calc ‖(c : K)‖ * ‖(x : K)‖ ≤ 1 * ‖(x : K)‖ :=
          mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

lemma mem_mIdeal {x : 𝒪} : x ∈ (mIdeal (K := K)) ↔ ‖(x : K)‖ < 1 := Iff.rfl

instance mIdeal_isMaximal : (mIdeal (K := K)).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_mIdeal], fun J x hJ hx hxJ => ?_⟩
  have hx1 : ‖(x : K)‖ = 1 := le_antisymm x.2 (not_lt.mp hx)
  have hx0 : (x : K) ≠ 0 := by intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  let y : 𝒪 := ⟨(x : K)⁻¹, by rw [mem_ball1, norm_inv, hx1, inv_one]⟩
  have : y * x = 1 := Subtype.ext (by simp [y, hx0])
  rw [← this]; exact J.mul_mem_left y hxJ

variable (K) in
/-- The residue field. -/
abbrev Res := 𝒪 ⧸ (mIdeal (K := K))

noncomputable instance : Field (Res K) := Ideal.Quotient.field _

/-- Reduction. -/
noncomputable abbrev res : 𝒪 →+* Res K := Ideal.Quotient.mk _

lemma res_eq_zero_iff {x : 𝒪} : res x = 0 ↔ ‖(x : K)‖ < 1 := Ideal.Quotient.eq_zero_iff_mem

lemma norm_eq_one_of_res_ne_zero {x : 𝒪} (h : res x ≠ 0) : ‖(x : K)‖ = 1 :=
  le_antisymm x.2 (not_lt.mp fun h' => h (res_eq_zero_iff.mpr h'))

lemma res_surj : Function.Surjective (res (K := K)) := Ideal.Quotient.mk_surjective

/-- Roots of monic polynomials with integral coefficients are integral. -/
lemma norm_le_one_of_root {g : Polynomial K} (hg : g.Monic) (hint : ∀ n, ‖g.coeff n‖ ≤ 1)
    {s : K} (hs : g.eval s = 0) : ‖s‖ ≤ 1 := by
  by_contra h
  push Not at h
  set n := g.natDegree
  have hsum := hs
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_mul] at hsum
  have hn : ‖s ^ n‖ = ‖∑ i ∈ Finset.range n, g.coeff i * s ^ i‖ := by
    have : s ^ n = -(∑ i ∈ Finset.range n, g.coeff i * s ^ i) := by linear_combination hsum
    rw [this, norm_neg]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero, norm_one, Finset.range_zero, Finset.sum_empty, norm_zero] at hn
    exact one_ne_zero hn
  have hle : ‖∑ i ∈ Finset.range n, g.coeff i * s ^ i‖ ≤ ‖s‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    calc ‖g.coeff i‖ * ‖s‖ ^ i ≤ 1 * ‖s‖ ^ (n - 1) :=
          mul_le_mul (hint i) (pow_le_pow_right₀ h.le (by simp at hi; omega)) (by positivity)
            zero_le_one
      _ = ‖s‖ ^ (n - 1) := one_mul _
  rw [← hn, norm_pow] at hle
  have : ‖s‖ ^ (n - 1) < ‖s‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

/-- The residue field of an algebraically closed ultrametric field is algebraically closed. -/
instance isAlgClosed_res [IsAlgClosed K] : IsAlgClosed (Res K) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  have hl : f ∈ Polynomial.lifts (res (K := K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]; intro n; exact res_surj _
  obtain ⟨q, hqf, hqdeg, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  set g := q.map (ball1 (K := K)).subtype
  have hgm : g.Monic := hqm.map _
  have hdeg : g.degree ≠ 0 := by
    rw [show g = q.map (ball1 (K := K)).subtype from rfl, hqm.degree_map,
      Polynomial.degree_eq_natDegree hqm.ne_zero, hqdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root g hdeg
  have hint : ∀ n, ‖g.coeff n‖ ≤ 1 := fun n => by
    rw [Polynomial.coeff_map]; exact (q.coeff n).2
  have hs1 := norm_le_one_of_root hgm hint hs
  set y : 𝒪 := ⟨s, hs1⟩
  have hqy : q.eval y = 0 := by
    apply Subtype.val_injective
    have : g.eval s = (ball1 (K := K)).subtype (q.eval y) := by
      rw [Polynomial.eval_map, ← Polynomial.eval₂_at_apply]; rfl
    have h2 : (ball1 (K := K)).subtype (q.eval y) = 0 := by rw [← this]; exact hs
    simpa using h2
  refine ⟨res y, ?_⟩
  rw [← hqf, Polynomial.eval_map, Polynomial.eval₂_at_apply, hqy, map_zero]

/-- Residue characteristic `p`. -/
lemma charP_res {p : ℕ} (hp : p.Prime) (hpK : ‖(p : K)‖ < 1) : CharP (Res K) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  rw [← map_natCast (res (K := K)), res_eq_zero_iff]
  simpa using hpK

/-! ### Integral polynomials -/

/-- The `𝒪`-polynomial with the same coefficients as an integral `P`. -/
noncomputable def liftO (P : MvPolynomial (Fin 2) K) (hP : ∀ d, ‖P.coeff d‖ ≤ 1) :
    MvPolynomial (Fin 2) 𝒪 :=
  ∑ d ∈ P.support, MvPolynomial.monomial d ⟨P.coeff d, hP d⟩

lemma coeff_liftO (P : MvPolynomial (Fin 2) K) (hP : ∀ d, ‖P.coeff d‖ ≤ 1) (d : Fin 2 →₀ ℕ) :
    (liftO P hP).coeff d = ⟨P.coeff d, hP d⟩ := by
  classical
  rw [liftO, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · apply Subtype.ext; simp [MvPolynomial.notMem_support_iff.mp h]

lemma map_liftO (P : MvPolynomial (Fin 2) K) (hP : ∀ d, ‖P.coeff d‖ ≤ 1) :
    MvPolynomial.map (ball1 (K := K)).subtype (liftO P hP) = P := by
  ext d; rw [MvPolynomial.coeff_map, coeff_liftO]; rfl

lemma eval_liftO (P : MvPolynomial (Fin 2) K) (hP : ∀ d, ‖P.coeff d‖ ≤ 1) (x : Fin 2 → 𝒪) :
    ((MvPolynomial.eval x (liftO P hP) : 𝒪) : K) = MvPolynomial.eval (fun i => (x i : K)) P := by
  conv_rhs => rw [← map_liftO P hP]
  rw [MvPolynomial.eval_map]
  have := MvPolynomial.eval₂_comp_left (ball1 (K := K)).subtype (RingHom.id _) x (liftO P hP)
  rw [RingHom.comp_id] at this
  exact this

lemma res_eval (Q : MvPolynomial (Fin 2) 𝒪) (x : Fin 2 → 𝒪) :
    res (MvPolynomial.eval x Q) = MvPolynomial.eval (fun i => res (x i)) (MvPolynomial.map res Q) := by
  rw [MvPolynomial.eval_map]
  have := MvPolynomial.eval₂_comp_left (res (K := K)) (RingHom.id _) x Q
  rw [RingHom.comp_id] at this
  exact this

end Igusa
