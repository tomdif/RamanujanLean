/-
# The numerator of Vélu's `X'` and the `2`-torsion

`E : y² = x³ + Ax + B` over a field `K` (`2 ≠ 0`, `4A³ + 27B² ≠ 0`), `κ` Vélu kernel data (odd order
subgroup `G`, half-system `S`, `n = |S|`). Vélu's `X' = N₁/D³` has
  `N₁ = ∏_{i=1,2,3} ∏_{Q∈S} (X - x(T_i + Q))`,
where `T_1, T_2, T_3` are the nonzero `2`-torsion points (`N1_eq_prod`): each `x(T_i + Q)` is a root
(`Y(T_i + Q) = Y(T_i) = 0` by `G`-invariance, and `y(T_i + Q) ≠ 0`), these `3n` roots are distinct,
and `N₁` is monic of degree `3n`.
Moreover `x(T + Q)·(x_Q - e) = e x_Q + 2e² + A` for `T = (e, 0)` (`xc_add_two_torsion`).
-/
import RamanujanTau.Velu.All

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open Polynomial Velu WeierstrassCurve

section Roots
variable {K : Type*} [Field K]

/-- `x³ + Ax + B = ∏ (x - eᵢ)` gives Vieta. -/
lemma cubic_prod (e1 e2 e3 : K) :
    (X - C e1) * (X - C e2) * (X - C e3) =
      X ^ 3 - C (e1 + e2 + e3) * X ^ 2 + C (e1 * e2 + e1 * e3 + e2 * e3) * X - C (e1 * e2 * e3) := by
  simp only [map_add, map_mul]; ring

lemma disc_identity (e1 e2 e3 : K) (hs : e1 + e2 + e3 = 0) :
    4 * (e1 * e2 + e1 * e3 + e2 * e3) ^ 3 + 27 * (e1 * e2 * e3) ^ 2 =
      -((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 := by
  have : e3 = -e1 - e2 := by linear_combination hs
  subst this; ring

/-- the three roots of a cubic with nonzero discriminant over an algebraically closed field. -/
theorem exists_roots [IsAlgClosed K] {A B : K} (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ e : Fin 3 → K, Function.Injective e ∧ ∀ i, e i ^ 3 + A * e i + B = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : K[X], f = X ^ 3 + C A * X + C B := ⟨_, rfl⟩
  have hdeg : f.natDegree = 3 := by rw [hf]; compute_degree!
  have hmon : f.Monic := by rw [hf]; monicity!
  have hcard : f.roots.card = 3 := by rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  obtain ⟨e1, e2, e3, he⟩ := Multiset.card_eq_three.1 hcard
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hcard, hdeg])
  rw [he] at hprod
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hprod
  have hp : f = X ^ 3 - C (e1 + e2 + e3) * X ^ 2 + C (e1 * e2 + e1 * e3 + e2 * e3) * X -
      C (e1 * e2 * e3) := by rw [← hprod, ← cubic_prod]; ring
  have c2 := congrArg (coeff · 2) hp
  have c1 := congrArg (coeff · 1) hp
  have c0 := congrArg (coeff · 0) hp
  simp only [hf, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at c2 c1 c0
  norm_num at c2 c1 c0
  have hs : e1 + e2 + e3 = 0 := by linear_combination c2
  have hA : A = e1 * e2 + e1 * e3 + e2 * e3 := c1
  have hB : B = -(e1 * e2 * e3) := c0
  have hd : (e1 - e2) * (e1 - e3) * (e2 - e3) ≠ 0 := by
    intro h0
    apply hΔ
    rw [hA, hB, neg_sq, disc_identity e1 e2 e3 hs, h0]; ring
  have hroot : ∀ r ∈ f.roots, r ^ 3 + A * r + B = 0 := by
    intro r hr
    have h := ((mem_roots hmon.ne_zero).1 hr).eq_zero
    simp only [hf, eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    exact h
  refine ⟨![e1, e2, e3], ?_, ?_⟩
  · intro i j hij
    have h12 : e1 ≠ e2 := fun h => hd (by rw [h]; ring)
    have h13 : e1 ≠ e3 := fun h => hd (by rw [h]; ring)
    have h23 : e2 ≠ e3 := fun h => hd (by rw [h]; ring)
    clear hroot hp hprod c2 c1 c0 he hcard hmon hdeg hf hd hs hA hB hΔ
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> exact hroot _ (by rw [he]; simp)

end Roots

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

/-- `x(T + Q)·(x_Q - e) = e x_Q + 2e² + A` for `T = (e, 0)`. -/
lemma xc_add_alg {e xq yq x3 : K} (he : e ^ 3 + A * e + B = 0)
    (hq : yq ^ 2 = xq ^ 3 + A * xq + B) (hx : e ≠ xq)
    (h3 : x3 = ((0 - yq) / (e - xq)) ^ 2 - e - xq) :
    x3 * (xq - e) = e * xq + 2 * e ^ 2 + A := by
  have hd : e - xq ≠ 0 := sub_ne_zero.2 hx
  have hd' : xq - e ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  subst h3
  have hB : B = -e ^ 3 - A * e := by linear_combination he
  subst hB
  field_simp
  linear_combination (xq - e) * hq

namespace Kernel'

variable (κ : Velu.Kernel A B)

/-- the `2`-torsion point `(e, 0)`. -/
noncomputable def T2 (h2 : (2 : K) ≠ 0) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) {e : K}
    (he : e ^ 3 + A * e + B = 0) : (short A B).Point :=
  .some e 0 (by
    have hΔ' : (short A B).Δ ≠ 0 := by
      rw [short_Δ]
      have h16 : (16 : K) ≠ 0 := by
        have : (16 : K) = 2 ^ 4 := by norm_num
        rw [this]; exact pow_ne_zero 4 h2
      exact mul_ne_zero (neg_ne_zero.2 h16) hΔ
    refine (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').1 ?_
    rw [short_equation_iff]; linear_combination -he)

variable (h2 : (2 : K) ≠ 0) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)

lemma T2_ne {e : K} (he : e ^ 3 + A * e + B = 0) : T2 h2 hΔ he ≠ 0 := by
  rw [T2]; exact fun h => by cases h

lemma xc_T2 {e : K} (he : e ^ 3 + A * e + B = 0) : xc (T2 h2 hΔ he) = e := rfl
lemma yc_T2 {e : K} (he : e ^ 3 + A * e + B = 0) : yc (T2 h2 hΔ he) = 0 := rfl

lemma two_T2 {e : K} (he : e ^ 3 + A * e + B = 0) : T2 h2 hΔ he + T2 h2 hΔ he = 0 := by
  rw [T2]
  apply Affine.Point.add_self_of_Y_eq
  simp [Affine.negY]

lemma two_tor_of_yc {P : (short A B).Point} (hP : P ≠ 0) (hy : yc P = 0) : P + P = 0 := by
  obtain ⟨h, eP⟩ := eq_some_of_ne_zero hP
  rw [eP]
  apply Affine.Point.add_self_of_Y_eq
  simp [Affine.negY, hy]

lemma eq_zero_of_two_tor_mem {P : (short A B).Point} (hP : P ∈ κ.G) (h : P + P = 0) : P = 0 :=
  κ.no_two_torsion P hP h

lemma T2_not_mem {e : K} (he : e ^ 3 + A * e + B = 0) : T2 h2 hΔ he ∉ κ.G := fun h =>
  T2_ne h2 hΔ he (κ.no_two_torsion _ h (two_T2 h2 hΔ he))

lemma sub_mem {P Q : (short A B).Point} (hP : P ∈ κ.G) (hQ : Q ∈ κ.G) : P - Q ∈ κ.G := by
  rw [sub_eq_add_neg]; exact κ.add_mem _ hP _ (κ.neg_mem _ hQ)

lemma add_T2_not_mem {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point} (hQ : Q ∈ κ.G) :
    T2 h2 hΔ he + Q ∉ κ.G := by
  intro h
  apply T2_not_mem κ h2 hΔ he
  have := sub_mem κ h hQ
  simpa using this

lemma add_T2_ne {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point} (hQ : Q ∈ κ.G) :
    T2 h2 hΔ he + Q ≠ 0 := fun h => add_T2_not_mem κ h2 hΔ he hQ (h ▸ κ.zero_mem)

lemma yc_add_T2_ne {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point} (hQ : Q ∈ κ.S) :
    yc (T2 h2 hΔ he + Q) ≠ 0 := by
  intro hy
  have h1 := two_tor_of_yc (add_T2_ne κ h2 hΔ he (κ.S_sub hQ)) hy
  have h2' : Q + Q = 0 := by
    have := two_T2 h2 hΔ he
    calc Q + Q = (T2 h2 hΔ he + Q) + (T2 h2 hΔ he + Q) - (T2 h2 hΔ he + T2 h2 hΔ he) := by abel
      _ = 0 := by rw [h1, this, sub_zero]
  exact κ.ne_zero_of_mem_S hQ (κ.no_two_torsion Q (κ.S_sub hQ) h2')

/-- `X'(x(T + Q)) = 0`. -/
lemma Xd_add_T2 {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point} (hQ : Q ∈ κ.S) :
    κ.Xd (xc (T2 h2 hΔ he + Q)) = 0 := by
  have h := κ.Y_add_mem h2 (T2_ne h2 hΔ he) (T2_not_mem κ h2 hΔ he) (κ.S_sub hQ)
  rw [Kernel.Y_eq, Kernel.Y_eq, yc_T2, zero_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (yc_add_T2_ne κ h2 hΔ he hQ)

lemma N1_eval_add_T2 {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point} (hQ : Q ∈ κ.S) :
    κ.N1.eval (xc (T2 h2 hΔ he + Q)) = 0 := by
  have hx : ∀ Q' ∈ κ.S, xc (T2 h2 hΔ he + Q) ≠ xc Q' := fun Q' hQ' =>
    κ.xc_ne_of_not_mem_G (add_T2_ne κ h2 hΔ he (κ.S_sub hQ)) (add_T2_not_mem κ h2 hΔ he
      (κ.S_sub hQ)) hQ'
  have h := κ.Xd_eq_div hx
  rw [Xd_add_T2 κ h2 hΔ he hQ, eq_comm, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) (κ.eval_D_ne hx)

/-- the explicit formula for `x(T + Q)`. -/
lemma xc_add_two_torsion {e : K} (he : e ^ 3 + A * e + B = 0) {Q : (short A B).Point}
    (hQ : Q ∈ κ.S) : xc (T2 h2 hΔ he + Q) * (xc Q - e) = e * xc Q + 2 * e ^ 2 + A := by
  have hQ0 := κ.ne_zero_of_mem_S hQ
  have hx : xc (T2 h2 hΔ he) ≠ xc Q := by
    intro h
    rcases Kernel.eq_or_eq_neg_of_xc_eq (T2_ne h2 hΔ he) hQ0 h with h' | h'
    · exact T2_not_mem κ h2 hΔ he (h' ▸ κ.S_sub hQ)
    · exact T2_not_mem κ h2 hΔ he (h' ▸ κ.neg_mem _ (κ.S_sub hQ))
  have hc := (add_coords_of_xc_ne (T2_ne h2 hΔ he) hQ0 hx).1
  rw [xc_T2, yc_T2] at hc
  exact xc_add_alg he (equation_xc_yc hQ0) hx hc

lemma D_monic : κ.D.Monic :=
  monic_prod_of_monic _ _ (fun Q _ => monic_X_sub_C _)

lemma D_natDegree : κ.D.natDegree = κ.S.card := by
  rw [Kernel.D, natDegree_prod_of_monic _ _ (fun Q _ => monic_X_sub_C _)]
  simp [Kernel.vp]

lemma Dq_natDegree {Q : (short A B).Point} (hQ : Q ∈ κ.S) :
    (κ.Dq Q).natDegree = κ.S.card - 1 := by
  rw [Kernel.Dq, natDegree_prod_of_monic _ _ (fun Q _ => monic_X_sub_C _)]
  simp [Kernel.vp, Finset.card_erase_of_mem hQ]

/-- `N₁` is monic of degree `3n`. -/
theorem N1_monic : κ.N1.Monic ∧ κ.N1.natDegree = 3 * κ.S.card := by
  have hD3 : (κ.D ^ 3).Monic := (D_monic κ).pow 3
  have hD3d : (κ.D ^ 3).natDegree = 3 * κ.S.card := by
    rw [(D_monic κ).natDegree_pow, D_natDegree]
  have hD3deg : (κ.D ^ 3).degree = ((3 * κ.S.card : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hD3.ne_zero, hD3d]
  have hterm : ∀ Q ∈ κ.S, ((C (Kernel.tQ Q) * Kernel.vp Q + 2 * C (Kernel.uQ Q)) *
      κ.Dq Q ^ 3).degree < ((3 * κ.S.card : ℕ) : WithBot ℕ) := by
    intro Q hQ
    have hn : 1 ≤ κ.S.card := Finset.card_pos.2 ⟨Q, hQ⟩
    have h1 : (C (Kernel.tQ Q) * Kernel.vp Q + 2 * C (Kernel.uQ Q)).natDegree ≤ 1 := by
      simp only [Kernel.vp]; compute_degree
    have hDq : (κ.Dq Q).Monic := monic_prod_of_monic _ _ (fun Q _ => monic_X_sub_C _)
    have h3 : (κ.Dq Q ^ 3).natDegree = 3 * (κ.S.card - 1) := by
      rw [hDq.natDegree_pow, Dq_natDegree κ hQ]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le ((natDegree_mul_le).trans
      (Nat.add_le_add h1 h3.le))) ?_
    exact_mod_cast (show 1 + 3 * (κ.S.card - 1) < 3 * κ.S.card by omega)
  have hR : (∑ Q ∈ κ.S, (C (Kernel.tQ Q) * Kernel.vp Q + 2 * C (Kernel.uQ Q)) * κ.Dq Q ^ 3).degree <
      (κ.D ^ 3).degree := by
    rw [hD3deg]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 hterm
  refine ⟨?_, ?_⟩
  · exact hD3.sub_of_left hR
  · have := degree_sub_eq_left_of_degree_lt hR
    rw [Kernel.N1, natDegree_eq_of_degree_eq this, hD3d]

section Prod
variable {e : Fin 3 → K} (he : ∀ i, e i ^ 3 + A * e i + B = 0) (hinj : Function.Injective e)

/-- the roots `x(T_i + Q)` of `N₁`. -/
noncomputable def rr (p : Fin 3 × (short A B).Point) : K := xc (T2 h2 hΔ (he p.1) + p.2)

include hinj in
lemma rr_inj {p q : Fin 3 × (short A B).Point} (hp : p.2 ∈ κ.S) (hq : q.2 ∈ κ.S)
    (h : rr h2 hΔ he p = rr h2 hΔ he q) : p = q := by
  obtain ⟨i, Q⟩ := p
  obtain ⟨j, Q'⟩ := q
  simp only at hp hq
  simp only [rr] at h
  set T := T2 h2 hΔ (he i)
  set T' := T2 h2 hΔ (he j)
  have hT : T + T = 0 := two_T2 h2 hΔ (he i)
  have hT' : T' + T' = 0 := two_T2 h2 hΔ (he j)
  have hij : ∀ (hTT : T = T'), i = j := by
    intro hTT
    have := congrArg xc hTT
    rw [xc_T2, xc_T2] at this
    exact hinj this
  rcases Kernel.eq_or_eq_neg_of_xc_eq (add_T2_ne κ h2 hΔ (he i) (κ.S_sub hp))
    (add_T2_ne κ h2 hΔ (he j) (κ.S_sub hq)) h with e1 | e1
  · have hm : T - T' ∈ κ.G := by
      have : T - T' = Q' - Q := by
        calc T - T' = (T + Q) - Q - T' := by abel
          _ = (T' + Q') - Q - T' := by rw [e1]
          _ = Q' - Q := by abel
      rw [this]; exact sub_mem κ (κ.S_sub hq) (κ.S_sub hp)
    have h2t : (T - T') + (T - T') = 0 := by
      calc (T - T') + (T - T') = (T + T) - (T' + T') := by abel
        _ = 0 := by rw [hT, hT', sub_zero]
    have hTT : T = T' := sub_eq_zero.1 (κ.no_two_torsion _ hm h2t)
    have := hij hTT
    subst this
    have : Q = Q' := add_left_cancel e1
    rw [this]
  · have hm : T + T' ∈ κ.G := by
      have : T + T' = -Q - Q' := by
        calc T + T' = (T + Q) - Q + T' := by abel
          _ = -(T' + Q') - Q + T' := by rw [e1]
          _ = -Q - Q' := by abel
      rw [this]; exact sub_mem κ (κ.neg_mem _ (κ.S_sub hp)) (κ.S_sub hq)
    have h2t : (T + T') + (T + T') = 0 := by
      calc (T + T') + (T + T') = (T + T) + (T' + T') := by abel
        _ = 0 := by rw [hT, hT', add_zero]
    have hTT' : T + T' = 0 := κ.no_two_torsion _ hm h2t
    have hTT : T = T' := by
      calc T = T + (T' + T') := by rw [hT', add_zero]
        _ = (T + T') + T' := by abel
        _ = T' := by rw [hTT', zero_add]
    have := hij hTT
    subst this
    exfalso
    have hQ : Q = -Q' := by
      calc Q = (T + Q) - T := by abel
        _ = -(T + Q') - T := by rw [e1]
        _ = -Q' - (T + T) := by abel
        _ = -Q' := by rw [hT, sub_zero]
    exact κ.neg_not_mem_S Q' hq (hQ ▸ hp)

include hinj in
/-- **`N₁ = ∏_{i, Q} (X - x(T_i + Q))`**. -/
theorem N1_eq_prod :
    κ.N1 = ∏ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ κ.S, (X - C (rr h2 hΔ he p)) := by
  have hmon : (∏ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ κ.S, (X - C (rr h2 hΔ he p))).Monic :=
    monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  refine eq_of_monic_of_dvd_of_natDegree_le hmon (N1_monic κ).1 ?_ ?_
  · refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hp q hq hpq
      have hp2 := (Finset.mem_product.1 hp).2
      have hq2 := (Finset.mem_product.1 hq).2
      have hne : rr h2 hΔ he p ≠ rr h2 hΔ he q := fun h => hpq (rr_inj κ h2 hΔ he hinj hp2 hq2 h)
      exact pairwise_coprime_X_sub_C (s := fun x : K => x) (fun _ _ h => h) hne
    · intro p hp
      exact dvd_iff_isRoot.2 (N1_eval_add_T2 κ h2 hΔ (he p.1) (Finset.mem_product.1 hp).2)
  · rw [(N1_monic κ).2, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp [Finset.card_product]

end Prod

end Kernel'

end VeluDescent
