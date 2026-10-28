/-
# Newton polygons over a non-archimedean field: the dominant-term root count

Let `K` be a normed field with ultrametric norm, and `f = ∏_{i} (X − rᵢ)` a split monic polynomial of
degree `N`. If at radius `ρ > 0` the term `‖c_m‖ ρ^m` strictly dominates every other `‖c_j‖ ρ^j`, then
* exactly `m` roots have `‖rᵢ‖ < ρ`, and no root has `‖rᵢ‖ = ρ`;
* `‖c₀‖ = ‖c_m‖ · ∏_{‖rᵢ‖<ρ} ‖rᵢ‖`.

This is the root-valuation step of Katz 3.10.7 (Lubin). Applied to `[p](T)/T` it gives the `p − 1` nonzero
points of the canonical subgroup with product valuation `1 − v` (`canonical_count` below).

Proof (no sorting). Put `wᵢ = max ‖rᵢ‖ ρ` and `M = ∏ wᵢ`. Every Vieta term of `c_j ρ^j` is at most `M`. At
`j = #{‖r‖ < ρ}` and at `j = #{‖r‖ ≤ ρ}` exactly one term equals `M` and the others are smaller. So the
maximum `M` is attained at both, and dominance forces both counts to equal `m`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrien.Newton
open Polynomial Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the `k`-th coefficient of `∏ (X − rᵢ)` (Vieta). -/
lemma coeff_prod (r : ι → K) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (∏ i, (X - C (r i))).coeff k =
      ∑ t ∈ (univ : Finset ι).powersetCard (Fintype.card ι - k), ∏ i ∈ t, (-r i) := by
  have := Finset.prod_X_add_C_coeff (univ : Finset ι) (fun i => -r i) (k := k) (by simpa using hk)
  simp only [map_neg, ← sub_eq_add_neg, card_univ] at this
  exact this

/-- strict ultrametric: a unique strictly-largest term determines the norm of a sum. -/
lemma norm_sum_eq_of_unique_max {α : Type*} [DecidableEq α] (S : Finset α) (a : α → K) (t₀ : α)
    (h₀ : t₀ ∈ S) (hpos : 0 < ‖a t₀‖) (hlt : ∀ t ∈ S, t ≠ t₀ → ‖a t‖ < ‖a t₀‖) :
    ‖∑ t ∈ S, a t‖ = ‖a t₀‖ := by
  rw [← Finset.add_sum_erase S a h₀]
  have hrest : ‖∑ t ∈ S.erase t₀, a t‖ < ‖a t₀‖ := by
    rcases (S.erase t₀).eq_empty_or_nonempty with he | hne
    · rw [he, sum_empty, norm_zero]; exact hpos
    · obtain ⟨t, ht, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne a
      exact lt_of_le_of_lt hle (hlt t (mem_of_mem_erase ht) (ne_of_mem_erase ht))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]

variable (r : ι → K) (ρ : ℝ)

/-- the weight `M = ∏ max ‖rᵢ‖ ρ`. -/
noncomputable def M : ℝ := ∏ i, max ‖r i‖ ρ

lemma M_pos (hρ : 0 < ρ) : 0 < M r ρ :=
  prod_pos fun i _ => lt_of_lt_of_le hρ (le_max_right _ _)

/-- a Vieta term, scaled by `ρ^k`, written as a product over all indices. -/
lemma term_eq (t : Finset ι) {k : ℕ} (ht : #t = Fintype.card ι - k) (hk : k ≤ Fintype.card ι) :
    ‖∏ i ∈ t, (-r i)‖ * ρ ^ k = ∏ i, (if i ∈ t then ‖r i‖ else ρ) := by
  rw [norm_prod, prod_ite, Finset.filter_mem_eq_inter, univ_inter, prod_const]
  simp only [norm_neg]
  congr 2
  have : #(univ.filter fun i => i ∉ t) = Fintype.card ι - #t := by
    rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _), card_univ]
  rw [this, ht]; omega

lemma term_le (hρ : 0 < ρ) (t : Finset ι) {k : ℕ} (ht : #t = Fintype.card ι - k)
    (hk : k ≤ Fintype.card ι) : ‖∏ i ∈ t, (-r i)‖ * ρ ^ k ≤ M r ρ := by
  rw [term_eq r ρ t ht hk, M]
  refine prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · split_ifs <;> [exact norm_nonneg _; exact hρ.le]
  · split_ifs <;> [exact le_max_left _ _; exact le_max_right _ _]

/-- strict version: if some factor is strictly below its weight. -/
lemma term_lt (hρ : 0 < ρ) (t : Finset ι) {k : ℕ} (ht : #t = Fintype.card ι - k)
    (hk : k ≤ Fintype.card ι) (i₀ : ι)
    (hi₀ : (if i₀ ∈ t then ‖r i₀‖ else ρ) < max ‖r i₀‖ ρ) :
    ‖∏ i ∈ t, (-r i)‖ * ρ ^ k < M r ρ := by
  rw [term_eq r ρ t ht hk, M, ← mul_prod_erase univ _ (mem_univ i₀), ← mul_prod_erase univ _ (mem_univ i₀)]
  have hle : ∏ i ∈ univ.erase i₀, (if i ∈ t then ‖r i‖ else ρ) ≤ ∏ i ∈ univ.erase i₀, max ‖r i‖ ρ := by
    refine prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
    · split_ifs <;> [exact norm_nonneg _; exact hρ.le]
    · split_ifs <;> [exact le_max_left _ _; exact le_max_right _ _]
  have hpos : 0 < ∏ i ∈ univ.erase i₀, max ‖r i‖ ρ :=
    prod_pos fun i _ => lt_of_lt_of_le hρ (le_max_right _ _)
  have h0 : 0 ≤ (if i₀ ∈ t then ‖r i₀‖ else ρ) := by split_ifs <;> [exact norm_nonneg _; exact hρ.le]
  calc _ ≤ (if i₀ ∈ t then ‖r i₀‖ else ρ) * ∏ i ∈ univ.erase i₀, max ‖r i‖ ρ :=
        mul_le_mul_of_nonneg_left hle h0
    _ < _ := mul_lt_mul_of_pos_right hi₀ hpos

/-- every scaled coefficient is at most `M`. -/
lemma coeff_le (hρ : 0 < ρ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ‖(∏ i, (X - C (r i))).coeff k‖ * ρ ^ k ≤ M r ρ := by
  rw [coeff_prod r hk]
  rcases ((univ : Finset ι).powersetCard (Fintype.card ι - k)).eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty, norm_zero, zero_mul]; exact (M_pos r ρ hρ).le
  · obtain ⟨t, ht, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun t => ∏ i ∈ t, (-r i))
    have hcard := (mem_powersetCard.mp ht).2
    exact le_trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hρ.le _)) (term_le r ρ hρ t hcard hk)

/-- **attained**: if the top set `{P}` has the right size and every other set of that size loses a
factor, the scaled coefficient equals `M`. -/
lemma coeff_eq_M (hρ : 0 < ρ) (P : ι → Prop) [DecidablePred P]
    (hPi : ∀ i, P i → max ‖r i‖ ρ = ‖r i‖) (hnP : ∀ i, ¬ P i → max ‖r i‖ ρ = ρ)
    (k : ℕ) (hk : k + #(univ.filter P) = Fintype.card ι)
    (hsep : ∀ t ∈ (univ : Finset ι).powersetCard (Fintype.card ι - k), t ≠ univ.filter P →
      ∃ i₀, (if i₀ ∈ t then ‖r i₀‖ else ρ) < max ‖r i₀‖ ρ) :
    ‖(∏ i, (X - C (r i))).coeff k‖ * ρ ^ k = M r ρ := by
  have hkN : k ≤ Fintype.card ι := by omega
  have hcardP : #(univ.filter P) = Fintype.card ι - k := by omega
  have hmem : univ.filter P ∈ (univ : Finset ι).powersetCard (Fintype.card ι - k) :=
    mem_powersetCard.mpr ⟨subset_univ _, hcardP⟩
  have hM : ‖∏ i ∈ univ.filter P, (-r i)‖ * ρ ^ k = M r ρ := by
    rw [term_eq r ρ _ hcardP hkN, M]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : P i
    · rw [if_pos (by simpa using h), hPi i h]
    · rw [if_neg (by simpa using h), hnP i h]
  rw [coeff_prod r hkN, ← hM, mul_left_inj' (pow_pos hρ k).ne']
  refine norm_sum_eq_of_unique_max _ _ _ hmem ?_ fun t ht hne => ?_
  · have := M_pos r ρ hρ
    rw [← hM] at this
    exact pos_of_mul_pos_left this (pow_nonneg hρ.le _)
  · obtain ⟨i₀, hi₀⟩ := hsep t ht hne
    have := term_lt r ρ hρ t (mem_powersetCard.mp ht).2 hkN i₀ hi₀
    rw [← hM] at this
    exact lt_of_mul_lt_mul_right this (pow_nonneg hρ.le _)

lemma split_lt : #(univ.filter fun i => ‖r i‖ < ρ) + #(univ.filter fun i => ρ ≤ ‖r i‖) = Fintype.card ι := by
  have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset ι)) (fun i => ‖r i‖ < ρ)
  simp only [not_lt, card_univ] at this; exact this

lemma split_le : #(univ.filter fun i => ‖r i‖ ≤ ρ) + #(univ.filter fun i => ρ < ‖r i‖) = Fintype.card ι := by
  have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset ι)) (fun i => ‖r i‖ ≤ ρ)
  simp only [not_le, card_univ] at this; exact this

/-- **Newton dominant-term theorem.** -/
theorem dominant (hρ : 0 < ρ) (m : ℕ) (hm : m ≤ Fintype.card ι)
    (hdom : ∀ j ≤ Fintype.card ι, j ≠ m →
      ‖(∏ i, (X - C (r i))).coeff j‖ * ρ ^ j < ‖(∏ i, (X - C (r i))).coeff m‖ * ρ ^ m) :
    #(univ.filter fun i => ‖r i‖ < ρ) = m ∧ (∀ i, ‖r i‖ ≠ ρ) ∧
      ‖(∏ i, (X - C (r i))).coeff 0‖ =
        ‖(∏ i, (X - C (r i))).coeff m‖ * ∏ i ∈ univ.filter (fun i => ‖r i‖ < ρ), ‖r i‖ := by
  set f := ∏ i, (X - C (r i)) with hf
  have hMm := coeff_le r ρ hρ hm
  -- the count `k₀ = #{‖r‖ < ρ}`: top set `{ρ ≤ ‖r‖}`
  set k₀ := #(univ.filter fun i => ‖r i‖ < ρ) with hk₀
  have hk₀N : k₀ ≤ Fintype.card ι := card_le_univ _
  have e₀ : ‖f.coeff k₀‖ * ρ ^ k₀ = M r ρ := by
    refine coeff_eq_M r ρ hρ (fun i => ρ ≤ ‖r i‖) (fun i h => max_eq_left h)
      (fun i h => max_eq_right (le_of_lt (lt_of_not_ge h))) k₀ (split_lt r ρ) fun t ht hne => ?_
    have hcard : #t = #(univ.filter fun i => ρ ≤ ‖r i‖) := by
      have := split_lt r ρ; rw [(mem_powersetCard.mp ht).2]; omega
    obtain ⟨i, hit, hi⟩ : ∃ i ∈ t, ¬ ρ ≤ ‖r i‖ := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hne (eq_of_subset_of_card_le (fun i hi => by simpa using hcon i hi) hcard.ge)
    refine ⟨i, ?_⟩
    rw [if_pos hit, max_eq_right (lt_of_not_ge hi).le]; exact lt_of_not_ge hi
  -- the count `l₀ = #{‖r‖ ≤ ρ}`: top set `{ρ < ‖r‖}`
  set l₀ := #(univ.filter fun i => ‖r i‖ ≤ ρ) with hl₀
  have hl₀N : l₀ ≤ Fintype.card ι := card_le_univ _
  have e₁ : ‖f.coeff l₀‖ * ρ ^ l₀ = M r ρ := by
    refine coeff_eq_M r ρ hρ (fun i => ρ < ‖r i‖) (fun i h => max_eq_left h.le)
      (fun i h => max_eq_right (le_of_not_gt h)) l₀ (split_le r ρ) fun t ht hne => ?_
    have hcard : #t = #(univ.filter fun i => ρ < ‖r i‖) := by
      have := split_le r ρ; rw [(mem_powersetCard.mp ht).2]; omega
    obtain ⟨i, hi, hit⟩ : ∃ i, ρ < ‖r i‖ ∧ i ∉ t := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hne (eq_of_subset_of_card_le (fun i hi => hcon i (by simpa using hi)) hcard.le).symm
    refine ⟨i, ?_⟩
    rw [if_neg hit, max_eq_left hi.le]; exact hi
  have hk : k₀ = m := by
    by_contra h
    have := hdom k₀ hk₀N h
    linarith
  have hl : l₀ = m := by
    by_contra h
    have := hdom l₀ hl₀N h
    linarith
  have hnoeq : ∀ i, ‖r i‖ ≠ ρ := by
    intro i hi
    have hsub : univ.filter (fun i => ‖r i‖ < ρ) ⊂ univ.filter (fun i => ‖r i‖ ≤ ρ) := by
      refine ⟨fun j hj => by simp at hj ⊢; exact hj.le, fun hsub => ?_⟩
      have := hsub (show i ∈ univ.filter (fun i => ‖r i‖ ≤ ρ) by simp [hi])
      simp [hi] at this
    have := card_lt_card hsub
    rw [← hk₀, ← hl₀, hk, hl] at this
    exact lt_irrefl _ this
  refine ⟨hk, hnoeq, ?_⟩
  -- `‖c_m‖ ρ^m = M = ρ^m ∏_{‖r‖>ρ} ‖r‖` and `‖c₀‖ = ∏ ‖r‖`
  have hc0 : ‖f.coeff 0‖ = ∏ i, ‖r i‖ := by
    rw [hf, coeff_prod r (Nat.zero_le _), Nat.sub_zero, ← card_univ, powersetCard_self, sum_singleton, norm_prod]
    simp
  have hMsplit : M r ρ = ρ ^ m * ∏ i ∈ univ.filter (fun i => ¬ ‖r i‖ < ρ), ‖r i‖ := by
    rw [M, ← prod_filter_mul_prod_filter_not univ (fun i => ‖r i‖ < ρ)]
    congr 1
    · rw [← hk, hk₀, ← prod_const]
      exact prod_congr rfl fun i hi => max_eq_right (by simp at hi; exact hi.le)
    · exact prod_congr rfl fun i hi => max_eq_left (by simp at hi; exact hi)
  have hcm : ‖f.coeff m‖ = ∏ i ∈ univ.filter (fun i => ¬ ‖r i‖ < ρ), ‖r i‖ := by
    have h := e₀
    rw [hk, hMsplit, mul_comm (ρ ^ m)] at h
    exact mul_right_cancel₀ (pow_pos hρ m).ne' h
  rw [hc0, hcm, mul_comm, prod_filter_mul_prod_filter_not]

lemma coeff_top : (∏ i, (X - C (r i))).coeff (Fintype.card ι) = 1 := by
  rw [coeff_prod r le_rfl, Nat.sub_self, powersetCard_zero, sum_singleton, prod_empty]

/-- **two-segment Newton polygon** (the shape of `[p](T)/T` in Katz 3.10.7). Let `f = ∏(X − rᵢ)` have
degree `N`, `0 < m < N`, `‖c₀‖ = ε > 0`, `‖c_m‖ = α ≤ 1`, `‖c_j‖ ≤ ε` for `j < m` and `‖c_j‖ ≤ α` for
`m < j < N`. If the break condition `ε^{N−m} < α^N` holds, then exactly `m` roots are "small"
(`‖rᵢ‖ < ρ` for a suitable `ρ`) and their norms multiply to `ε/α`.
For `[p](T)/T` take `N = p²−1`, `m = p−1`, `ε = |p|`, `α = |p|^v`. Then the condition is `v < p/(p+1)`
(`I2Val.newton_break`), and the small roots are the nonzero points of the canonical subgroup, with
product valuation `1 − v`. -/
theorem two_segment (m : ℕ) (hm0 : 0 < m) (hmN : m < Fintype.card ι) (ε α : ℝ) (hε : 0 < ε) (hα1 : α ≤ 1)
    (hc0 : ‖(∏ i, (X - C (r i))).coeff 0‖ = ε) (hcm : ‖(∏ i, (X - C (r i))).coeff m‖ = α)
    (hlo : ∀ j < m, ‖(∏ i, (X - C (r i))).coeff j‖ ≤ ε)
    (hhi : ∀ j, m < j → j < Fintype.card ι → ‖(∏ i, (X - C (r i))).coeff j‖ ≤ α)
    (hbreak : ε ^ (Fintype.card ι - m) < α ^ Fintype.card ι) :
    ∃ ρ : ℝ, 0 < ρ ∧ #(univ.filter fun i => ‖r i‖ < ρ) = m ∧ (∀ i, ‖r i‖ ≠ ρ) ∧
      α * ∏ i ∈ univ.filter (fun i => ‖r i‖ < ρ), ‖r i‖ = ε := by
  set N := Fintype.card ι
  set d := N - m with hd
  have hd0 : 0 < d := by omega
  have hα0 : 0 < α := by
    by_contra h; push_neg at h
    have : α ^ N ≤ 0 := by
      rcases eq_or_lt_of_le h with h | h
      · rw [h, zero_pow (by omega)]
      · exact absurd (hcm ▸ norm_nonneg _) (not_le.mpr h)
    linarith [pow_pos hε d]
  set L := (ε / α) ^ ((1 : ℝ) / m)
  set U := α ^ ((1 : ℝ) / d)
  have hL0 : 0 ≤ L := Real.rpow_nonneg (div_pos hε hα0).le _
  have hLm : L ^ m = ε / α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hε hα0).le]
    rw [one_div_mul_cancel (by exact_mod_cast hm0.ne'), Real.rpow_one]
  have hUd : U ^ d = α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hα0.le]
    rw [one_div_mul_cancel (by exact_mod_cast hd0.ne'), Real.rpow_one]
  have hU1 : U ≤ 1 := Real.rpow_le_one hα0.le hα1 (by positivity)
  have hLU : L < U := by
    by_contra h; push_neg at h
    have h1 : U ^ (m * d) ≤ L ^ (m * d) := pow_le_pow_left₀ (Real.rpow_nonneg hα0.le _) h _
    have hU' : U ^ (m * d) = α ^ m := by rw [mul_comm, pow_mul, hUd]
    have hL' : L ^ (m * d) = ε ^ d / α ^ d := by rw [pow_mul, hLm, div_pow]
    rw [hU', hL'] at h1
    -- `α^m ≤ ε^d / α^d` contradicts `ε^d < α^N = α^m α^d`
    have hN : α ^ N = α ^ m * α ^ d := by rw [← pow_add]; congr 1; omega
    rw [le_div_iff₀ (pow_pos hα0 d), ← hN] at h1
    linarith
  set ρ := (L + U) / 2
  have hρ0 : 0 < ρ := by
    have : 0 < U := Real.rpow_pos_of_pos hα0 _
    positivity
  have hρL : L < ρ := by rw [show ρ = (L + U) / 2 from rfl]; linarith
  have hρU : ρ < U := by rw [show ρ = (L + U) / 2 from rfl]; linarith
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρU hU1
  have hρm : ε < α * ρ ^ m := by
    have : ε / α < ρ ^ m := hLm ▸ pow_lt_pow_left₀ hρL hL0 hm0.ne'
    rwa [div_lt_iff₀ hα0, mul_comm] at this
  have hρd : ρ ^ d < α := hUd ▸ pow_lt_pow_left₀ hρU hρ0.le hd0.ne'
  obtain ⟨hcount, hne, hprod⟩ := dominant r ρ hρ0 m hmN.le fun j hjN hjm => by
    rw [hcm]
    rcases lt_trichotomy j m with hj | hj | hj
    · calc ‖(∏ i, (X - C (r i))).coeff j‖ * ρ ^ j ≤ ε * 1 :=
            mul_le_mul (hlo j hj) (pow_le_one₀ hρ0.le hρ1.le) (pow_nonneg hρ0.le _) hε.le
        _ < α * ρ ^ m := by rw [mul_one]; exact hρm
    · exact absurd hj hjm
    · rcases lt_or_eq_of_le hjN with hjN | rfl
      · calc ‖(∏ i, (X - C (r i))).coeff j‖ * ρ ^ j ≤ α * ρ ^ j :=
              mul_le_mul_of_nonneg_right (hhi j hj hjN) (pow_nonneg hρ0.le _)
          _ < α * ρ ^ m := mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hj) hα0
      · rw [coeff_top, norm_one, one_mul]
        have : ρ ^ N = ρ ^ m * ρ ^ d := by rw [← pow_add]; congr 1; omega
        rw [this, mul_comm α]
        exact mul_lt_mul_of_pos_left hρd (pow_pos hρ0 m)
  exact ⟨ρ, hρ0, hcount, hne, by rw [← hcm, ← hprod, hc0]⟩

end AtkinOBrien.Newton
