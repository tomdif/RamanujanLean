/-
# Newton polygon of `[p](T)/T`: classification of the root norms

Let `h = P·U` with `P = ∏ (X − rᵢ)` split of degree `N`, `‖U₀‖ = 1`, `‖U_k‖ ≤ 1`, and suppose `h` has
the coefficient shape of `[p](T)/T` (`Shape`): `‖h₀‖ = ε`, `‖h_k‖ ≤ ε` for `k < m`, `‖h_m‖ = α`,
`‖h_k‖ ≤ max ε α` for `m < k < N`, `‖h_N‖ = 1`, all `‖h_k‖ ≤ 1`.

At a radius `ρ ∈ (0,1)` lying strictly inside one of the three regions
* `α ρ^m < ε ∧ ρ^N < ε` (term `0` dominates),
* `ε < α ρ^m ∧ ρ^{N−m} < α` (term `m` dominates),
* `ε < ρ^N ∧ α < ρ^{N−m}` (term `N` dominates),
no root has norm `ρ` (`dominance_transfer` + `Newton.dominant`). Hence every root norm `x ∈ (0,1)`
is on a region boundary:
* break `ε^{N−m} < α^N`: `α x^m = ε` (canonical) or `x^{N−m} = α` (non-canonical);
* no break: `x^N = ε`.
This is the converse direction of the Newton polygon used for the quotient formal groups.
-/
import RamanujanTau.AtkinOBrien.Canonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotientHasse
open Polynomial Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The coefficient shape of `[p](T)/T`. -/
structure Shape (h : PowerSeries K) (m N : ℕ) (ε α : ℝ) : Prop where
  c0 : ‖PowerSeries.coeff 0 h‖ = ε
  lo : ∀ k < m, ‖PowerSeries.coeff k h‖ ≤ ε
  cm : ‖PowerSeries.coeff m h‖ = α
  mid : ∀ k, m < k → k < N → ‖PowerSeries.coeff k h‖ ≤ max ε α
  cN : ‖PowerSeries.coeff N h‖ = 1
  le1 : ∀ k, ‖PowerSeries.coeff k h‖ ≤ 1

variable {h : PowerSeries K} {m N : ℕ} {ε α ρ : ℝ}

lemma max_mul_pow_lt {ε α ρ c : ℝ} (k : ℕ) (hρ : 0 ≤ ρ) (h1 : ε * ρ ^ k < c) (h2 : α * ρ ^ k < c) :
    max ε α * ρ ^ k < c := by
  rw [max_mul_of_nonneg _ _ (pow_nonneg hρ k)]; exact max_lt h1 h2

/-- the term `0` dominates. -/
theorem dom0 (hS : Shape h m N ε α) (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h1 : α * ρ ^ m < ε) (h2 : ρ ^ N < ε) :
    ∀ k, k ≠ 0 → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff 0 h‖ * ρ ^ 0 := by
  intro k hk
  rw [hS.c0, pow_zero, mul_one]
  have hρk : ρ ^ k < 1 := pow_lt_one₀ hρ0.le hρ1 hk
  have hα : 0 ≤ α := hS.cm ▸ norm_nonneg _
  rcases lt_trichotomy k m with hkm | hkm | hkm
  · calc _ ≤ ε * ρ ^ k := mul_le_mul_of_nonneg_right (hS.lo k hkm) (by positivity)
      _ < ε * 1 := mul_lt_mul_of_pos_left hρk hε
      _ = ε := mul_one ε
  · rw [hkm, hS.cm]; exact h1
  · rcases lt_or_ge k N with hkN | hkN
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hS.mid k hkm hkN) (by positivity)) ?_
      refine max_mul_pow_lt k hρ0.le ?_ ?_
      · calc ε * ρ ^ k < ε * 1 := mul_lt_mul_of_pos_left hρk hε
          _ = ε := mul_one ε
      · calc α * ρ ^ k ≤ α * ρ ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le hkm.le) hα
          _ < ε := h1
    · calc _ ≤ 1 * ρ ^ k := mul_le_mul_of_nonneg_right (hS.le1 k) (by positivity)
        _ ≤ ρ ^ N := by rw [one_mul]; exact pow_le_pow_of_le_one hρ0.le hρ1.le hkN
        _ < ε := h2

/-- the term `m` dominates. -/
theorem domm (hS : Shape h m N ε α) (hmN : m < N) (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h1 : ε < α * ρ ^ m) (h2 : ρ ^ (N - m) < α) :
    ∀ k, k ≠ m → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff m h‖ * ρ ^ m := by
  intro k hk
  rw [hS.cm]
  have hα : 0 < α := lt_of_le_of_lt (by positivity) h2
  rcases lt_trichotomy k m with hkm | hkm | hkm
  · calc _ ≤ ε * 1 := mul_le_mul (hS.lo k hkm) (pow_le_one₀ hρ0.le hρ1.le) (by positivity) hε.le
      _ < _ := by rw [mul_one]; exact h1
  · exact absurd hkm hk
  · rcases lt_or_ge k N with hkN | hkN
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hS.mid k hkm hkN) (by positivity)) ?_
      refine max_mul_pow_lt k hρ0.le ?_ ?_
      · calc ε * ρ ^ k ≤ ε * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0.le hρ1.le) hε.le
          _ < _ := by rw [mul_one]; exact h1
      · exact mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hkm) hα
    · have hρN : ρ ^ N = ρ ^ m * ρ ^ (N - m) := by rw [← pow_add]; congr 1; omega
      calc _ ≤ 1 * ρ ^ N :=
            mul_le_mul (hS.le1 k) (pow_le_pow_of_le_one hρ0.le hρ1.le hkN) (by positivity) zero_le_one
        _ = ρ ^ m * ρ ^ (N - m) := by rw [one_mul, hρN]
        _ < ρ ^ m * α := mul_lt_mul_of_pos_left h2 (pow_pos hρ0 m)
        _ = α * ρ ^ m := mul_comm _ _

/-- the term `N` dominates. -/
theorem domN (hS : Shape h m N ε α) (hmN : m < N) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h1 : ε < ρ ^ N) (h2 : α < ρ ^ (N - m)) :
    ∀ k, k ≠ N → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff N h‖ * ρ ^ N := by
  intro k hk
  rw [hS.cN, one_mul]
  have hε : 0 ≤ ε := hS.c0 ▸ norm_nonneg _
  rcases lt_trichotomy k m with hkm | hkm | hkm
  · calc _ ≤ ε * 1 := mul_le_mul (hS.lo k hkm) (pow_le_one₀ hρ0.le hρ1.le) (by positivity) hε
      _ < _ := by rw [mul_one]; exact h1
  · rw [hkm, hS.cm]
    have hρN : ρ ^ N = ρ ^ (N - m) * ρ ^ m := by rw [← pow_add]; congr 1; omega
    rw [hρN]; exact mul_lt_mul_of_pos_right h2 (pow_pos hρ0 _)
  · rcases lt_or_gt_of_ne hk with hkN | hkN
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hS.mid k hkm hkN) (by positivity)) ?_
      refine max_mul_pow_lt k hρ0.le ?_ ?_
      · calc ε * ρ ^ k ≤ ε * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0.le hρ1.le) hε
          _ < _ := by rw [mul_one]; exact h1
      · have hρN : ρ ^ N = ρ ^ (N - k) * ρ ^ k := by rw [← pow_add]; congr 1; omega
        rw [hρN]
        exact mul_lt_mul_of_pos_right
          (lt_of_lt_of_le h2 (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega))) (pow_pos hρ0 _)
    · calc _ ≤ 1 * ρ ^ k := mul_le_mul_of_nonneg_right (hS.le1 k) (by positivity)
        _ < ρ ^ N := by rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hkN

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **root count at a dominant radius**: `#{‖rᵢ‖ < ρ} = j` and no root has norm `ρ`. -/
theorem root_count (r : κ → K) (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1)
    (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (X - C (r i)) : K[X]) : PowerSeries K) * U = h)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (j : ℕ) (hj : j ≤ Fintype.card κ)
    (hdom : ∀ k, k ≠ j → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff j h‖ * ρ ^ j) :
    #(univ.filter fun i => ‖r i‖ < ρ) = j ∧ ∀ i, ‖r i‖ ≠ ρ := by
  have hUlt : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k U‖ * ρ ^ k < 1 := fun k hk =>
    calc ‖PowerSeries.coeff k U‖ * ρ ^ k ≤ 1 * ρ ^ k := mul_le_mul_of_nonneg_right (hU k) (by positivity)
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  rw [← hW] at hdom
  obtain ⟨hPdom, -, -⟩ := AtkinOBrien.Canonical.dominance_transfer _ U ρ hρ0 hU0 hUlt j hdom
  obtain ⟨hc, hne, -⟩ := AtkinOBrien.Newton.dominant r ρ hρ0 j hj fun k _ hk => hPdom k hk
  exact ⟨hc, hne⟩

/-- **classification of the root norms** in `(0, 1)`. -/
theorem classify (hS : Shape h m N ε α) (hm : 0 < m) (hmN : m < N) (hε : 0 < ε)
    (hN : N = Fintype.card κ) (r : κ → K) (U : PowerSeries K)
    (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (X - C (r i)) : K[X]) : PowerSeries K) * U = h)
    (i : κ) (hi0 : 0 < ‖r i‖) (hi1 : ‖r i‖ < 1) :
    (ε ^ (N - m) < α ^ N → α * ‖r i‖ ^ m = ε ∨ ‖r i‖ ^ (N - m) = α) ∧
      (α ^ N ≤ ε ^ (N - m) → ‖r i‖ ^ N = ε) := by
  set x := ‖r i‖ with hx
  have noroot : ∀ j ≤ N, (∀ k, k ≠ j → ‖PowerSeries.coeff k h‖ * x ^ k <
      ‖PowerSeries.coeff j h‖ * x ^ j) → False :=
    fun j hj hd => (root_count r U hU0 hU hW hi0 hi1 j (hN ▸ hj) hd).2 i rfl
  have n0 : ¬ (α * x ^ m < ε ∧ x ^ N < ε) := fun ⟨a, b⟩ =>
    noroot 0 (Nat.zero_le _) (dom0 hS hε hi0 hi1 a b)
  have nm : ¬ (ε < α * x ^ m ∧ x ^ (N - m) < α) := fun ⟨a, b⟩ =>
    noroot m hmN.le (domm hS hmN hε hi0 hi1 a b)
  have nN : ¬ (ε < x ^ N ∧ α < x ^ (N - m)) := fun ⟨a, b⟩ =>
    noroot N le_rfl (domN hS hmN hi0 hi1 a b)
  have hxN : x ^ N = x ^ m * x ^ (N - m) := by rw [← pow_add]; congr 1; omega
  have hα0 : 0 ≤ α := hS.cm ▸ norm_nonneg _
  have hxm : 0 < x ^ m := pow_pos hi0 m
  constructor
  · intro hb
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · have h3 : x ^ (N - m) < α := by
        by_contra h3; push Not at h3
        have e1 : (α * x ^ m) ^ (N - m) < ε ^ (N - m) :=
          pow_lt_pow_left₀ h1 (by positivity) (by omega)
        have e2 : α ^ m ≤ (x ^ (N - m)) ^ m := pow_le_pow_left₀ hα0 h3 m
        have e3 : α ^ N = α ^ (N - m) * α ^ m := by rw [← pow_add]; congr 1; omega
        have e4 : (α * x ^ m) ^ (N - m) = α ^ (N - m) * (x ^ (N - m)) ^ m := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
        have : α ^ N ≤ (α * x ^ m) ^ (N - m) := by
          rw [e3, e4]; exact mul_le_mul_of_nonneg_left e2 (by positivity)
        linarith
      refine n0 ⟨h1, ?_⟩
      rw [hxN]
      calc x ^ m * x ^ (N - m) < x ^ m * α := mul_lt_mul_of_pos_left h3 hxm
        _ = α * x ^ m := mul_comm _ _
        _ < ε := h1
    · rcases lt_or_gt_of_ne h2 with h2 | h2
      · exact nm ⟨h1, h2⟩
      · refine nN ⟨?_, h2⟩
        rw [hxN]
        calc ε < α * x ^ m := h1
          _ = x ^ m * α := mul_comm _ _
          _ < x ^ m * x ^ (N - m) := mul_lt_mul_of_pos_left h2 hxm
  · intro hnb
    by_contra hcon
    rcases lt_or_gt_of_ne hcon with h1 | h1
    · refine n0 ⟨?_, h1⟩
      have : (α * x ^ m) ^ N < ε ^ N := by
        calc (α * x ^ m) ^ N = α ^ N * (x ^ N) ^ m := by
              rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
          _ ≤ ε ^ (N - m) * (x ^ N) ^ m := mul_le_mul_of_nonneg_right hnb (by positivity)
          _ < ε ^ (N - m) * ε ^ m :=
            mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h1 (by positivity) hm.ne') (by positivity)
          _ = ε ^ N := by rw [← pow_add]; congr 1; omega
      exact lt_of_pow_lt_pow_left₀ N hε.le this
    · refine nN ⟨h1, ?_⟩
      have : α ^ N < (x ^ (N - m)) ^ N := by
        calc α ^ N ≤ ε ^ (N - m) := hnb
          _ < (x ^ N) ^ (N - m) := pow_lt_pow_left₀ h1 hε.le (by omega)
          _ = (x ^ (N - m)) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
      exact lt_of_pow_lt_pow_left₀ N (by positivity) this

/-- the roots are nonzero (`‖h₀‖ = ε > 0`). -/
theorem roots_ne_zero (hS : Shape h m N ε α) (hε : 0 < ε) (r : κ → K) (U : PowerSeries K)
    (hW : ((∏ i, (X - C (r i)) : K[X]) : PowerSeries K) * U = h) (i : κ) : r i ≠ 0 := by
  intro hi
  have h0 : PowerSeries.coeff 0 h = (∏ i, (X - C (r i)) : K[X]).coeff 0 * PowerSeries.constantCoeff U := by
    rw [← hW, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod,
    Finset.prod_eq_zero (mem_univ i) (by simp [hi]), zero_mul] at h0
  have := hS.c0
  rw [h0, norm_zero] at this
  exact hε.ne this

/-- all roots have norm `< 1` (the term `N` dominates near radius `1`). -/
theorem roots_lt_one (hS : Shape h m N ε α) (hmN : m < N) (hε1 : ε < 1) (hα1 : α < 1)
    (hN : N = Fintype.card κ) (r : κ → K) (U : PowerSeries K)
    (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (X - C (r i)) : K[X]) : PowerSeries K) * U = h) (i : κ) : ‖r i‖ < 1 := by
  have hε : 0 ≤ ε := hS.c0 ▸ norm_nonneg _
  have hα : 0 ≤ α := hS.cm ▸ norm_nonneg _
  set b := (max ε α + 1) / 2 with hb
  have hb1 : b < 1 := by rw [hb]; have := max_lt hε1 hα1; linarith
  have hbm : max ε α < b := by rw [hb]; have := max_lt hε1 hα1; linarith
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_of_le_left hε) hbm
  have hN0 : N ≠ 0 := by omega
  set ρ := b ^ ((N : ℝ)⁻¹) with hρ
  have hρN : ρ ^ N = b := Real.rpow_inv_natCast_pow hb0.le hN0
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hb0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hb0.le hb1 (by positivity)
  have h1 : ε < ρ ^ N := by rw [hρN]; exact lt_of_le_of_lt (le_max_left _ _) hbm
  have h2 : α < ρ ^ (N - m) := by
    calc α < b := lt_of_le_of_lt (le_max_right _ _) hbm
      _ = ρ ^ N := hρN.symm
      _ ≤ ρ ^ (N - m) := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
  obtain ⟨hc, -⟩ := root_count r U hU0 hU hW hρ0 hρ1 N (hN ▸ le_rfl) (domN hS hmN hρ0 hρ1 h1 h2)
  rw [hN, ← card_univ, card_filter_eq_iff] at hc
  exact lt_trans (hc i (mem_univ i)) hρ1

/-- **existence** of a canonical and of a non-canonical root (break case). -/
theorem exists_small_big (hS : Shape h m N ε α) (hm : 0 < m) (hmN : m < N) (hε : 0 < ε)
    (hε1 : ε < 1) (hα1 : α < 1) (hN : N = Fintype.card κ) (r : κ → K) (U : PowerSeries K)
    (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (X - C (r i)) : K[X]) : PowerSeries K) * U = h)
    (hb : ε ^ (N - m) < α ^ N) :
    (∃ i, 0 < ‖r i‖ ∧ ‖r i‖ < 1 ∧ α * ‖r i‖ ^ m = ε) ∧
      (∃ i, 0 < ‖r i‖ ∧ ‖r i‖ < 1 ∧ ‖r i‖ ^ (N - m) = α) := by
  have hα : 0 ≤ α := hS.cm ▸ norm_nonneg _
  obtain ⟨ρ, hρ0, hρ1, hρm, hρd, hα0⟩ :=
    AtkinOBrien.Canonical.exists_rho m N hm hmN ε α hε hα hα1.le hb
  obtain ⟨hc, -⟩ := root_count r U hU0 hU hW hρ0 hρ1 m (hN ▸ hmN.le) (domm hS hmN hε hρ0 hρ1 hρm hρd)
  have pos : ∀ i, 0 < ‖r i‖ := fun i => norm_pos_iff.mpr (roots_ne_zero hS hε r U hW i)
  have lt1 : ∀ i, ‖r i‖ < 1 := roots_lt_one hS hmN hε1 hα1 hN r U hU0 hU hW
  have cl := fun i => classify hS hm hmN hε hN r U hU0 hU hW i (pos i) (lt1 i)
  constructor
  · obtain ⟨i, hi⟩ : (univ.filter fun i => ‖r i‖ < ρ).Nonempty := by
      rw [← card_pos, hc]; exact hm
    have hiρ : ‖r i‖ < ρ := (mem_filter.mp hi).2
    refine ⟨i, pos i, lt1 i, ?_⟩
    rcases (cl i).1 hb with h | h
    · exact h
    · exfalso
      have : ‖r i‖ ^ (N - m) < ρ ^ (N - m) := pow_lt_pow_left₀ hiρ (norm_nonneg _) (by omega)
      linarith
  · obtain ⟨i, -, hi⟩ := exists_mem_notMem_of_card_lt_card
      (s := univ.filter fun i => ‖r i‖ < ρ) (t := univ) (by rw [hc, card_univ, ← hN]; exact hmN)
    have hiρ : ρ ≤ ‖r i‖ := by
      by_contra h; exact hi (mem_filter.mpr ⟨mem_univ _, lt_of_not_ge h⟩)
    refine ⟨i, pos i, lt1 i, ?_⟩
    rcases (cl i).1 hb with h | h
    · exfalso
      have : α * ρ ^ m ≤ α * ‖r i‖ ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0.le hiρ m) hα
      linarith
    · exact h

end QuotientHasse
