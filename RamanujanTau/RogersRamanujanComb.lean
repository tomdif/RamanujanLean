/-
# The Rogers–Ramanujan identities, combinatorial form (MacMahon, Schur)

* The number of partitions of `m` whose parts differ pairwise by at least 2 equals the number of partitions of
  `m` into parts `≡ ±1 (mod 5)`.
* The number of partitions of `m` whose parts differ pairwise by at least 2 and are all `≥ 2` equals the number
  of partitions of `m` into parts `≡ ±2 (mod 5)`.

**Gap side.** A gap-2 partition is its set of parts. Let `A(m,n,t)` be the `n`-element sets with sum `m`, all
elements `≥ t+1` and no two consecutive. Splitting on whether `t+1 ∈ S` gives
`|A(m,n+1,t)| = |A(m,n+1,t+1)| + |A(m−t−1,n,t+2)|`, the recursion satisfied by `q^{(n+1)²+(n+1)t}/(q;q)_{n+1}`.
Summing over `n` gives `Σ q^{n²}/(q)_n` and `Σ q^{n²+n}/(q)_n`.
**Product side.** Mathlib's `hasProd_powerSeriesMk_card_restricted` compared with `(q^r;q⁵)_∞`.
-/
import RamanujanTau.RogersRamanujan
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

set_option autoImplicit false

namespace MockTheta5.JTP.RR
open PowerSeries Finset MockTheta5.Bailey

/-! ## sets of parts with gaps `≥ 2` -/

/-- `n`-element sets of naturals with sum `m`, elements `≥ t+1`, no two consecutive. -/
def A (m n t : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).powerset.filter fun S => S.card = n ∧ S.sum id = m ∧ (∀ i ∈ S, t + 1 ≤ i) ∧ ∀ i ∈ S, i + 1 ∉ S

lemma mem_A {m n t : ℕ} {S : Finset ℕ} :
    S ∈ A m n t ↔ S.card = n ∧ S.sum id = m ∧ (∀ i ∈ S, t + 1 ≤ i) ∧ ∀ i ∈ S, i + 1 ∉ S := by
  rw [A, mem_filter, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨fun i hi => mem_range.mpr ?_, h⟩⟩
  have := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
  rw [h.2.1] at this
  exact Nat.lt_succ_of_le this

lemma card_A_zero (m t : ℕ) : (#(A m 0 t) : ℤ) = if m = 0 then 1 else 0 := by
  have : A m 0 t = if m = 0 then {∅} else ∅ := by
    ext S
    rw [mem_A, card_eq_zero]
    split_ifs with h
    · simp only [mem_singleton]
      constructor
      · exact fun h' => h'.1
      · rintro rfl; simp [h]
    · simp only [notMem_empty, iff_false]
      rintro ⟨rfl, h2, -, -⟩; simp at h2; omega
  rw [this]; split_ifs <;> simp

lemma A_eq_empty {m n t : ℕ} (h : m ≤ t) : A m (n + 1) t = ∅ := by
  refine eq_empty_of_forall_notMem fun S hS => ?_
  rw [mem_A] at hS
  obtain ⟨hc, hs, ht, -⟩ := hS
  obtain ⟨i, hi⟩ : S.Nonempty := card_pos.mp (by omega)
  have := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
  have := ht i hi
  simp only [id] at *; omega

lemma card_A_succ {m n t : ℕ} (h : t + 1 ≤ m) :
    #(A m (n + 1) t) = #(A m (n + 1) (t + 1)) + #(A (m - (t + 1)) n (t + 2)) := by
  have hsplit : A m (n + 1) t = A m (n + 1) (t + 1) ∪ (A m (n + 1) t).filter (fun S => t + 1 ∈ S) := by
    ext S
    simp only [mem_union, mem_filter, mem_A]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases ht : t + 1 ∈ S
      · exact Or.inr ⟨⟨h1, h2, h3, h4⟩, ht⟩
      · refine Or.inl ⟨h1, h2, fun i hi => ?_, h4⟩
        have := h3 i hi
        rcases Nat.eq_or_lt_of_le this with h' | h'
        · exact absurd (h' ▸ hi) ht
        · omega
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h, -⟩)
      · exact ⟨h1, h2, fun i hi => by have := h3 i hi; omega, h4⟩
      · exact h
  have hdisj : Disjoint (A m (n + 1) (t + 1)) ((A m (n + 1) t).filter (fun S => t + 1 ∈ S)) := by
    rw [disjoint_left]
    intro S hS hS'
    rw [mem_A] at hS
    rw [mem_filter] at hS'
    have := hS.2.2.1 _ hS'.2; omega
  rw [hsplit, card_union_of_disjoint hdisj]
  congr 1
  refine card_bij' (fun S _ => S.erase (t + 1)) (fun T _ => insert (t + 1) T) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_A] at hS
    obtain ⟨⟨h1, h2, h3, h4⟩, ht⟩ := hS
    rw [mem_A]
    refine ⟨by show (S.erase (t + 1)).card = n; rw [card_erase_of_mem ht, h1]; rfl, ?_,
      fun i hi => ?_, fun i hi hi' => ?_⟩
    · show (S.erase (t + 1)).sum id = m - (t + 1)
      have := add_sum_erase S id ht
      simp only [id] at this h2 ⊢; omega
    · rw [mem_erase] at hi
      have := h3 i hi.2
      rcases (by omega : i = t + 2 ∨ t + 3 ≤ i) with rfl | h'
      · exact absurd hi.2 (h4 _ ht)
      · omega
    · exact h4 i (mem_of_mem_erase hi) (mem_of_mem_erase hi')
  · intro T hT
    rw [mem_A] at hT
    obtain ⟨h1, h2, h3, h4⟩ := hT
    have hn : t + 1 ∉ T := fun h' => by have := h3 _ h'; omega
    rw [mem_filter, mem_A]
    refine ⟨⟨by show (insert (t + 1) T).card = n + 1; rw [card_insert_of_notMem hn, h1], ?_,
      fun i hi => ?_, fun i hi hi' => ?_⟩, mem_insert_self _ _⟩
    · show (insert (t + 1) T).sum id = m
      rw [sum_insert hn, h2]; simp only [id]; omega
    · rw [mem_insert] at hi
      rcases hi with rfl | hi
      · exact le_rfl
      · have := h3 i hi; omega
    · rw [mem_insert] at hi hi'
      rcases hi with rfl | hi
      · rcases hi' with h' | h'
        · omega
        · have := h3 _ h'; omega
      · rcases hi' with h' | h'
        · have := h3 i hi; omega
        · exact h4 i hi h'
  · intro S hS
    rw [mem_filter] at hS
    exact insert_erase hS.2
  · intro T hT
    rw [mem_A] at hT
    exact erase_insert fun h' => by have := hT.2.2.1 _ h'; omega

/-! ## the generating function `q^{n²+nt}/(q;q)_n` -/

lemma inv_qfac_succ (n : ℕ) :
    Ring.inverse (qfac n) = Ring.inverse (qfac (n + 1)) * (1 - X ^ (n + 1)) := by
  apply inverse_eq_of_mul
  have hq : qfac (n + 1) = qfac n * (1 - X ^ (n + 1)) := by rw [qfac, qfac, prod_range_succ]
  rw [show qfac n * (Ring.inverse (qfac (n + 1)) * (1 - X ^ (n + 1)))
      = qfac (n + 1) * Ring.inverse (qfac (n + 1)) by rw [hq]; ring, Ring.mul_inverse_cancel _ (isUnit_qfac _)]

/-- **gap side**: `|A(m,n,t)| = [q^m] q^{n²+nt}/(q;q)_n`. -/
theorem card_A (n : ℕ) : ∀ t m, (#(A m n t) : ℤ) = coeff m (X ^ (n ^ 2 + n * t) * Ring.inverse (qfac n)) := by
  induction n with
  | zero =>
    intro t m
    rw [card_A_zero]
    simp [qfac, coeff_one]
  | succ n ih =>
    intro t m
    suffices H : ∀ k t, m ≤ t + k → (#(A m (n + 1) t) : ℤ)
        = coeff m (X ^ ((n + 1) ^ 2 + (n + 1) * t) * Ring.inverse (qfac (n + 1))) from H m t (by omega)
    intro k
    induction k with
    | zero =>
      intro t h
      rw [A_eq_empty (by omega), card_empty, coeff_X_pow_mul', if_neg (by nlinarith)]; rfl
    | succ k ihk =>
      intro t h
      by_cases hmt : m ≤ t
      · rw [A_eq_empty hmt, card_empty, coeff_X_pow_mul', if_neg (by nlinarith)]; rfl
      rw [card_A_succ (by omega), Nat.cast_add, ihk (t + 1) (by omega), ih (t + 2) (m - (t + 1))]
      have hser : X ^ ((n + 1) ^ 2 + (n + 1) * t) * Ring.inverse (qfac (n + 1))
          = X ^ ((n + 1) ^ 2 + (n + 1) * (t + 1)) * Ring.inverse (qfac (n + 1))
            + X ^ (t + 1) * (X ^ (n ^ 2 + n * (t + 2)) * Ring.inverse (qfac n)) := by
        rw [inv_qfac_succ n, ← mul_assoc, ← mul_assoc, ← pow_add,
          show t + 1 + (n ^ 2 + n * (t + 2)) = (n + 1) ^ 2 + (n + 1) * t by ring,
          show (n + 1) ^ 2 + (n + 1) * (t + 1) = (n + 1) ^ 2 + (n + 1) * t + (n + 1) by ring, pow_add]
        ring
      rw [hser, map_add]
      congr 1
      rw [coeff_X_pow_mul' (X ^ (n ^ 2 + n * (t + 2)) * Ring.inverse (qfac n)) (t + 1) m, if_pos (by omega)]


/-! ## gap-2 partitions are their sets of parts -/

/-- partitions of `m` with parts `≥ t+1` that pairwise differ by at least `2`. -/
def gapTwo (m t : ℕ) : Finset m.Partition :=
  univ.filter fun l => l.parts.Nodup ∧ (∀ i ∈ l.parts, t + 1 ≤ i) ∧ ∀ i ∈ l.parts, i + 1 ∉ l.parts

/-- the corresponding sets of parts. -/
def F (m t : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).powerset.filter fun S => S.sum id = m ∧ (∀ i ∈ S, t + 1 ≤ i) ∧ ∀ i ∈ S, i + 1 ∉ S

lemma sum_val (S : Finset ℕ) : S.val.sum = S.sum id := by
  rw [Finset.sum_eq_multiset_sum, Multiset.map_id]

lemma card_gapTwo (m t : ℕ) : #(gapTwo m t) = #(F m t) := by
  refine card_bij' (fun l _ => l.parts.toFinset)
    (fun S hS => ⟨S.val, fun {i} hi => by
        rw [F, mem_filter] at hS; have := hS.2.2.1 i hi; omega,
      by rw [F, mem_filter] at hS; rw [sum_val]; exact hS.2.1⟩) ?_ ?_ ?_ ?_
  · intro l hl
    rw [gapTwo, mem_filter] at hl
    obtain ⟨-, hnd, ht, hg⟩ := hl
    have hval : l.parts.toFinset.val = l.parts := by rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [F, mem_filter, mem_powerset]
    refine ⟨fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts (Multiset.mem_toFinset.mp hi))),
      ?_, fun i hi => ht i (Multiset.mem_toFinset.mp hi), fun i hi hi' => hg i (Multiset.mem_toFinset.mp hi)
        (Multiset.mem_toFinset.mp hi')⟩
    rw [← sum_val, hval, l.parts_sum]
  · intro S hS
    rw [F, mem_filter] at hS
    rw [gapTwo, mem_filter]
    exact ⟨mem_univ _, S.nodup, hS.2.2.1, hS.2.2.2⟩
  · intro l hl
    rw [gapTwo, mem_filter] at hl
    apply Nat.Partition.ext
    show l.parts.toFinset.val = l.parts
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hl.2.1]
  · intro S hS
    exact Finset.val_toFinset S

lemma card_F (m t : ℕ) : #(F m t) = ∑ n ∈ range (m + 2), #(A m n t) := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (m + 2)) fun S hS => by
    rw [mem_coe, F, mem_filter, mem_powerset] at hS
    have := card_le_card hS.1
    rw [card_range] at this
    exact mem_coe.mpr (mem_range.mpr (by omega))]
  refine sum_congr rfl fun n _ => congrArg _ ?_
  ext S
  rw [mem_filter, mem_A, F, mem_filter, ← mem_A.trans (Iff.rfl), mem_A]
  constructor
  · rintro ⟨⟨-, h1, h2, h3⟩, h4⟩; exact ⟨h4, h1, h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩
    refine ⟨⟨?_, h1, h2, h3⟩, h4⟩
    have : S ∈ A m n t := mem_A.mpr ⟨h4, h1, h2, h3⟩
    rw [A, mem_filter] at this
    exact this.1

/-- `#gap-2 partitions of m` with parts `≥ 1` is `[q^m] Σ q^{n²}/(q;q)_n`. -/
lemma card_gapTwo_zero (m : ℕ) :
    (#(gapTwo m 0) : ℤ) = coeff m (tsumQsq fun n => Ring.inverse (qfac n)) := by
  rw [card_gapTwo, card_F, coeff_tsumQsq _ (show m + 1 ≤ m + 2 by omega), Nat.cast_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [card_A n 0 m, mul_zero, add_zero]

/-- `#gap-2 partitions of m` with parts `≥ 2` is `[q^m] Σ q^{n²+n}/(q;q)_n`. -/
lemma card_gapTwo_one (m : ℕ) :
    (#(gapTwo m 1) : ℤ) = coeff m (tsumQsqQ fun n => Ring.inverse (qfac n)) := by
  rw [card_gapTwo, card_F, coeff_tsumQsqQ _ (show m + 1 ≤ m + 2 by omega), Nat.cast_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [card_A n 1 m, mul_one]


/-! ## the product side: partitions into restricted parts -/

section Product
open Filter Topology
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pinf_sub)
open scoped PowerSeries.WithPiTopology

/-- the factor `1 − q^{i+1}` if `p(i+1)`, else `1`. -/
noncomputable def gfac (p : ℕ → Prop) [DecidablePred p] (i : ℕ) : PowerSeries ℤ :=
  if p (i + 1) then 1 - X ^ (i + 1) else 1

lemma multipliable_gfac (p : ℕ → Prop) [DecidablePred p] : Multipliable (gfac p) := by
  have h : gfac p = fun i => 1 + (if p (i + 1) then -X ^ (i + 1) else 0 : PowerSeries ℤ) := by
    funext i; rw [gfac]; split_ifs <;> ring
  rw [h]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  split_ifs
  · rw [order_neg, order_X_pow]; norm_cast; omega
  · rw [order_zero]; exact WithTop.coe_lt_top _

/-- if the blocks of five factors are `(1 − q^{r₁+5M})(1 − q^{r₂+5M})`, then `∏ gfac = (q^{r₁};q⁵)(q^{r₂};q⁵)`,
and the restricted-partition generating function is its inverse. -/
lemma restricted_mul_eq_one (p : ℕ → Prop) [DecidablePred p] {r₁ r₂ : ℕ} (h₁ : 1 ≤ r₁) (h₂ : 1 ≤ r₂)
    (hblock : ∀ M, ∏ i ∈ range (5 * M), gfac p i = Pfin r₁ 5 M * Pfin r₂ 5 M) :
    PowerSeries.mk (fun n => (#(Nat.Partition.restricted n p) : ℤ)) * (Pinf r₁ 5 * Pinf r₂ 5) = 1 := by
  have hm := multipliable_gfac p
  have htend : Tendsto (fun M => ∏ i ∈ range (5 * M), gfac p i) atTop (𝓝 (Pinf r₁ 5 * Pinf r₂ 5)) := by
    simp_rw [hblock]
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    refine tendsto_atTop_of_eventually_const (i₀ := d) fun M hM => ?_
    have h1 := X_pow_dvd_Pinf_sub r₁ 5 h₁ (by norm_num) M
    have h2 := X_pow_dvd_Pinf_sub r₂ 5 h₂ (by norm_num) M
    have h3 : (X : PowerSeries ℤ) ^ (M + 1) ∣ Pfin r₁ 5 M * Pfin r₂ 5 M - Pinf r₁ 5 * Pinf r₂ 5 := by
      rw [show Pfin r₁ 5 M * Pfin r₂ 5 M - Pinf r₁ 5 * Pinf r₂ 5
          = -((Pinf r₁ 5 - Pfin r₁ 5 M) * Pinf r₂ 5 + Pfin r₁ 5 M * (Pinf r₂ 5 - Pfin r₂ 5 M)) by ring]
      exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _))
    exact coeff_eq_of_dvd h3 (by omega)
  have hseq : Tendsto (fun M => ∏ i ∈ range (5 * M), gfac p i) atTop (𝓝 (∏' i, gfac p i)) :=
    hm.hasProd.tendsto_prod_nat.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 5))
  have htprod : ∏' i, gfac p i = Pinf r₁ 5 * Pinf r₂ 5 := tendsto_nhds_unique hseq htend
  have hf := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ p
  have hmul := hf.mul hm.hasProd
  have hone : (fun i => (if p (i + 1) then ∑' j : ℕ, (X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) * gfac p i)
      = fun _ => 1 := by
    funext i
    rw [gfac]
    split_ifs
    · have hcc : (X ^ (i + 1) : PowerSeries ℤ).constantCoeff = 0 := by rw [map_pow]; simp
      simp_rw [pow_mul]
      exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hcc
    · rw [one_mul]
  rw [hone, htprod] at hmul
  exact (hasProd_one.unique hmul).symm

lemma coeff_inv_eq_card (p : ℕ → Prop) [DecidablePred p] {r₁ r₂ : ℕ} (h₁ : 1 ≤ r₁) (h₂ : 1 ≤ r₂)
    (hblock : ∀ M, ∏ i ∈ range (5 * M), gfac p i = Pfin r₁ 5 M * Pfin r₂ 5 M) (m : ℕ) :
    coeff m (Ring.inverse (Pinf r₁ 5 * Pinf r₂ 5)) = #(Nat.Partition.restricted m p) := by
  rw [inverse_eq_of_mul (by rw [mul_comm]; exact restricted_mul_eq_one p h₁ h₂ hblock), coeff_mk]

lemma block14 (M : ℕ) : ∏ i ∈ range (5 * M), gfac (fun i => i % 5 = 1 ∨ i % 5 = 4) i = Pfin 1 5 M * Pfin 4 5 M := by
  induction M with
  | zero => simp [Pfin]
  | succ M ih =>
    rw [show 5 * (M + 1) = 5 * M + 5 by ring, prod_range_add, ih, Pfin_succ, Pfin_succ]
    simp only [prod_range_succ, prod_range_zero, one_mul, gfac]
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    ring_nf

lemma block23 (M : ℕ) : ∏ i ∈ range (5 * M), gfac (fun i => i % 5 = 2 ∨ i % 5 = 3) i = Pfin 2 5 M * Pfin 3 5 M := by
  induction M with
  | zero => simp [Pfin]
  | succ M ih =>
    rw [show 5 * (M + 1) = 5 * M + 5 by ring, prod_range_add, ih, Pfin_succ, Pfin_succ]
    simp only [prod_range_succ, prod_range_zero, one_mul, gfac]
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    ring_nf

end Product

/-- **The first Rogers–Ramanujan identity, combinatorial form**: the partitions of `m` whose parts differ
pairwise by at least 2 are equinumerous with the partitions of `m` into parts `≡ ±1 (mod 5)`. -/
theorem rogers_ramanujan_1_comb (m : ℕ) :
    #(gapTwo m 0) = #(Nat.Partition.restricted m fun i => i % 5 = 1 ∨ i % 5 = 4) := by
  have h := card_gapTwo_zero m
  rw [rogers_ramanujan_1, coeff_inv_eq_card _ le_rfl (by norm_num) block14] at h
  exact_mod_cast h

/-- **The second Rogers–Ramanujan identity, combinatorial form**: the partitions of `m` into parts `≥ 2` that
differ pairwise by at least 2 are equinumerous with the partitions of `m` into parts `≡ ±2 (mod 5)`. -/
theorem rogers_ramanujan_2_comb (m : ℕ) :
    #(gapTwo m 1) = #(Nat.Partition.restricted m fun i => i % 5 = 2 ∨ i % 5 = 3) := by
  have h := card_gapTwo_one m
  rw [rogers_ramanujan_2, coeff_inv_eq_card _ (by norm_num) (by norm_num) block23] at h
  exact_mod_cast h

end MockTheta5.JTP.RR
