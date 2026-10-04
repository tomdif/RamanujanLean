/-
# The Göllnitz–Gordon theorem (combinatorial form)

The number of partitions of `m` into parts `≡ 1, 4, 7 (mod 8)` equals the number of partitions of `m` into
distinct parts that differ by at least 2, with even parts differing by at least 4.

**Gap side.** Let `A(m,n,s)` be the `n`-element sets of parts `≥ 2s+1` with sum `m` satisfying the gap conditions.
According to whether `2s+1`, `2s+2`, or neither is a part (an even part `2s+2` excludes `2s+3` and `2s+4`),
`|A(m,n+1,s)| = |A(m,n+1,s+1)| + |A(m−2s−1,n,s+1)| + |A(m−2s−2,n,s+2)|`. This is the recursion of
`q^{n²+2sn}(−q;q²)_n/(q²;q²)_n`.
-/
import RamanujanTau.GollnitzGordon
import RamanujanTau.GollnitzGordon2
import RamanujanTau.RogersRamanujanComb

set_option autoImplicit false

namespace GG
open PowerSeries Finset MockTheta5.JTP

/-- the Göllnitz–Gordon gap condition on a set of parts. -/
def GGgap (S : Finset ℕ) : Prop := ∀ i ∈ S, i + 1 ∉ S ∧ (i % 2 = 0 → i + 2 ∉ S)

instance (S : Finset ℕ) : Decidable (GGgap S) := by unfold GGgap; infer_instance

/-- `n`-element gap sets with sum `m` and parts `≥ 2s+1`. -/
def AG (m n s : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).powerset.filter fun S => S.card = n ∧ S.sum id = m ∧ (∀ i ∈ S, 2 * s + 1 ≤ i) ∧ GGgap S

lemma mem_AG {m n s : ℕ} {S : Finset ℕ} :
    S ∈ AG m n s ↔ S.card = n ∧ S.sum id = m ∧ (∀ i ∈ S, 2 * s + 1 ≤ i) ∧ GGgap S := by
  rw [AG, mem_filter, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨fun i hi => mem_range.mpr ?_, h⟩⟩
  have := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
  rw [h.2.1] at this
  exact Nat.lt_succ_of_le this

lemma card_AG_zero (m s : ℕ) : (#(AG m 0 s) : ℤ) = if m = 0 then 1 else 0 := by
  have : AG m 0 s = if m = 0 then {∅} else ∅ := by
    ext S
    rw [mem_AG, card_eq_zero]
    split_ifs with h
    · simp only [mem_singleton]
      constructor
      · exact fun h' => h'.1
      · rintro rfl; simp [h, GGgap]
    · simp only [notMem_empty, iff_false]
      rintro ⟨rfl, h2, -, -⟩; simp at h2; omega
  rw [this]; split_ifs <;> simp

lemma AG_eq_empty {m n s : ℕ} (h : m ≤ 2 * s) : AG m (n + 1) s = ∅ := by
  refine eq_empty_of_forall_notMem fun S hS => ?_
  rw [mem_AG] at hS
  obtain ⟨hc, hs, ht, -⟩ := hS
  obtain ⟨i, hi⟩ : S.Nonempty := card_pos.mp (by omega)
  have := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
  have := ht i hi
  simp only [id] at *; omega

/-- the three-way split of `A(m,n+1,s)`. -/
lemma card_AG_succ {m n s : ℕ} :
    #(AG m (n + 1) s) = #(AG m (n + 1) (s + 1)) + #((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∈ S))
      + #((AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S)) := by
  have h1 : AG m (n + 1) s = (AG m (n + 1) s).filter (fun S => 2 * s + 1 ∉ S ∧ 2 * s + 2 ∉ S)
      ∪ ((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∈ S) ∪ (AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S)) := by
    ext S; simp only [mem_union, mem_filter]; tauto
  have hd1 : Disjoint ((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∈ S)) ((AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S)) := by
    rw [disjoint_left]
    intro S hS hS'
    rw [mem_filter, mem_AG] at hS hS'
    exact (hS.1.2.2.2 _ hS.2).1 hS'.2
  have hd2 : Disjoint ((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∉ S ∧ 2 * s + 2 ∉ S))
      ((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∈ S) ∪ (AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S)) := by
    rw [disjoint_left]
    intro S hS hS'
    rw [mem_filter] at hS
    rw [mem_union, mem_filter, mem_filter] at hS'
    rcases hS' with h | h
    · exact hS.2.1 h.2
    · exact hS.2.2 h.2
  have h3 : (AG m (n + 1) s).filter (fun S => 2 * s + 1 ∉ S ∧ 2 * s + 2 ∉ S) = AG m (n + 1) (s + 1) := by
    ext S
    simp only [mem_filter, mem_AG]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
      refine ⟨h1, h2, fun i hi => ?_, h4⟩
      have := h3 i hi
      rcases (by omega : i = 2 * s + 1 ∨ i = 2 * s + 2 ∨ 2 * (s + 1) + 1 ≤ i) with rfl | rfl | h'
      · exact absurd hi h5
      · exact absurd hi h6
      · exact h'
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, fun i hi => by have := h3 i hi; omega, h4⟩, fun h => by have := h3 _ h; omega,
        fun h => by have := h3 _ h; omega⟩
  conv_lhs => rw [h1]
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, h3]
  ring

lemma card_odd_case {m n s : ℕ} (h : 2 * s + 1 ≤ m) :
    #((AG m (n + 1) s).filter (fun S => 2 * s + 1 ∈ S)) = #(AG (m - (2 * s + 1)) n (s + 1)) := by
  refine card_bij' (fun S _ => S.erase (2 * s + 1)) (fun T _ => insert (2 * s + 1) T) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_AG] at hS
    obtain ⟨⟨h1, h2, h3, h4⟩, ht⟩ := hS
    rw [mem_AG]
    refine ⟨by show (S.erase _).card = n; rw [card_erase_of_mem ht, h1]; rfl, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · show (S.erase _).sum id = _
      have := add_sum_erase S id ht
      simp only [id] at this h2 ⊢; omega
    · rw [mem_erase] at hi
      have := h3 i hi.2
      rcases (by omega : i = 2 * s + 2 ∨ 2 * (s + 1) + 1 ≤ i) with rfl | h'
      · exact absurd hi.2 (h4 _ ht).1
      · exact h'
    · have hi' := mem_of_mem_erase hi
      exact ⟨fun h' => (h4 i hi').1 (mem_of_mem_erase h'), fun he h' => (h4 i hi').2 he (mem_of_mem_erase h')⟩
  · intro T hT
    rw [mem_AG] at hT
    obtain ⟨h1, h2, h3, h4⟩ := hT
    have hn : 2 * s + 1 ∉ T := fun h' => by have := h3 _ h'; omega
    rw [mem_filter, mem_AG]
    refine ⟨⟨by show (insert _ T).card = n + 1; rw [card_insert_of_notMem hn, h1], ?_, fun i hi => ?_,
      fun i hi => ?_⟩, mem_insert_self _ _⟩
    · show (insert _ T).sum id = m
      rw [sum_insert hn, h2]; simp only [id]; omega
    · rw [mem_insert] at hi
      rcases hi with rfl | hi
      · exact le_rfl
      · have := h3 i hi; omega
    · rw [mem_insert] at hi
      rcases hi with rfl | hi
      · refine ⟨fun h' => ?_, fun he => by omega⟩
        rw [mem_insert] at h'
        rcases h' with h' | h'
        · omega
        · have := h3 _ h'; omega
      · refine ⟨fun h' => ?_, fun he h' => ?_⟩
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · have := h3 i hi; omega
          · exact (h4 i hi).1 h'
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · have := h3 i hi; omega
          · exact (h4 i hi).2 he h'
  · intro S hS
    rw [mem_filter] at hS
    exact insert_erase hS.2
  · intro T hT
    rw [mem_AG] at hT
    exact erase_insert fun h' => by have := hT.2.2.1 _ h'; omega

lemma card_even_case {m n s : ℕ} (h : 2 * s + 2 ≤ m) :
    #((AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S)) = #(AG (m - (2 * s + 2)) n (s + 2)) := by
  refine card_bij' (fun S _ => S.erase (2 * s + 2)) (fun T _ => insert (2 * s + 2) T) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_AG] at hS
    obtain ⟨⟨h1, h2, h3, h4⟩, ht⟩ := hS
    rw [mem_AG]
    refine ⟨by show (S.erase _).card = n; rw [card_erase_of_mem ht, h1]; rfl, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · show (S.erase _).sum id = _
      have := add_sum_erase S id ht
      simp only [id] at this h2 ⊢; omega
    · rw [mem_erase] at hi
      have := h3 i hi.2
      rcases (by omega : i = 2 * s + 1 ∨ i = 2 * s + 3 ∨ i = 2 * s + 4 ∨ 2 * (s + 2) + 1 ≤ i) with rfl | rfl | rfl | h'
      · exact absurd ht (h4 _ hi.2).1
      · exact absurd hi.2 (h4 _ ht).1
      · exact absurd hi.2 ((h4 _ ht).2 (by omega))
      · exact h'
    · have hi' := mem_of_mem_erase hi
      exact ⟨fun h' => (h4 i hi').1 (mem_of_mem_erase h'), fun he h' => (h4 i hi').2 he (mem_of_mem_erase h')⟩
  · intro T hT
    rw [mem_AG] at hT
    obtain ⟨h1, h2, h3, h4⟩ := hT
    have hn : 2 * s + 2 ∉ T := fun h' => by have := h3 _ h'; omega
    rw [mem_filter, mem_AG]
    refine ⟨⟨by show (insert _ T).card = n + 1; rw [card_insert_of_notMem hn, h1], ?_, fun i hi => ?_,
      fun i hi => ?_⟩, mem_insert_self _ _⟩
    · show (insert _ T).sum id = m
      rw [sum_insert hn, h2]; simp only [id]; omega
    · rw [mem_insert] at hi
      rcases hi with rfl | hi
      · omega
      · have := h3 i hi; omega
    · rw [mem_insert] at hi
      rcases hi with rfl | hi
      · refine ⟨fun h' => ?_, fun _ h' => ?_⟩
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · omega
          · have := h3 _ h'; omega
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · omega
          · have := h3 _ h'; omega
      · refine ⟨fun h' => ?_, fun he h' => ?_⟩
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · have := h3 i hi; omega
          · exact (h4 i hi).1 h'
        · rw [mem_insert] at h'
          rcases h' with h' | h'
          · have := h3 i hi; omega
          · exact (h4 i hi).2 he h'
  · intro S hS
    rw [mem_filter] at hS
    exact insert_erase hS.2
  · intro T hT
    rw [mem_AG] at hT
    exact erase_insert fun h' => by have := hT.2.2.1 _ h'; omega


/-! ## the generating function -/

lemma card_AG (n : ℕ) : ∀ s m, (#(AG m n s) : ℤ) = coeff m (X ^ (n ^ 2 + 2 * s * n) * Mq n * Ring.inverse (Qf n)) := by
  induction n with
  | zero =>
    intro s m
    rw [card_AG_zero]
    simp [Mq, Qf, coeff_one]
  | succ n ih =>
    intro s m
    suffices H : ∀ k s, m ≤ 2 * s + k → (#(AG m (n + 1) s) : ℤ)
        = coeff m (X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) * Mq (n + 1) * Ring.inverse (Qf (n + 1))) from H m s (by omega)
    intro k
    have hzero : ∀ s, m ≤ 2 * s → (#(AG m (n + 1) s) : ℤ)
        = coeff m (X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) * Mq (n + 1) * Ring.inverse (Qf (n + 1))) := fun s h => by
      rw [AG_eq_empty h, card_empty, mul_assoc, coeff_X_pow_mul', if_neg (by nlinarith)]; rfl
    induction k with
    | zero => intro s h; exact hzero s (by omega)
    | succ k ihk =>
      intro s h
      by_cases hms : m ≤ 2 * s
      · exact hzero s hms
      have hinv : Ring.inverse (Qf n) = Ring.inverse (Qf (n + 1)) * (1 - X ^ (2 * n + 2)) := by
        apply MockTheta5.JTP.RR.inverse_eq_of_mul
        rw [show Qf n * (Ring.inverse (Qf (n + 1)) * (1 - X ^ (2 * n + 2)))
            = Qf (n + 1) * Ring.inverse (Qf (n + 1)) by rw [Qf_succ]; ring, Ring.mul_inverse_cancel _ (isUnit_Qf _)]
      have hser : X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) * Mq (n + 1) * Ring.inverse (Qf (n + 1))
          = X ^ ((n + 1) ^ 2 + 2 * (s + 1) * (n + 1)) * Mq (n + 1) * Ring.inverse (Qf (n + 1))
            + X ^ (2 * s + 1) * (X ^ (n ^ 2 + 2 * (s + 1) * n) * Mq n * Ring.inverse (Qf n))
            + X ^ (2 * s + 2) * (X ^ (n ^ 2 + 2 * (s + 2) * n) * Mq n * Ring.inverse (Qf n)) := by
        have h1 : (X : PowerSeries ℤ) ^ ((n + 1) ^ 2 + 2 * (s + 1) * (n + 1))
            = X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) * X ^ (2 * n + 2) := by rw [← pow_add]; congr 1; ring
        have h2 : (X : PowerSeries ℤ) ^ (2 * s + 1) * X ^ (n ^ 2 + 2 * (s + 1) * n)
            = X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) := by rw [← pow_add]; congr 1; ring
        have h3 : (X : PowerSeries ℤ) ^ (2 * s + 2) * X ^ (n ^ 2 + 2 * (s + 2) * n)
            = X ^ ((n + 1) ^ 2 + 2 * s * (n + 1)) * X ^ (2 * n + 1) := by rw [← pow_add, ← pow_add]; congr 1; ring
        rw [hinv, Mq_succ, h1]
        linear_combination (-(Mq n * Ring.inverse (Qf (n + 1)) * (1 - X ^ (2 * n + 2)))) * h2
          + (-(Mq n * Ring.inverse (Qf (n + 1)) * (1 - X ^ (2 * n + 2)))) * h3
      rw [card_AG_succ, Nat.cast_add, Nat.cast_add, ihk (s + 1) (by omega), card_odd_case (by omega),
        ih (s + 1) (m - (2 * s + 1)), hser, map_add, map_add,
        coeff_X_pow_mul' (X ^ (n ^ 2 + 2 * (s + 1) * n) * Mq n * Ring.inverse (Qf n)) (2 * s + 1) m,
        if_pos (by omega)]
      congr 1
      by_cases h2 : 2 * s + 2 ≤ m
      · rw [card_even_case h2, ih (s + 2) (m - (2 * s + 2)),
          coeff_X_pow_mul' (X ^ (n ^ 2 + 2 * (s + 2) * n) * Mq n * Ring.inverse (Qf n)) (2 * s + 2) m, if_pos h2]
      · rw [coeff_X_pow_mul' (X ^ (n ^ 2 + 2 * (s + 2) * n) * Mq n * Ring.inverse (Qf n)) (2 * s + 2) m, if_neg h2]
        have : (AG m (n + 1) s).filter (fun S => 2 * s + 2 ∈ S) = ∅ := by
          refine eq_empty_of_forall_notMem fun S hS => ?_
          rw [mem_filter, mem_AG] at hS
          have := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hS.2
          rw [hS.1.2.1] at this
          simp only [id] at this; omega
        rw [this, card_empty, Nat.cast_zero]


/-! ## partitions -/

/-- partitions of `m` into distinct parts differing by `≥ 2`, even parts by `≥ 4`. -/
def gapGG (m : ℕ) : Finset m.Partition :=
  univ.filter fun l => l.parts.Nodup ∧ ∀ i ∈ l.parts, i + 1 ∉ l.parts ∧ (i % 2 = 0 → i + 2 ∉ l.parts)

def FG (m : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).powerset.filter fun S => S.sum id = m ∧ (∀ i ∈ S, 1 ≤ i) ∧ GGgap S

lemma card_gapGG (m : ℕ) : #(gapGG m) = #(FG m) := by
  refine card_bij' (fun l _ => l.parts.toFinset)
    (fun S hS => ⟨S.val, fun {i} hi => by
        rw [FG, mem_filter] at hS; have := hS.2.2.1 i hi; omega,
      by rw [FG, mem_filter] at hS; rw [MockTheta5.JTP.RR.sum_val]; exact hS.2.1⟩) ?_ ?_ ?_ ?_
  · intro l hl
    rw [gapGG, mem_filter] at hl
    obtain ⟨-, hnd, hg⟩ := hl
    have hval : l.parts.toFinset.val = l.parts := by rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [FG, mem_filter, mem_powerset]
    refine ⟨fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts (Multiset.mem_toFinset.mp hi))),
      ?_, fun i hi => l.parts_pos (Multiset.mem_toFinset.mp hi), fun i hi => ⟨fun h' => (hg i
        (Multiset.mem_toFinset.mp hi)).1 (Multiset.mem_toFinset.mp h'),
        fun he h' => (hg i (Multiset.mem_toFinset.mp hi)).2 he (Multiset.mem_toFinset.mp h')⟩⟩
    rw [← MockTheta5.JTP.RR.sum_val, hval, l.parts_sum]
  · intro S hS
    rw [FG, mem_filter] at hS
    rw [gapGG, mem_filter]
    exact ⟨mem_univ _, S.nodup, fun i hi => hS.2.2.2 i hi⟩
  · intro l hl
    rw [gapGG, mem_filter] at hl
    apply Nat.Partition.ext
    show l.parts.toFinset.val = l.parts
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hl.2.1]
  · intro S hS
    exact Finset.val_toFinset S

lemma card_FG (m : ℕ) : #(FG m) = ∑ n ∈ range (m + 2), #(AG m n 0) := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (m + 2)) fun S hS => by
    rw [mem_coe, FG, mem_filter, mem_powerset] at hS
    have := card_le_card hS.1
    rw [card_range] at this
    exact mem_coe.mpr (mem_range.mpr (by omega))]
  refine sum_congr rfl fun n _ => congrArg _ ?_
  ext S
  rw [mem_filter, mem_AG, FG, mem_filter]
  constructor
  · rintro ⟨⟨-, h1, h2, h3⟩, h4⟩; exact ⟨h4, h1, by simpa using h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩
    refine ⟨⟨?_, h1, by simpa using h2, h3⟩, h4⟩
    have : S ∈ AG m n 0 := mem_AG.mpr ⟨h4, h1, h2, h3⟩
    rw [AG, mem_filter] at this
    exact this.1

lemma card_gapGG_eq (m : ℕ) : (#(gapGG m) : ℤ) = coeff m (tsumQsq fun n => Mq n * Ring.inverse (Qf n)) := by
  rw [card_gapGG, card_FG, coeff_tsumQsq _ (show m + 1 ≤ m + 2 by omega), Nat.cast_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [card_AG n 0 m, mul_zero, zero_mul, add_zero, mul_assoc]

/-! ## the product side, for a general modulus and residue set -/

section Product
open Filter Topology MockTheta5.JTP.RR
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pinf_sub)
open scoped PowerSeries.WithPiTopology

lemma restricted_mul_eq_one_gen (p : ℕ → Prop) [DecidablePred p] (a : ℕ) (ha : 1 ≤ a) (R : Finset ℕ)
    (hR : ∀ r ∈ R, 1 ≤ r)
    (hblock : ∀ M, ∏ i ∈ range (a * M), gfac p i = ∏ r ∈ R, Pfin r a M) :
    PowerSeries.mk (fun n => (#(Nat.Partition.restricted n p) : ℤ)) * ∏ r ∈ R, Pinf r a = 1 := by
  have hm := multipliable_gfac p
  have htend : Tendsto (fun M => ∏ i ∈ range (a * M), gfac p i) atTop (𝓝 (∏ r ∈ R, Pinf r a)) := by
    simp_rw [hblock]
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    refine tendsto_atTop_of_eventually_const (i₀ := d) fun M hM => ?_
    have h3 : (X : PowerSeries ℤ) ^ (M + 1) ∣ ∏ r ∈ R, Pinf r a - ∏ r ∈ R, Pfin r a M :=
      dvd_sub_prod' _ _ fun r hr => X_pow_dvd_Pinf_sub r a (hR r hr) ha M
    exact (coeff_eq_of_dvd h3 (by omega)).symm
  have hseq : Tendsto (fun M => ∏ i ∈ range (a * M), gfac p i) atTop (𝓝 (∏' i, gfac p i)) :=
    hm.hasProd.tendsto_prod_nat.comp (tendsto_id.const_mul_atTop' (by omega : 0 < a))
  have htprod : ∏' i, gfac p i = ∏ r ∈ R, Pinf r a := tendsto_nhds_unique hseq htend
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

lemma block147 (M : ℕ) : ∏ i ∈ range (8 * M), gfac (fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7) i
    = ∏ r ∈ ({1, 4, 7} : Finset ℕ), Pfin r 8 M := by
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton]
  induction M with
  | zero => simp [Pfin]
  | succ M ih =>
    rw [show 8 * (M + 1) = 8 * M + 8 by ring, prod_range_add, ih, Pfin_succ, Pfin_succ, Pfin_succ]
    simp only [prod_range_succ, prod_range_zero, one_mul, gfac]
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    ring_nf

end Product

/-- **The Göllnitz–Gordon theorem**: the partitions of `m` into distinct parts differing by at least 2, with even
parts differing by at least 4, are equinumerous with the partitions of `m` into parts `≡ 1, 4, 7 (mod 8)`. -/
theorem gollnitz_gordon_comb (m : ℕ) :
    #(gapGG m) = #(Nat.Partition.restricted m fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7) := by
  have h := card_gapGG_eq m
  have hG := gollnitz_gordon_1
  have hR := restricted_mul_eq_one_gen (fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7) 8 (by norm_num)
    {1, 4, 7} (by decide) block147
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton, ← mul_assoc] at hR
  have heq : tsumQsq (fun n => Mq n * Ring.inverse (Qf n))
      = PowerSeries.mk (fun n => (#(Nat.Partition.restricted n fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7) : ℤ)) := by
    have e1 := MockTheta5.JTP.RR.inverse_eq_of_mul (by rw [mul_comm]; exact hG)
    have e2 := MockTheta5.JTP.RR.inverse_eq_of_mul (show RankProof.Pinf 1 8 * RankProof.Pinf 4 8 * RankProof.Pinf 7 8
      * PowerSeries.mk (fun n => (#(Nat.Partition.restricted n fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7) : ℤ)) = 1 by
        rw [← hR]; ring)
    rw [← e1, e2]
  rw [heq, coeff_mk] at h
  exact_mod_cast h


/-! ## the second identity: parts `≥ 3` -/

/-- gap partitions with all parts `≥ 3`. -/
def gapGG3 (m : ℕ) : Finset m.Partition :=
  univ.filter fun l => l.parts.Nodup ∧ (∀ i ∈ l.parts, 3 ≤ i) ∧
    ∀ i ∈ l.parts, i + 1 ∉ l.parts ∧ (i % 2 = 0 → i + 2 ∉ l.parts)

def FG3 (m : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).powerset.filter fun S => S.sum id = m ∧ (∀ i ∈ S, 2 * 1 + 1 ≤ i) ∧ GGgap S

lemma card_gapGG3 (m : ℕ) : #(gapGG3 m) = #(FG3 m) := by
  refine card_bij' (fun l _ => l.parts.toFinset)
    (fun S hS => ⟨S.val, fun {i} hi => by
        rw [FG3, mem_filter] at hS; have := hS.2.2.1 i hi; omega,
      by rw [FG3, mem_filter] at hS; rw [MockTheta5.JTP.RR.sum_val]; exact hS.2.1⟩) ?_ ?_ ?_ ?_
  · intro l hl
    rw [gapGG3, mem_filter] at hl
    obtain ⟨-, hnd, h3, hg⟩ := hl
    have hval : l.parts.toFinset.val = l.parts := by rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [FG3, mem_filter, mem_powerset]
    refine ⟨fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts (Multiset.mem_toFinset.mp hi))),
      ?_, fun i hi => h3 i (Multiset.mem_toFinset.mp hi), fun i hi => ⟨fun h' => (hg i
        (Multiset.mem_toFinset.mp hi)).1 (Multiset.mem_toFinset.mp h'),
        fun he h' => (hg i (Multiset.mem_toFinset.mp hi)).2 he (Multiset.mem_toFinset.mp h')⟩⟩
    rw [← MockTheta5.JTP.RR.sum_val, hval, l.parts_sum]
  · intro S hS
    rw [FG3, mem_filter] at hS
    rw [gapGG3, mem_filter]
    exact ⟨mem_univ _, S.nodup, hS.2.2.1, fun i hi => hS.2.2.2 i hi⟩
  · intro l hl
    rw [gapGG3, mem_filter] at hl
    apply Nat.Partition.ext
    show l.parts.toFinset.val = l.parts
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hl.2.1]
  · intro S hS
    exact Finset.val_toFinset S

lemma card_FG3 (m : ℕ) : #(FG3 m) = ∑ n ∈ range (m + 2), #(AG m n 1) := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (m + 2)) fun S hS => by
    rw [mem_coe, FG3, mem_filter, mem_powerset] at hS
    have := card_le_card hS.1
    rw [card_range] at this
    exact mem_coe.mpr (mem_range.mpr (by omega))]
  refine sum_congr rfl fun n _ => congrArg _ ?_
  ext S
  rw [mem_filter, mem_AG, FG3, mem_filter]
  constructor
  · rintro ⟨⟨-, h1, h2, h3⟩, h4⟩; exact ⟨h4, h1, h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩
    refine ⟨⟨?_, h1, h2, h3⟩, h4⟩
    have : S ∈ AG m n 1 := mem_AG.mpr ⟨h4, h1, h2, h3⟩
    rw [AG, mem_filter] at this
    exact this.1

lemma card_gapGG3_eq (m : ℕ) :
    (#(gapGG3 m) : ℤ) = coeff m (tsumQsq fun n => X ^ (2 * n) * (Mq n * Ring.inverse (Qf n))) := by
  rw [card_gapGG3, card_FG3, coeff_tsumQsq _ (show m + 1 ≤ m + 2 by omega), Nat.cast_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [card_AG n 1 m, mul_one, pow_add]
  ring_nf

section Product2
open MockTheta5.JTP.RR
open RankProof (Pinf Pfin Pfin_succ)

lemma block345 (M : ℕ) : ∏ i ∈ range (8 * M), gfac (fun i => i % 8 = 3 ∨ i % 8 = 4 ∨ i % 8 = 5) i
    = ∏ r ∈ ({3, 4, 5} : Finset ℕ), Pfin r 8 M := by
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton]
  induction M with
  | zero => simp [Pfin]
  | succ M ih =>
    rw [show 8 * (M + 1) = 8 * M + 8 by ring, prod_range_add, ih, Pfin_succ, Pfin_succ, Pfin_succ]
    simp only [prod_range_succ, prod_range_zero, one_mul, gfac]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring_nf

end Product2

/-- **The second Göllnitz–Gordon theorem**: the partitions of `m` into distinct parts `≥ 3` differing by at least 2,
with even parts differing by at least 4, are equinumerous with the partitions of `m` into parts `≡ 3, 4, 5 (mod 8)`. -/
theorem gollnitz_gordon_comb_2 (m : ℕ) :
    #(gapGG3 m) = #(Nat.Partition.restricted m fun i => i % 8 = 3 ∨ i % 8 = 4 ∨ i % 8 = 5) := by
  have h := card_gapGG3_eq m
  have hG := gollnitz_gordon_2
  have hR := restricted_mul_eq_one_gen (fun i => i % 8 = 3 ∨ i % 8 = 4 ∨ i % 8 = 5) 8 (by norm_num)
    {3, 4, 5} (by decide) block345
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton] at hR
  have heq : tsumQsq (fun n => X ^ (2 * n) * (Mq n * Ring.inverse (Qf n)))
      = PowerSeries.mk (fun n => (#(Nat.Partition.restricted n fun i => i % 8 = 3 ∨ i % 8 = 4 ∨ i % 8 = 5) : ℤ)) := by
    have e1 := MockTheta5.JTP.RR.inverse_eq_of_mul (by rw [mul_comm]; exact hG)
    have e2 := MockTheta5.JTP.RR.inverse_eq_of_mul (show RankProof.Pinf 3 8 * RankProof.Pinf 4 8 * RankProof.Pinf 5 8
      * PowerSeries.mk (fun n => (#(Nat.Partition.restricted n fun i => i % 8 = 3 ∨ i % 8 = 4 ∨ i % 8 = 5) : ℤ)) = 1 by
        rw [← hR]; ring)
    rw [← e1, e2]
  rw [heq, coeff_mk] at h
  exact_mod_cast h

end GG
