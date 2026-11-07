import RamanujanTau.MultiQuintupleFourWitness2521Data

/-! A delayed four-factor witness beyond the quarter-prime cutoff. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] quadBox quintBranchBox tripleQuintBranchBox

private lemma short_index2521 (b : Bool) (i : ℕ) (n : ℤ)
    (hi : i=35 ∨ i=36 ∨ i=71 ∨ i=1) (he : quintExp2 b 2521 i n ≤ 3191090) :
    n.natAbs ≤ 20 := by
  have hn : -20 ≤ n ∧ n ≤ 20 := by
    rcases hi with rfl | rfl | rfl | rfl <;> cases b <;>
      norm_num [quintExp2,quintExpA2,quintExpB2] at he <;>
      constructor <;> by_contra h <;>
      have hside : n ≤ -21 ∨ 21 ≤ n := by omega
    all_goals rcases hside with hside | hside <;>
      nlinarith [sq_nonneg (n+21),sq_nonneg (n-21)]
  omega

private lemma mem_short_box2521 (K : ℕ) (hK : K ≤ 1595545) (x : QuadQuintBranchIndex)
    (he : quadExp2 2521 35 36 71 1 x = 2*(K : ℤ)) : x ∈ quadBox 19 := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2,pointTripleExp2,tripleQuintExp2,pointB1,pointB2,pointB3,
    pointN1,pointN2,pointN3,quadB4,quadN4] at he
  have h1 := quintExp2_nonneg b1 2521 35 n1 (by norm_num) (by norm_num)
  have h2 := quintExp2_nonneg b2 2521 36 n2 (by norm_num) (by norm_num)
  have h3 := quintExp2_nonneg b3 2521 71 n3 (by norm_num) (by norm_num)
  have h4 := quintExp2_nonneg b4 2521 1 n4 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he h1 h2 h3 h4
  have hn1 := short_index2521 b1 35 n1 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn2 := short_index2521 b2 36 n2 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn3 := short_index2521 b3 71 n3 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  have hn4 := short_index2521 b4 1 n4 (by simp) (by norm_num only [Nat.cast_ofNat]; omega)
  unfold quadBox
  apply Finset.mem_product.mpr
  constructor
  · unfold tripleQuintBranchBox
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨mem_quintBranchBox_of_natAbs_le 19 b1 n1 hn1,
        mem_quintBranchBox_of_natAbs_le 19 b2 n2 hn2⟩
    · exact mem_quintBranchBox_of_natAbs_le 19 b3 n3 hn3
  · exact mem_quintBranchBox_of_natAbs_le 19 b4 n4 hn4

private lemma witness2521_centered (v z : ℤ) (h : (v-z)%2521=0)
    (hl : -60 ≤ z) (hu : z ≤ 61) : (v+60)%2521-60=z := by omega

lemma witness2521_complete_eq (N : ℕ) (hN : N ≤ 632) (x : QuadQuintBranchIndex)
    (he : quadExp2 2521 35 36 71 1 x=2*((2521*N+2273 : ℕ) : ℤ)) :
    witness2521Complete x.1=x := by
  have hb := mem_short_box2521 (2521*N+2273) (by omega) x he
  rw [quadBox] at hb
  have hn4 : -20 ≤ x.2.2 ∧ x.2.2 ≤ 20 := by
    simpa [quintBranchBox,quintBranchInterval] using (Finset.mem_product.mp hb).2
  have heq := quadExp2_energy 2521 35 36 71 1 x
  rw [he] at heq
  have hz := congrArg (fun t : ℤ => (t : ZMod 2521)) heq
  simp [fourEnergy,fourDot,fourSum,quadZ] at hz
  have hd : (2273-35*branchZ x.1.1.1-36*branchZ x.1.1.2-
      71*branchZ x.1.2-branchZ x.2) % 2521=0 := by
    apply Int.emod_eq_zero_of_dvd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2521).mp
    push_cast
    linear_combination (norm := ring_nf) 2101*hz
    all_goals reduce_mod_char
  rcases x with ⟨y,⟨b,n⟩⟩
  change -20 ≤ n ∧ n ≤ 20 at hn4
  have hez : (2273-35*branchZ y.1.1-36*branchZ y.1.2-71*branchZ y.2+60)%2521-60=
      branchZ (b,n) := by
    apply witness2521_centered _ _ hd
    · cases b <;> simp [branchZ] <;> omega
    · cases b <;> simp [branchZ] <;> omega
  simp only [witness2521Complete,hez]
  cases b <;> simp [branchZ,Int.add_emod] <;> omega

private lemma witness2521_branch_injective : Function.Injective witness2521Branch := by
  intro a b h
  have hn := congrArg Prod.snd h
  have hb := congrArg Prod.fst h
  simp only [witness2521Branch,Prod.mk.injEq] at h
  simp only [witness2521Branch] at hn hb
  apply Fin.ext
  have ha : a.val%2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : b.val%2 < 2 := Nat.mod_lt _ (by norm_num)
  have hp : (a.val%2==1)=true ↔ (b.val%2==1)=true := by rw [hb]
  simp only [beq_iff_eq] at hp
  omega

private lemma witness2521_branch_image :
    (Finset.univ.image witness2521Branch)=quintBranchBox 19 := by
  decide +kernel

private lemma witness2521_sum_branch (f : QuintBranchIndex → ℤ) :
    (∑ x ∈ quintBranchBox 19, f x)=∑ a : Fin 82, f (witness2521Branch a) := by
  rw [← witness2521_branch_image,Finset.sum_image]
  exact witness2521_branch_injective.injOn

lemma coeff_four2521_eq_completed (N : ℕ) (hN : N ≤ 632) :
    coeff (2521*N+2273) (quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 *
      quintupleSpecialized 2521 71 * quintupleSpecialized 2521 1) =
      ∑ a : Fin 82, ∑ b : Fin 82, ∑ c : Fin 82,
        quadContribution 2521 35 36 71 1 (2521*N+2273)
          (witness2521Complete ((witness2521Branch a,witness2521Branch b),witness2521Branch c)) := by
  let K := 2521*N+2273
  have hK : K ≤ 1595545 := by dsimp [K]; omega
  have hex (x : QuadQuintBranchIndex) (hn : quadContribution 2521 35 36 71 1 K x ≠ 0) :
      quadExp2 2521 35 36 71 1 x=2*(K : ℤ) := by
    by_contra he
    simp [quadContribution,he] at hn
  rw [coeff_quad_eq_finiteBox 2521 35 36 71 1 _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  change (∑ x ∈ quadBox K, quadContribution 2521 35 36 71 1 K x)=_
  have hshort : (∑ x ∈ quadBox K, quadContribution 2521 35 36 71 1 K x)=
      ∑ x ∈ quadBox 19, quadContribution 2521 35 36 71 1 K x := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro x hx hnx
      by_contra hn
      exact hnx (mem_short_box2521 K hK x (hex x hn))
    · intro x hx hnx
      by_contra hn
      exact hnx (mem_quadBox_of_exp 2521 35 36 71 1 K x
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (hex x hn))
    · intro x hx hy; rfl
  rw [hshort,sum_quadBox]
  have hlast (a b c : QuintBranchIndex) :
      (∑ d ∈ quintBranchBox 19, quadContribution 2521 35 36 71 1 K (((a,b),c),d))=
        quadContribution 2521 35 36 71 1 K (witness2521Complete ((a,b),c)) := by
    apply Finset.sum_eq_single (witness2521Complete ((a,b),c)).2
    · intro d hd hne
      by_contra hn
      have hh := witness2521_complete_eq N hN (((a,b),c),d) (hex _ hn)
      exact hne (congrArg Prod.snd hh).symm
    · intro hnot
      by_contra hn
      have hb := mem_short_box2521 K hK (witness2521Complete ((a,b),c)) (hex _ hn)
      rw [quadBox] at hb
      exact hnot (Finset.mem_product.mp hb).2
  simp_rw [hlast,witness2521_sum_branch]
  rfl

private lemma witness2521_sum_flatMap {α β : Type} (xs : List α)
    (f : α → List β) (g : β → ℤ) :
    ((xs.flatMap f).map g).sum=(xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,List.sum_append]

private lemma witness2521_sum_finRange {n : ℕ} (f : Fin n → ℤ) :
    ((List.finRange n).map f).sum=∑ a, f a := by
  rw [← List.ofFn_eq_map,List.sum_ofFn]

lemma witness2521_entries_eval (N : ℕ) (hN : N ≤ 632) :
    (witness2521Entries.map fun x => if x.1=2*((2521*N+2273 : ℕ) : ℤ) then x.2 else 0).sum=
      coeff (2521*N+2273) (quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 *
        quintupleSpecialized 2521 71 * quintupleSpecialized 2521 1) := by
  rw [coeff_four2521_eq_completed N hN]
  simp only [witness2521Entries,witness2521Slice,witness2521_sum_flatMap,witness2521_sum_finRange]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  let x := witness2521Complete ((witness2521Branch a,witness2521Branch b),witness2521Branch c)
  change ((if quadExp2 2521 35 36 71 1 x ≤ 3191090 ∧
      quadExp2 2521 35 36 71 1 x % 5042=4546 then
        [(quadExp2 2521 35 36 71 1 x,quadWeight x)] else []).map _).sum=_
  by_cases he : quadExp2 2521 35 36 71 1 x=2*((2521*N+2273 : ℕ) : ℤ)
  · have hle : quadExp2 2521 35 36 71 1 x ≤ 3191090 := by omega
    have hm : quadExp2 2521 35 36 71 1 x % 5042=4546 := by omega
    rw [if_pos ⟨hle,hm⟩]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,quadContribution,he,ite_true,add_zero]
    change quadWeight x=(if quadExp2 2521 35 36 71 1 x=2*((2521*N+2273 : ℕ) : ℤ) then quadWeight x else 0)
    rw [if_pos he]
  · simp only [quadContribution]
    split_ifs <;> simp_all

private lemma quadWeight_one_or_neg_one (x : QuadQuintBranchIndex) :
    quadWeight x=1 ∨ quadWeight x= -1 := by
  rcases x with ⟨⟨⟨⟨a,na⟩,⟨b,nb⟩⟩,⟨c,nc⟩⟩,⟨d,nd⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [quadWeight,pointBranchWeight,pointB1,pointB2,pointB3,quadB4,branchSign]

private lemma witness2521_entries_weight :
    ∀ x ∈ witness2521Entries, x.2=1 ∨ x.2= -1 := by
  intro x hx
  simp only [witness2521Entries,witness2521Slice,List.mem_flatMap] at hx
  obtain ⟨a,ha,b,hb,c,hc,hx⟩ := hx
  dsimp [witness2521Entry] at hx
  split_ifs at hx with h
  · simp only [List.mem_singleton] at hx
    subst x
    exact quadWeight_one_or_neg_one _
  · simp at hx

private lemma witness2521_split (xs : List (ℤ × ℤ))
    (hw : ∀ x ∈ xs, x.2=1 ∨ x.2= -1) (K : ℤ) :
    (xs.map fun x => if x.1=K then x.2 else 0).sum=
      ((xs.filterMap fun x => if x.2=1 then some x.1 else none).map
        fun e => if e=K then (1 : ℤ) else 0).sum-
      ((xs.filterMap fun x => if x.2= -1 then some x.1 else none).map
        fun e => if e=K then (1 : ℤ) else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    rcases hh with hh | hh <;> by_cases he : x.1=K <;>
      simp [hh,he,ht] <;> ring

private lemma witness2521_balance_eval
    (hp : witness2521Positive.Perm (3191090 :: witness2521Negative)) (K : ℤ) :
    (witness2521Entries.map fun x => if x.1=K then x.2 else 0).sum=
      if 3191090=K then 1 else 0 := by
  have hh := (hp.map (fun e => if e=K then (1 : ℤ) else 0)).sum_eq
  simp only [List.map_cons,List.sum_cons] at hh
  rw [witness2521_split witness2521Entries witness2521_entries_weight K]
  change ((witness2521Positive.map _).sum-(witness2521Negative.map _).sum)=_
  omega

/-- Exact coefficients through the first witness for the actual product. -/
theorem coeff_four2521_first_range (N : ℕ) (hN : N ≤ 632) :
    coeff (2521*N+2273) (quintupleSpecialized 2521 1 * quintupleSpecialized 2521 35 *
      quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71)=
        if N=632 then 1 else 0 := by
  have hh := witness2521_entries_eval N hN
  rw [witness2521_balance_eval witness2521_signed_balance] at hh
  have hp : quintupleSpecialized 2521 1 * quintupleSpecialized 2521 35 *
      quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71=
      quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 *
      quintupleSpecialized 2521 71 * quintupleSpecialized 2521 1 := by ring
  rw [hp,← hh]
  have he : (3191090 : ℤ)=2*((2521*N+2273 : ℕ) : ℤ) ↔ N=632 := by omega
  simp only [he]

/-- The first 632 progression terms vanish and the next is one. -/
theorem first_witness_four2521 :
    (∀ N : ℕ, N < 632 → coeff (2521*N+2273) (quintupleSpecialized 2521 1 *
      quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71)=0) ∧
    coeff (2521*632+2273) (quintupleSpecialized 2521 1 * quintupleSpecialized 2521 35 *
      quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71)=1 := by
  constructor
  · intro N hN
    rw [coeff_four2521_first_range N (by omega),if_neg (by omega)]
  · simpa using coeff_four2521_first_range 632 (by omega)

/-- Even rounding the quarter-prime cutoff upward leaves a false vanishing test. -/
theorem four2521_quarter_plus_one_fails :
    (∀ N : ℕ, N ≤ 2521/4+1 → coeff (2521*N+2273) (quintupleSpecialized 2521 1 *
      quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71)=0) ∧
    ¬ (∀ N : ℕ, coeff (2521*N+2273) (quintupleSpecialized 2521 1 *
      quintupleSpecialized 2521 35 * quintupleSpecialized 2521 36 * quintupleSpecialized 2521 71)=0) := by
  refine ⟨fun N hN => first_witness_four2521.1 N (by omega),?_⟩
  intro h
  have hh := h 632
  rw [first_witness_four2521.2] at hh
  norm_num at hh

/-- This counterexample lies inside the expanded sum-of-two-squares reflection family. -/
theorem four2521_parameters : Nat.Prime 2521 ∧ 2521=36^2+35^2 ∧
    9 ∣ (36 : ℕ) ∧ 2521 ∣ (1^2+35^2+36^2+71^2 : ℕ) ∧
    (0 < (1 : ℕ) ∧ 1 < (35 : ℕ) ∧ 35 < (36 : ℕ) ∧ 36 < (71 : ℕ) ∧ 2*71 < (2521 : ℕ)) := by
  norm_num

end Ramanujan.MultiQuintuple
