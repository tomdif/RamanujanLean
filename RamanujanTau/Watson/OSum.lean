/-
# Locally finite sums of power series

`osum f = Σᵢ f i` for a family `f : ι → ℤ⟦X⟧` that is *locally finite*: for each `k`, only finitely many
`f i` have a nonzero `X^k` coefficient. This is the formal-power-series version of an absolutely
convergent series, and it is all Watson's 1937 proofs need:
- linearity (`osum_add`, `osum_sub`, `osum_neg`, `osum_smul`);
- multiplication by a fixed series (`mul_osum`);
- swapping double sums (`osum_prod`);
- reindexing (`osum_equiv`), the parity split (`osum_parity`) and peeling off the first term
  (`osum_succ`);
- compatibility with `q ↦ q^b` (`expand_osum`).
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Logic.Equiv.Nat
import Mathlib.RingTheory.PowerSeries.Expand

set_option autoImplicit false

namespace Watson
open PowerSeries Function

variable {ι κ : Type*}

/-- `f` is locally finite: each coefficient sees only finitely many members of the family. -/
def LF (f : ι → PowerSeries ℤ) : Prop := ∀ k, (support fun i => coeff k (f i)).Finite

/-- the sum of a locally finite family. -/
noncomputable def osum (f : ι → PowerSeries ℤ) : PowerSeries ℤ := mk fun k => ∑ᶠ i, coeff k (f i)

lemma coeff_osum (f : ι → PowerSeries ℤ) (k : ℕ) : coeff k (osum f) = ∑ᶠ i, coeff k (f i) :=
  coeff_mk _ _

lemma osum_ext {f g : ι → PowerSeries ℤ} (h : ∀ i, f i = g i) : osum f = osum g := by
  rw [funext h]

/-- a finset containing the supports of all coefficients up to `k`. -/
noncomputable def LF.fs {f : ι → PowerSeries ℤ} (hf : LF f) (k : ℕ) : Finset ι :=
  (Set.Finite.biUnion (Set.finite_Iic k) fun j _ => hf j).toFinset

lemma LF.mem_fs {f : ι → PowerSeries ℤ} (hf : LF f) {k j : ℕ} (hj : j ≤ k) {i : ι}
    (hi : coeff j (f i) ≠ 0) : i ∈ hf.fs k := by
  simp only [LF.fs, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_Iic]
  exact ⟨j, hj, hi⟩

lemma LF.finsum_eq {f : ι → PowerSeries ℤ} (hf : LF f) {k j : ℕ} (hj : j ≤ k) :
    ∑ᶠ i, coeff j (f i) = ∑ i ∈ hf.fs k, coeff j (f i) :=
  finsum_eq_sum_of_support_subset _ fun i hi => hf.mem_fs hj hi

lemma LF.coeff_osum_fs {f : ι → PowerSeries ℤ} (hf : LF f) {k j : ℕ} (hj : j ≤ k) :
    coeff j (osum f) = ∑ i ∈ hf.fs k, coeff j (f i) := by
  rw [Watson.coeff_osum, hf.finsum_eq hj]

/-- vanishing criterion: if `f i` is divisible by `X^(w i)` and `w` is finite-to-one, `f` is
locally finite. -/
lemma LF.of_order {f : ι → PowerSeries ℤ} (w : ι → ℕ) (hw : ∀ i k, k < w i → coeff k (f i) = 0)
    (hfin : ∀ k, {i | w i ≤ k}.Finite) : LF f := by
  intro k
  refine (hfin k).subset fun i hi => ?_
  by_contra h
  exact hi (hw i k (lt_of_not_ge h))

/-- for `ℕ`-indexed families, it suffices that `f n` has no terms below degree `n`. -/
lemma LF.of_nat {f : ℕ → PowerSeries ℤ} (h : ∀ n k, k < n → coeff k (f n) = 0) : LF f :=
  LF.of_order id h fun k => (Set.finite_Iic k).subset fun _ hi => hi

lemma LF.add {f g : ι → PowerSeries ℤ} (hf : LF f) (hg : LF g) : LF (f + g) := fun k =>
  ((hf k).union (hg k)).subset fun i hi => by
    by_contra h
    simp only [Set.mem_union, mem_support, not_or, not_not] at h
    exact hi (by simp [h.1, h.2])

lemma LF.neg {f : ι → PowerSeries ℤ} (hf : LF f) : LF (-f) := fun k =>
  (hf k).subset fun i hi => by simpa using hi

lemma LF.sub {f g : ι → PowerSeries ℤ} (hf : LF f) (hg : LF g) : LF (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma LF.mem_fs_mul {f : ι → PowerSeries ℤ} (hf : LF f) (g : PowerSeries ℤ) {k j : ℕ} (hj : j ≤ k)
    {i : ι} (hi : coeff j (g * f i) ≠ 0) : i ∈ hf.fs k := by
  rw [coeff_mul] at hi
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hp' := Finset.mem_antidiagonal.mp hp
  exact hf.mem_fs (by omega : p.2 ≤ k) (right_ne_zero_of_mul hne)

lemma LF.mul_left {f : ι → PowerSeries ℤ} (hf : LF f) (g : PowerSeries ℤ) :
    LF fun i => g * f i := fun k =>
  ((hf.fs k).finite_toSet).subset fun _ hi => hf.mem_fs_mul g le_rfl hi

lemma LF.mul_right {f : ι → PowerSeries ℤ} (hf : LF f) (g : PowerSeries ℤ) :
    LF fun i => f i * g := by
  simpa [mul_comm] using hf.mul_left g

lemma LF.comp_injective {f : ι → PowerSeries ℤ} (hf : LF f) {e : κ → ι} (he : Injective e) :
    LF (f ∘ e) := fun k => (hf k).preimage he.injOn

lemma osum_add {f g : ι → PowerSeries ℤ} (hf : LF f) (hg : LF g) :
    osum (fun i => f i + g i) = osum f + osum g := by
  ext k
  simp only [coeff_osum, map_add]
  exact finsum_add_distrib (hf k) (hg k)

lemma osum_neg (f : ι → PowerSeries ℤ) : osum (fun i => -f i) = -osum f := by
  ext k
  simp only [coeff_osum, map_neg]
  exact finsum_neg_distrib _

lemma osum_sub {f g : ι → PowerSeries ℤ} (hf : LF f) (hg : LF g) :
    osum (fun i => f i - g i) = osum f - osum g := by
  ext k
  simp only [coeff_osum, map_sub]
  exact finsum_sub_distrib (hf k) (hg k)

lemma osum_zero : osum (fun _ : ι => (0 : PowerSeries ℤ)) = 0 := by
  ext k; simp [coeff_osum]

/-- multiplying a locally finite sum by a fixed series. -/
lemma mul_osum {f : ι → PowerSeries ℤ} (hf : LF f) (g : PowerSeries ℤ) :
    g * osum f = osum fun i => g * f i := by
  ext k
  rw [coeff_osum, finsum_eq_sum_of_support_subset _ (s := hf.fs k)
    (fun i hi => hf.mem_fs_mul g le_rfl hi), coeff_mul]
  simp only [coeff_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : p.2 ≤ k := by have := Finset.mem_antidiagonal.mp hp; omega
  rw [hf.coeff_osum_fs hp2, Finset.mul_sum]

lemma osum_mul {f : ι → PowerSeries ℤ} (hf : LF f) (g : PowerSeries ℤ) :
    osum f * g = osum fun i => f i * g := by
  rw [mul_comm, mul_osum hf]; simp only [mul_comm]

lemma osum_smul {f : ι → PowerSeries ℤ} (c : PowerSeries ℤ) (hf : LF f) :
    osum (fun i => c * f i) = c * osum f := (mul_osum hf c).symm

lemma LF.prod_left {f : ι × κ → PowerSeries ℤ} (hf : LF f) (i : ι) : LF fun j => f (i, j) :=
  hf.comp_injective (f := f) (e := Prod.mk i) (Prod.mk_right_injective i)

lemma LF.prod_outer {f : ι × κ → PowerSeries ℤ} (hf : LF f) :
    LF fun i => osum fun j => f (i, j) := fun k =>
  ((hf k).image Prod.fst).subset fun i hi => by
    simp only [mem_support] at hi
    rw [coeff_osum] at hi
    by_contra hc
    refine hi (finsum_eq_zero_of_forall_eq_zero (M := ℤ) fun j => ?_)
    by_contra hj
    exact hc ⟨(i, j), hj, rfl⟩

lemma LF.prod_outer' {f : ι × κ → PowerSeries ℤ} (hf : LF f) :
    LF fun j => osum fun i => f (i, j) :=
  LF.prod_outer (f := fun p : κ × ι => f (p.2, p.1)) (hf.comp_injective (e := Prod.swap) Prod.swap_injective)

/-- **Fubini** for locally finite double sums. -/
lemma osum_prod {f : ι × κ → PowerSeries ℤ} (hf : LF f) :
    osum f = osum fun i => osum fun j => f (i, j) := by
  ext k
  simp only [coeff_osum]
  exact finsum_curry _ (hf k)

/-- Fubini, the other way round. -/
lemma osum_prod_swap {f : ι × κ → PowerSeries ℤ} (hf : LF f) :
    (osum fun i => osum fun j => f (i, j)) = osum fun j => osum fun i => f (i, j) := by
  rw [← osum_prod hf]
  have hf' : LF (f ∘ Prod.swap) := hf.comp_injective Prod.swap_injective
  rw [show (osum fun j => osum fun i => f (i, j)) = osum fun j => osum fun i => (f ∘ Prod.swap) (j, i)
    from rfl, ← osum_prod hf']
  ext k
  simp only [coeff_osum]
  exact (finsum_comp_equiv (M := ℤ) (Equiv.prodComm ι κ).symm (f := fun p => coeff k (f p))).symm

/-- reindexing along an equivalence. -/
lemma osum_equiv (e : κ ≃ ι) (f : ι → PowerSeries ℤ) : osum (fun j => f (e j)) = osum f := by
  ext k
  simp only [coeff_osum]
  exact finsum_comp_equiv (M := ℤ) e (f := fun i => coeff k (f i))

lemma finsum_sum_elim {M : Type*} [AddCommMonoid M] (g : ι ⊕ κ → M) (hg : (support g).Finite) :
    ∑ᶠ x, g x = ∑ᶠ i, g (Sum.inl i) + ∑ᶠ j, g (Sum.inr j) := by
  classical
  set s := (hg.preimage Sum.inl_injective.injOn).toFinset
  set t := (hg.preimage Sum.inr_injective.injOn).toFinset
  rw [finsum_eq_sum_of_support_subset g (s := s.disjSum t) (fun x hx => by
      rcases x with i | j <;> simp [s, t, hx]),
    Finset.sum_disjSum,
    finsum_eq_sum_of_support_subset (fun i => g (Sum.inl i)) (s := s) (fun i hi => by simpa [s] using hi),
    finsum_eq_sum_of_support_subset (fun j => g (Sum.inr j)) (s := t) (fun j hj => by simpa [t] using hj)]

/-- **parity split** of an `ℕ`-indexed sum. -/
lemma osum_parity {f : ℕ → PowerSeries ℤ} (hf : LF f) :
    osum f = osum (fun n => f (2 * n)) + osum (fun n => f (2 * n + 1)) := by
  rw [← osum_equiv Equiv.natSumNatEquivNat f]
  ext k
  simp only [coeff_osum, map_add]
  rw [finsum_sum_elim _ ((hf k).preimage Equiv.natSumNatEquivNat.injective.injOn)]
  simp [Equiv.natSumNatEquivNat_apply]

lemma finsum_nat_succ {M : Type*} [AddCommMonoid M] (g : ℕ → M) (hg : (support g).Finite) :
    ∑ᶠ n, g n = g 0 + ∑ᶠ n, g (n + 1) := by
  obtain ⟨N, hN⟩ := hg.bddAbove
  have hsub : support g ⊆ ↑(Finset.range (N + 1)) := fun n hn => by
    simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le (hN hn)
  rw [finsum_eq_sum_of_support_subset g hsub, Finset.sum_range_succ',
    finsum_eq_sum_of_support_subset (fun n => g (n + 1)) (s := Finset.range N) (fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have := hN (show n + 1 ∈ support g from hn); omega), add_comm]

/-- peeling off the first term. -/
lemma osum_succ {f : ℕ → PowerSeries ℤ} (hf : LF f) : osum f = f 0 + osum fun n => f (n + 1) := by
  ext k
  simp only [coeff_osum, map_add]
  exact finsum_nat_succ _ (hf k)

/-- a family supported on a finset sums to the finite sum. -/
lemma osum_eq_sum {f : ι → PowerSeries ℤ} (s : Finset ι) (hs : ∀ i ∉ s, f i = 0) :
    osum f = ∑ i ∈ s, f i := by
  ext k
  rw [coeff_osum, map_sum]
  exact finsum_eq_sum_of_support_subset _ fun i hi => by
    by_contra h; exact hi (by simp [hs i h])

lemma LF.of_finite {f : ι → PowerSeries ℤ} (s : Finset ι) (hs : ∀ i ∉ s, f i = 0) : LF f := fun _ =>
  s.finite_toSet.subset fun i hi => by by_contra h; exact hi (by simp [hs i h])

/-- `q ↦ q^b` commutes with locally finite sums. -/
lemma expand_osum (b : ℕ) (hb : b ≠ 0) {f : ι → PowerSeries ℤ} (hf : LF f) :
    expand b hb (osum f) = osum fun i => expand b hb (f i) := by
  ext k
  rw [coeff_expand, coeff_osum, coeff_osum]
  simp only [coeff_expand]
  split_ifs with h
  · rfl
  · simp

lemma LF.expand {f : ι → PowerSeries ℤ} (hf : LF f) (b : ℕ) (hb : b ≠ 0) :
    LF fun i => expand b hb (f i) := fun k =>
  (hf (k / b)).subset fun i hi => by
    simp only [mem_support, coeff_expand] at hi ⊢
    split_ifs at hi <;> simp_all

end Watson
