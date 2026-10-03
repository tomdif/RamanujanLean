/-
# Appell–Lerch sums over Laurent series: summation infrastructure

All objects live in `L = ℂ((t))` (`LaurentSeries ℂ`). Infinite sums are `HahnSeries.SummableFamily`
sums. This file adds:
* `ofSupp` — a summable family from "each coefficient is hit finitely often, uniformly bounded below";
* `hsum_fubini` — `Σ_{(i,j)} s(i,j) = Σ_i Σ_j s(i,j)`;
* monomial bookkeeping `mono e c = c·tᵉ`.
-/
import Mathlib

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

abbrev L := HahnSeries ℤ ℂ

/-- the monomial `c·tᵉ`. -/
noncomputable abbrev mono (e : ℤ) (c : ℂ) : L := single e c

lemma mono_mul (e f : ℤ) (c d : ℂ) : mono e c * mono f d = mono (e + f) (c * d) := single_mul_single

section Summable
variable {ι κ : Type*}

/-- a family is summable when everything lives above `D` and each coefficient is hit finitely often. -/
noncomputable def ofSupp (f : ι → L) (D : ℤ) (hD : ∀ i n, n < D → (f i).coeff n = 0)
    (hfin : ∀ n : ℤ, {i | (f i).coeff n ≠ 0}.Finite) : SummableFamily ℤ ℂ ι where
  toFun := f
  isPWO_iUnion_support' := by
    refine (BddBelow.isWF ⟨D, ?_⟩).isPWO
    intro n hn
    simp only [Set.mem_iUnion, HahnSeries.mem_support] at hn
    obtain ⟨i, hi⟩ := hn
    by_contra h
    exact hi (hD i n (lt_of_not_ge h))
  finite_co_support' := hfin

/-- the sum of a summable family, typed in `L` (avoids instance-path mismatches for `ring`). -/
noncomputable def hs (s : SummableFamily ℤ ℂ ι) : L := s.hsum

lemma hs_eq (s : SummableFamily ℤ ℂ ι) : hs s = s.hsum := rfl

@[simp] lemma ofSupp_apply (f : ι → L) (D : ℤ) (hD) (hfin) (i : ι) : ofSupp f D hD hfin i = f i := rfl

/-- **Fubini** for summable families: if every row sums to `t i`, the total is `Σ t`. -/
theorem hsum_fubini (s : SummableFamily ℤ ℂ (ι × κ)) (t : SummableFamily ℤ ℂ ι)
    (u : ι → SummableFamily ℤ ℂ κ) (hu : ∀ i j, u i j = s (i, j)) (ht : ∀ i, t i = hs (u i)) :
    hs s = hs t := by
  classical
  unfold hs
  ext n
  rw [SummableFamily.coeff_hsum, SummableFamily.coeff_hsum]
  set S := (s.finite_co_support n).toFinset
  set T := (t.finite_co_support n).toFinset
  set I := S.image Prod.fst ∪ T
  set J := S.image Prod.snd
  have hrow : ∀ i, (t i).coeff n = ∑ j ∈ J, (s (i, j)).coeff n := by
    intro i
    rw [ht, hs, SummableFamily.coeff_hsum_eq_sum_of_subset (t := J)]
    · exact sum_congr rfl fun j _ => by rw [hu]
    · intro j hj
      simp only [ne_eq, hu] at hj
      exact mem_image.mpr ⟨(i, j), (Set.Finite.mem_toFinset _).mpr hj, rfl⟩
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := I)]
  · simp_rw [hrow]
    rw [← sum_product' (f := fun i j => (s (i, j)).coeff n)]
    refine sum_subset (fun p hp => ?_) fun p _ hp => ?_
    · exact mem_product.mpr ⟨mem_union_left _ (mem_image_of_mem _ hp), mem_image_of_mem _ hp⟩
    · by_contra h; exact hp ((Set.Finite.mem_toFinset _).mpr h)
  · intro i hi
    exact mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hi)
  · intro p hp
    exact (Set.Finite.mem_toFinset _).mpr hp

end Summable

end ALz

namespace ALz
open HahnSeries Finset

/-! ## Monomial families -/

section MonoFam
variable {ι : Type*}

lemma coeff_mono_ne {e n : ℤ} {c : ℂ} (h : (mono e c).coeff n ≠ 0) : n = e := by
  by_contra hne; exact h (by simp [mono, coeff_single_of_ne hne])

/-- a family of monomials `c_i t^{E_i}` with `E` bounded below and finite fibres. -/
noncomputable def monoFam (E : ι → ℤ) (c : ι → ℂ) (D : ℤ) (hD : ∀ i, D ≤ E i)
    (hfin : ∀ n, {i | E i = n}.Finite) : SummableFamily ℤ ℂ ι :=
  ofSupp (fun i => mono (E i) (c i)) D
    (fun i n hn => by
      have : n ≠ E i := by have := hD i; omega
      simp [mono, coeff_single_of_ne this])
    (fun n => (hfin n).subset fun i hi => (coeff_mono_ne hi).symm)

@[simp] lemma monoFam_apply (E : ι → ℤ) (c : ι → ℂ) (D hD hfin) (i : ι) :
    monoFam E c D hD hfin i = mono (E i) (c i) := rfl

end MonoFam

/-! ## Binomial `C(k,2)` on `ℤ` -/

/-- `C(k,2) = k(k−1)/2` for `k : ℤ`. -/
def c2 (k : ℤ) : ℤ := k * (k - 1) / 2

lemma two_c2 (k : ℤ) : 2 * c2 k = k * (k - 1) := by
  unfold c2
  have : 2 ∣ k * (k - 1) := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (k - 1), by subst hm; ring⟩
    · exact ⟨k * m, by subst hm; ring⟩
  exact Int.mul_ediv_cancel' this

lemma c2_succ (k : ℤ) : c2 (k + 1) = c2 k + k := by
  have h1 := two_c2 (k + 1); have h2 := two_c2 k; nlinarith

lemma c2_one_sub (k : ℤ) : c2 (1 - k) = c2 k := by
  have h1 := two_c2 (1 - k); have h2 := two_c2 k; nlinarith

lemma c2_nonneg (k : ℤ) : 0 ≤ c2 k := by
  have h := two_c2 k; nlinarith [sq_nonneg (2 * k - 1)]

/-! ## Theta values `θ(w) = Σ_k (−1)^k q^{C(k,2)} wᵏ`, `q = t^N`, `w = c tᵉ` -/

section Theta
variable (N : ℕ)

/-- exponent of the `k`-th theta term. -/
def thE (e k : ℤ) : ℤ := N * c2 k + e * k

/-- coefficient of the `k`-th theta term. -/
noncomputable def thC (c : ℂ) (k : ℤ) : ℂ := (-1) ^ k * c ^ k

variable {N}

lemma thE_lb (hN : 1 ≤ N) (e k : ℤ) : -(e * e) - 1 ≤ thE N e k := by
  unfold thE
  have h := two_c2 k
  have h0 := c2_nonneg k
  have : c2 k ≤ (N : ℤ) * c2 k := le_mul_of_one_le_left h0 (by exact_mod_cast hN)
  nlinarith [sq_nonneg (k + e), sq_nonneg (k - 1 + e)]

lemma thE_bound (hN : 1 ≤ N) (e k n : ℤ) (h : thE N e k = n) : |k| ≤ 2 * |n| + 2 * |e| + 1 := by
  unfold thE at h
  have h2 := two_c2 k
  have h0 := c2_nonneg k
  have : c2 k ≤ (N : ℤ) * c2 k := le_mul_of_one_le_left h0 (by exact_mod_cast hN)
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rcases abs_cases e with ⟨he, _⟩ | ⟨he, _⟩ <;>
    rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rw [hk, he, hn] <;> nlinarith

lemma thE_fin (hN : 1 ≤ N) (e n : ℤ) : {k : ℤ | thE N e k = n}.Finite :=
  (Set.finite_Icc (-(2 * |n| + 2 * |e| + 1)) (2 * |n| + 2 * |e| + 1)).subset fun k hk => by
    have := thE_bound hN e k n hk
    exact ⟨by rw [abs_le] at this; exact this.1, by rw [abs_le] at this; exact this.2⟩

/-- the theta family. -/
noncomputable def thF (hN : 1 ≤ N) (e : ℤ) (c : ℂ) : SummableFamily ℤ ℂ ℤ :=
  monoFam (thE N e) (thC c) _ (thE_lb hN e) (thE_fin hN e)

/-- `θ(c tᵉ) = Σ_k (−1)^k q^{C(k,2)} (c tᵉ)ᵏ`. -/
noncomputable def θ (hN : 1 ≤ N) (e : ℤ) (c : ℂ) : L := hs (thF hN e c)

end Theta


/-! ## Reindexing -/

section Reindex
variable {ι κ : Type*}

lemma hsum_congr (s t : SummableFamily ℤ ℂ ι) (h : ∀ i, s i = t i) : hs s = hs t := by
  rw [SummableFamily.coe_injective (funext h)]

/-- if `t (σ i) = a · s i` along a bijection `σ`, then `Σ t = a · Σ s`. -/
lemma hsum_reindex (s : SummableFamily ℤ ℂ ι) (t : SummableFamily ℤ ℂ κ) (σ : ι ≃ κ) (a : L)
    (h : ∀ i, t (σ i) = a * s i) : hs t = a * hs s := by
  unfold hs
  rw [← SummableFamily.hsum_smul, ← SummableFamily.hsum_equiv σ (a • s)]
  refine hsum_congr _ _ fun k => ?_
  simp only [SummableFamily.Equiv_toFun, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul]
  rw [← h, Equiv.apply_symm_apply]

end Reindex

section ThetaFacts
variable {N : ℕ} (hN : 1 ≤ N)
include hN

omit hN in
lemma zpow_neg_one_one_sub (k : ℤ) : ((-1 : ℂ)) ^ (1 - k) = -(-1) ^ k := by
  rw [zpow_sub₀ (by norm_num), zpow_one, div_eq_mul_inv, ← zpow_neg]
  rw [show ((-1 : ℂ)) ^ (-k) = (-1) ^ k by rw [zpow_neg, ← inv_zpow, inv_neg, inv_one], neg_one_mul]

omit hN in
lemma neg_one_zpow_sq (k : ℤ) : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by
  rw [← mul_zpow]; norm_num

/-- `θ(1) = 0`. -/
theorem θ_one : θ hN 0 1 = 0 := by
  have h := hsum_reindex (thF hN 0 1) (thF hN 0 1) (Equiv.subLeft 1) (-1) fun k => by
    simp only [thF, monoFam_apply, Equiv.subLeft_apply, thE, thC, c2_one_sub, one_zpow, mul_one,
      zero_mul, add_zero]
    rw [zpow_neg_one_one_sub, mono, mono, single_neg]
    exact (neg_one_mul _).symm
  have h2 : (2 : L) * θ hN 0 1 = 0 := by
    unfold θ; rw [two_mul]; nth_rw 1 [h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exfalso
    rw [← one_add_one_eq_two] at h3
    have := congrArg (fun f : L => f.coeff 0) h3
    simp only [coeff_add, coeff_one, if_true, coeff_zero] at this
    norm_num at this
  · exact h3

/-- `θ(1/w) = −w⁻¹ θ(w)`. -/
theorem θ_inv (e : ℤ) {c : ℂ} (hc : c ≠ 0) : θ hN (-e) c⁻¹ = -mono (-e) c⁻¹ * θ hN e c := by
  refine hsum_reindex (thF hN e c) (thF hN (-e) c⁻¹) (Equiv.subLeft 1) _ fun k => ?_
  simp only [thF, monoFam_apply, Equiv.subLeft_apply, thE, thC, c2_one_sub, zpow_neg_one_one_sub]
  rw [neg_mul (mono (-e) c⁻¹), mono_mul, mono, mono, ← single_neg]
  congr 1
  · ring
  · rw [inv_zpow', show -(1 - k) = k - 1 by ring, zpow_sub₀ hc, zpow_one]; field_simp

end ThetaFacts


/-! ## Rows of a summable family over a product -/

section Rows
variable {ι κ : Type*}

/-- the `i`-th row of a summable family over `ι × κ`. -/
noncomputable def row (s : SummableFamily ℤ ℂ (ι × κ)) (i : ι) : SummableFamily ℤ ℂ κ where
  toFun j := s (i, j)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono fun n hn => by
    simp only [Set.mem_iUnion] at hn ⊢
    obtain ⟨j, hj⟩ := hn; exact ⟨(i, j), hj⟩
  finite_co_support' n := (s.finite_co_support n).preimage
    (fun _ _ _ _ h => (Prod.mk.inj h).2)

@[simp] lemma row_apply (s : SummableFamily ℤ ℂ (ι × κ)) (i : ι) (j : κ) : row s i j = s (i, j) := rfl

/-- the family of row sums of a summable family over `ι × κ`. -/
noncomputable def rowFam (s : SummableFamily ℤ ℂ (ι × κ)) : SummableFamily ℤ ℂ ι where
  toFun i := hs (row s i)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono fun n hn => by
    simp only [Set.mem_iUnion] at hn ⊢
    obtain ⟨i, hi⟩ := hn
    have := SummableFamily.support_hsum_subset hi
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, hj⟩ := this; exact ⟨(i, j), hj⟩
  finite_co_support' n := by
    refine ((s.finite_co_support n).image Prod.fst).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, hs, SummableFamily.coeff_hsum] at hi
    by_contra hne
    apply hi
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    by_contra hj
    exact hne ⟨(i, j), hj, rfl⟩

@[simp] lemma rowFam_apply (s : SummableFamily ℤ ℂ (ι × κ)) (i : ι) : rowFam s i = hs (row s i) := rfl

/-- **Fubini**: the total equals the sum of row sums. -/
theorem hs_rowFam (s : SummableFamily ℤ ℂ (ι × κ)) : hs (rowFam s) = hs s :=
  (hsum_fubini s (rowFam s) (row s) (fun _ _ => rfl) (fun _ => rfl)).symm

end Rows

end ALz
