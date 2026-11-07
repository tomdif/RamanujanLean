/-
# M2.4 (arithmetic core): partial sums along a line `P m − Q n = k` are box sums

Along the line `P m − Q n = k` (`P, Q ≥ 1`) both `m` and `n` increase, so the partial sum over
`m ≤ M` equals the two-sided box sum `shiftSum2 P Q k N` for `N = max(M, ⌊(PM − k)/Q⌋)`
(`lineSum_eq_shiftSum2`).  Hence `SCS2Coprime.scs2_general` bounds every partial sum
(`abs_lineSum_le`), and Abel summation (`norm_sum_mul_le_abel`) bounds weighted line sums
`Σ_{m<M} h(m) c(m)` by `max |partial sums| · (|h(M−1)| + Σ |h(m+1) − h(m)|)`.
Level 1.
-/
import RamanujanTau.SCS2Coprime.Main3

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Finset RamanujanTau.SubconvexityCond RamanujanTau.HeckeAFE

/-- The term of the line `P m − Q n = k` at `m` (at most one `n` contributes). -/
noncomputable def lineTerm (P Q : ℕ) (k : ℤ) (m : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 (P * m + k.natAbs), if (P : ℤ) * m - Q * n = k then lam m * lam n else 0

/-- The partial sum `Σ_{1 ≤ m ≤ M}` along the line. -/
noncomputable def lineSum (P Q : ℕ) (k : ℤ) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, lineTerm P Q k m

/-- `⌊(PM − k)/Q⌋⁺`. -/
def nmax (P Q : ℕ) (k : ℤ) (M : ℕ) : ℕ := (((P : ℤ) * M - k) / Q).toNat

/-- The box size. -/
def Nbox (P Q : ℕ) (k : ℤ) (M : ℕ) : ℕ := max M (nmax P Q k M)

lemma le_nmax {P Q : ℕ} (hQ : 1 ≤ Q) {k : ℤ} {M n : ℕ} (h : (Q : ℤ) * n ≤ (P : ℤ) * M - k) :
    n ≤ nmax P Q k M := by
  unfold nmax
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have : (n : ℤ) ≤ ((P : ℤ) * M - k) / Q := by
    rw [Int.le_ediv_iff_mul_le hQ']; linarith
  omega

lemma mul_nmax_le {P Q : ℕ} (hQ : 1 ≤ Q) {k : ℤ} {M : ℕ} (h1 : 1 ≤ nmax P Q k M) :
    (Q : ℤ) * nmax P Q k M ≤ (P : ℤ) * M - k := by
  unfold nmax at *
  have hQ' : (Q : ℤ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have h2 := Int.ediv_mul_le ((P : ℤ) * M - k) hQ'
  have h3 : (0 : ℤ) ≤ ((P : ℤ) * M - k) / Q := by omega
  rw [Int.toNat_of_nonneg h3]
  linarith

lemma nmax_le {P Q : ℕ} (hQ : 1 ≤ Q) (k : ℤ) (M : ℕ) : nmax P Q k M ≤ P * M + k.natAbs := by
  by_cases h1 : 1 ≤ nmax P Q k M
  · have h := mul_nmax_le hQ h1
    have hk : -k ≤ |k| := neg_le_abs k
    have hQn : (nmax P Q k M : ℤ) ≤ (Q : ℤ) * nmax P Q k M := by
      have : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    have : (nmax P Q k M : ℤ) ≤ ((P * M + k.natAbs : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  · omega

lemma Nbox_le {P Q : ℕ} (hQ : 1 ≤ Q) (k : ℤ) (M : ℕ) : Nbox P Q k M ≤ M + P * M + k.natAbs := by
  unfold Nbox
  have := nmax_le (P := P) hQ k M
  omega

/-- The inner box sum at `m`, for `m ≤ M`, is the line term. -/
lemma inner_eq_lineTerm {P Q : ℕ} (hQ : 1 ≤ Q) (k : ℤ) {M m : ℕ} (hm : m ≤ M) :
    (∑ n ∈ Icc 1 (Nbox P Q k M), if (P : ℤ) * m - Q * n = k then lam m * lam n else 0) =
      lineTerm P Q k m := by
  unfold lineTerm
  set f : ℕ → ℝ := fun n => if (P : ℤ) * m - Q * n = k then lam m * lam n else 0
  set L := Nbox P Q k M + (P * m + k.natAbs)
  have hQ1 : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hA : (∑ n ∈ Icc 1 (Nbox P Q k M), f n) = ∑ n ∈ Icc 1 L, f n := by
    refine sum_subset (Icc_subset_Icc le_rfl (by omega)) fun n hn hn' => ?_
    simp only [f]
    rw [if_neg]
    intro he
    rw [mem_Icc] at hn hn'
    have hle : n ≤ nmax P Q k M := le_nmax hQ (by
      have : (P : ℤ) * m ≤ (P : ℤ) * M := by
        have : (m : ℤ) ≤ M := by exact_mod_cast hm
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith)
    have : n ≤ Nbox P Q k M := le_trans hle (le_max_right _ _)
    omega
  have hB : (∑ n ∈ Icc 1 (P * m + k.natAbs), f n) = ∑ n ∈ Icc 1 L, f n := by
    refine sum_subset (Icc_subset_Icc le_rfl (by omega)) fun n hn hn' => ?_
    simp only [f]
    rw [if_neg]
    intro he
    rw [mem_Icc] at hn hn'
    have h1 : P * m + k.natAbs < n := by omega
    have h2 : ((P * m + k.natAbs : ℕ) : ℤ) < n := by exact_mod_cast h1
    push_cast at h2
    have hk : -k ≤ |k| := neg_le_abs k
    have : (n : ℤ) ≤ (Q : ℤ) * n := by nlinarith
    linarith
  rw [hA, hB]

/-- The inner box sum at `m`, for `M < m`, vanishes. -/
lemma inner_eq_zero {P Q : ℕ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (k : ℤ) {M m : ℕ} (hm : M < m)
    (hmN : m ≤ Nbox P Q k M) :
    (∑ n ∈ Icc 1 (Nbox P Q k M), if (P : ℤ) * m - Q * n = k then lam m * lam n else 0) = 0 := by
  refine sum_eq_zero fun n hn => ?_
  rw [if_neg]
  intro he
  rw [mem_Icc] at hn
  have hN : Nbox P Q k M = nmax P Q k M := by
    unfold Nbox at hmN ⊢; omega
  have h1 : 1 ≤ nmax P Q k M := by omega
  have h2 := mul_nmax_le hQ h1
  have h3 : (P : ℤ) * M < (P : ℤ) * m := by
    have : (M : ℤ) < m := by exact_mod_cast hm
    have : (1 : ℤ) ≤ P := by exact_mod_cast hP
    nlinarith
  have h4 : (Q : ℤ) * nmax P Q k M < (Q : ℤ) * n := by linarith
  have h5 : (nmax P Q k M : ℤ) < n := by
    have : (0 : ℤ) < Q := by exact_mod_cast hQ
    nlinarith
  have : n ≤ nmax P Q k M := hN ▸ hn.2
  omega

/-- **Partial sums along the line are box sums.** -/
theorem lineSum_eq_shiftSum2 {P Q : ℕ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (k : ℤ) (M : ℕ) :
    lineSum P Q k M = shiftSum2 P Q k (Nbox P Q k M) := by
  unfold shiftSum2 lineSum
  have hMN : M ≤ Nbox P Q k M := le_max_left _ _
  symm
  calc (∑ m ∈ Icc 1 (Nbox P Q k M), ∑ n ∈ Icc 1 (Nbox P Q k M),
        if (P : ℤ) * m - Q * n = k then lam m * lam n else 0)
      = ∑ m ∈ Icc 1 (Nbox P Q k M), if m ≤ M then lineTerm P Q k m else 0 := by
        refine sum_congr rfl fun m hm => ?_
        split_ifs with h
        · exact inner_eq_lineTerm hQ k h
        · exact inner_eq_zero hP hQ k (by omega) (mem_Icc.1 hm).2
    _ = ∑ m ∈ Icc 1 M, lineTerm P Q k m := by
        rw [← sum_filter]
        congr 1
        ext m; simp only [mem_filter, mem_Icc]; omega

/-- **Every partial sum along the line is bounded by `scs2_general`.** -/
theorem abs_lineSum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (P Q : ℕ) (k : ℤ) (M : ℕ), 1 ≤ P → 1 ≤ Q → k ≠ 0 →
    |lineSum P Q k M| ≤
      C * ((M + P * M + k.natAbs : ℕ) : ℝ) ^ (1 - 1 / 21 : ℝ) * |(k : ℝ)| ^ (1 / 21 : ℝ) *
        ((P * Q : ℕ) : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.SCS2Coprime.scs2_general
  refine ⟨C, hC0, fun P Q k M hP hQ hk => ?_⟩
  rw [lineSum_eq_shiftSum2 hP hQ k M]
  refine (hC P Q k _ hP hQ hk).trans ?_
  have hle : ((Nbox P Q k M : ℕ) : ℝ) ≤ ((M + P * M + k.natAbs : ℕ) : ℝ) := by
    exact_mod_cast Nbox_le hQ k M
  gcongr

/-! ## Abel summation -/

/-- **Abel summation bound.** If every partial sum `Σ_{i<n} c i` (`n ≤ N`) has norm `≤ B`, then
`‖Σ_{i<N} h i · c i‖ ≤ B (‖h(N−1)‖ + Σ_{i<N−1} ‖h(i+1) − h i‖)`. -/
theorem norm_sum_mul_le_abel (h c : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : ∀ n ≤ N, ‖∑ i ∈ range n, c i‖ ≤ B) :
    ‖∑ i ∈ range N, h i * c i‖ ≤
      B * (‖h (N - 1)‖ + ∑ i ∈ range (N - 1), ‖h (i + 1) - h i‖) := by
  have e := sum_range_by_parts h c N
  simp only [smul_eq_mul] at e
  rw [e]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add, Finset.mul_sum (range (N - 1)) (fun i => ‖h (i + 1) - h i‖) B]
  refine add_le_add ?_ ((norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_))
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB N le_rfl) (norm_nonneg _)
  · rw [norm_mul, mul_comm]
    have : i + 1 ≤ N := by rw [mem_range] at hi; omega
    exact mul_le_mul_of_nonneg_right (hB (i + 1) this) (norm_nonneg _)

end RamanujanTau.SelbergKey4
