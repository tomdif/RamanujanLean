/-
# The log-derivative (Newton) identity for the Kloosterman L-function

For a finite field `F` and the completely multiplicative `λ = lam ψ a b` on monic polynomials,
with `A_n = degSum n` and the "von Mangoldt" sums
`V_k = Σ_{P monic irreducible, deg P ∣ k} deg P · λ(P)^{k / deg P}`,
`newton_identity`: `n A_n = Σ_{k=1}^n V_k A_{n-k}`.
This is the coefficient form of `T L'(T)/L(T) = Σ_k V_k T^k` for `L(T) = Σ_n A_n T^n`; it is
proved by unique factorization (`deg f = Σ_{P^j ∣ f, j ≥ 1} deg P`), with no Euler product.
-/
import RamanujanTau.KloostermanL.Lambda

set_option autoImplicit false

namespace RamanujanTau.KloostermanL

open Polynomial Finset UniqueFactorizationMonoid
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

/-- Monic irreducible polynomials of degree `≤ n`. -/
noncomputable def irrLe (n : ℕ) : Finset F[X] :=
  (range (n + 1)).biUnion (fun d => (monicDeg d).filter Irreducible)

theorem mem_irrLe {n : ℕ} {P : F[X]} :
    P ∈ irrLe n ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ≤ n := by
  simp only [irrLe, mem_biUnion, mem_range, mem_filter, mem_monicDeg]
  constructor
  · rintro ⟨d, hd, ⟨hm, rfl⟩, hi⟩
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨P.natDegree, by omega, ⟨hm, rfl⟩, hi⟩

omit [Fintype F] in
theorem pow_dvd_iff_le_count {P f : F[X]} (hP : Irreducible P) (hPm : P.Monic) (hf : f ≠ 0)
    (j : ℕ) : P ^ j ∣ f ↔ j ≤ (normalizedFactors f).count P := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP.ne_zero) hf,
    normalizedFactors_pow, normalizedFactors_irreducible hP, hPm.normalize_eq_self,
    Multiset.nsmul_singleton, Multiset.le_count_iff_replicate_le]

omit [Fintype F] in
theorem natDegree_eq_sum_count {f : F[X]} (hf : f.Monic) :
    f.natDegree = ∑ P ∈ (normalizedFactors f).toFinset,
      (normalizedFactors f).count P * P.natDegree := by
  have h0 : (0 : F[X]) ∉ normalizedFactors f := zero_notMem_normalizedFactors f
  conv_lhs => rw [← hf.normalize_eq_self, ← prod_normalizedFactors_eq hf.ne_zero]
  rw [natDegree_multiset_prod _ h0, Finset.sum_multiset_map_count]
  rfl

omit [Fintype F] in
theorem monic_irreducible_of_mem {f P : F[X]} (hP : P ∈ normalizedFactors f) :
    P.Monic ∧ Irreducible P := by
  have hi := irreducible_of_normalized_factor P hP
  have hn := normalize_normalized_factor P hP
  refine ⟨?_, hi⟩
  rw [← hn]
  exact monic_normalize hi.ne_zero

/-- `deg f = Σ_{P monic irreducible} Σ_{1 ≤ j ≤ n} [P^j ∣ f] deg P`. -/
theorem natDegree_eq_vonMangoldt {n : ℕ} {f : F[X]} (hf : f.Monic) (hn : f.natDegree = n) :
    (n : ℂ) = ∑ P ∈ irrLe n, ∑ j ∈ Icc 1 n, if P ^ j ∣ f then (P.natDegree : ℂ) else 0 := by
  have hinner : ∀ P ∈ irrLe n, (∑ j ∈ Icc 1 n, if P ^ j ∣ f then (P.natDegree : ℂ) else 0) =
      ((normalizedFactors f).count P * P.natDegree : ℕ) := by
    intro P hP
    obtain ⟨hPm, hPi, -⟩ := mem_irrLe.mp hP
    set c := (normalizedFactors f).count P
    have hc : c ≤ n := by
      have hdvd : P ^ c ∣ f := (pow_dvd_iff_le_count hPi hPm hf.ne_zero c).2 le_rfl
      have := natDegree_le_of_dvd hdvd hf.ne_zero
      rw [natDegree_pow] at this
      have hpos := hPi.natDegree_pos
      nlinarith
    simp_rw [pow_dvd_iff_le_count hPi hPm hf.ne_zero]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (Icc 1 n).filter (fun j => j ≤ c) = Icc 1 c := by
      ext j; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hinner]
  have hsub : (normalizedFactors f).toFinset ⊆ irrLe n := by
    intro P hP
    rw [Multiset.mem_toFinset] at hP
    obtain ⟨hm, hi⟩ := monic_irreducible_of_mem hP
    exact mem_irrLe.2 ⟨hm, hi, hn ▸ natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hP)
      hf.ne_zero⟩
  rw [← Finset.sum_subset hsub (fun P _ hP => by
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hP; simp [hP])]
  rw [← hn, natDegree_eq_sum_count hf]
  push_cast
  rfl

variable (ψ : AddChar F ℂ) (a b : F)

/-- Sum of `λ` over the multiples of `P^j` of degree `n`. -/
theorem sum_dvd_lam {P : F[X]} (hPm : P.Monic) (n j : ℕ) :
    ∑ f ∈ (monicDeg n).filter (fun f => P ^ j ∣ f), lam ψ a b f =
      if j * P.natDegree ≤ n then lam ψ a b P ^ j * degSum ψ a b (n - j * P.natDegree)
      else 0 := by
  split_ifs with hle
  · unfold degSum
    rw [Finset.mul_sum, ← lam_pow ψ a b hPm]
    symm
    refine Finset.sum_bij (fun h _ => P ^ j * h) (fun h hh => ?_) (fun h₁ _ h₂ _ e => ?_)
      (fun f hf => ?_) (fun h hh => ?_)
    · rw [mem_monicDeg] at hh
      rw [mem_filter, mem_monicDeg]
      refine ⟨⟨(hPm.pow j).mul hh.1, ?_⟩, dvd_mul_right _ _⟩
      rw [(hPm.pow j).natDegree_mul hh.1, natDegree_pow, hh.2]
      omega
    · exact mul_left_cancel₀ (pow_ne_zero _ hPm.ne_zero) e
    · rw [mem_filter, mem_monicDeg] at hf
      obtain ⟨⟨hfm, hfn⟩, h, rfl⟩ := hf
      have hhm : h.Monic := (hPm.pow j).of_mul_monic_left hfm
      refine ⟨h, mem_monicDeg.2 ⟨hhm, ?_⟩, rfl⟩
      rw [(hPm.pow j).natDegree_mul hhm, natDegree_pow] at hfn
      omega
    · rw [mem_monicDeg] at hh
      exact (lam_mul ψ a b (hPm.pow j) hh.1).symm
  · refine Finset.sum_eq_zero (fun f hf => ?_)
    rw [mem_filter, mem_monicDeg] at hf
    obtain ⟨⟨hfm, hfn⟩, hd⟩ := hf
    have := natDegree_le_of_dvd hd hfm.ne_zero
    rw [natDegree_pow] at this
    omega

/-- The von Mangoldt sums `V_k = Σ_{P monic irr., deg P ∣ k} deg P · λ(P)^{k / deg P}`. -/
noncomputable def vM (k : ℕ) : ℂ :=
  ∑ P ∈ (irrLe k).filter (fun P : F[X] => P.natDegree ∣ k),
    (P.natDegree : ℂ) * lam ψ a b P ^ (k / P.natDegree)

/-- **Newton / log-derivative identity**: `n A_n = Σ_{k=1}^n V_k A_{n-k}`. -/
theorem newton_identity (n : ℕ) :
    (n : ℂ) * degSum ψ a b n = ∑ k ∈ Icc 1 n, vM ψ a b k * degSum ψ a b (n - k) := by
  -- step 1: expand `n` by unique factorization
  have step1 : (n : ℂ) * degSum ψ a b n = ∑ P ∈ irrLe n, ∑ j ∈ Icc 1 n,
      (P.natDegree : ℂ) * ∑ f ∈ (monicDeg n).filter (fun f => P ^ j ∣ f), lam ψ a b f := by
    unfold degSum
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun f hf => by
      rw [natDegree_eq_vonMangoldt (mem_monicDeg.mp hf).1 (mem_monicDeg.mp hf).2])]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    split_ifs <;> simp
  rw [step1]
  -- step 2: divide out `P^j`
  have step2 : ∀ P ∈ irrLe n, ∀ j ∈ Icc 1 n,
      (P.natDegree : ℂ) * ∑ f ∈ (monicDeg n).filter (fun f => P ^ j ∣ f), lam ψ a b f =
      ∑ k ∈ Icc 1 n, if j * P.natDegree = k then
        (P.natDegree : ℂ) * lam ψ a b P ^ j * degSum ψ a b (n - k) else 0 := by
    intro P hP j hj
    have hPm := (mem_irrLe.mp hP).1
    have hpos := (mem_irrLe.mp hP).2.1.natDegree_pos
    rw [sum_dvd_lam ψ a b hPm, Finset.sum_ite_eq]
    rw [mem_Icc] at hj
    by_cases hle : j * P.natDegree ≤ n
    · rw [if_pos hle, if_pos (mem_Icc.2 ⟨by nlinarith, hle⟩)]
      ring
    · rw [if_neg hle, if_neg (fun h => hle (mem_Icc.1 h).2)]
      simp
  rw [Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl (fun j hj => step2 P hP j hj))]
  -- step 3: regroup by `k = j deg P`
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [mem_Icc] at hk
  rw [vM, Finset.sum_mul]
  have hfilt : (irrLe k).filter (fun P : F[X] => P.natDegree ∣ k) =
      (irrLe n).filter (fun P : F[X] => P.natDegree ∣ k) := by
    ext P
    simp only [mem_filter, mem_irrLe]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h2, by omega⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨h1, h2, Nat.le_of_dvd (by omega) h4⟩, h4⟩
  rw [hfilt, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  have hpos := (mem_irrLe.mp hP).2.1.natDegree_pos
  split_ifs with hd
  · obtain ⟨m, hm⟩ := hd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    have hmn : m ≤ n := by nlinarith
    rw [Finset.sum_eq_single m]
    · rw [if_pos (by rw [hm]; ring), hm, Nat.mul_div_cancel_left _ hpos]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      have : j * P.natDegree = m * P.natDegree := by rw [h, hm]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    · intro h; exact absurd (mem_Icc.2 ⟨hm1, hmn⟩) h
  · refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    rintro rfl
    exact hd (dvd_mul_left _ _)

end RamanujanTau.KloostermanL
