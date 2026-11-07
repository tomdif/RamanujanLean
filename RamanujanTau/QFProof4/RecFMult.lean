/-
# `recF g` is multiplicative when `g` is supported on prime powers (unconditional)

* `recF_ppow_rec`: `k log p · recF g (p^k) = Σ_{e≤k} g(p^e) recF g(p^{k−e})`;
* **`recF_eq_prod`**: `recF g n = Π_{p | n} recF g (p^{v_p n})` for `n ≠ 0`;
* `recF_ppow_bound`: `|g(p^j)| ≤ 3 log p` (j ≥ 1) ⇒ `|recF g (p^k)| ≤ (k+1)(k+2)/2`.
-/
import RamanujanTau.QFProof3.Factor
import RamanujanTau.QFProof3.Decomp1

set_option autoImplicit false

namespace RamanujanTau.QFProof4

open Finset ArithmeticFunction RamanujanTau.QFProof3 RamanujanTau.QFProof2
open RamanujanTau.SelbergDelange3 (recF recFA toA recF_eq recF_zero recF_one recF_log)
open RamanujanTau.SelbergCoeffs (ofLocal ofLocal_apply ofLocal_ppow isMultiplicative_ofLocal)

variable (g : ℕ → ℝ)

lemma sum_ppow_div {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ e ∈ range (k + 1), g (p ^ e) * recF g (p ^ k / p ^ e) =
      ∑ e ∈ range (k + 1), g (p ^ e) * recF g (p ^ (k - e)) := by
  refine sum_congr rfl fun e he => ?_
  rw [Nat.pow_div (by have := mem_range.1 he; omega) hp.pos]

lemma recF_ppow_rec (h0 : g 0 = 0) (h1 : g 1 = 0) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k : ℝ) * Real.log p * recF g (p ^ k) = ∑ e ∈ Icc 0 k, g (p ^ e) * recF g (p ^ (k - e)) := by
  have h := recF_log g h0 h1 (p ^ k) (pow_pos hp.pos k)
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => toA g h0 a * recFA g b),
    Nat.divisors_prime_pow hp, sum_map] at h
  simp only [Function.Embedding.coeFn_mk, toA, recFA, coe_mk] at h
  have hI : Icc 0 k = range (k + 1) := by ext; simp only [mem_Icc, mem_range]; omega
  rw [hI, ← sum_ppow_div g hp k, ← h]
  have : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; rfl
  rw [this, Real.log_pow]
  ring

lemma g_repr (h1 : g 1 = 0) (hpp : ∀ n, ¬ IsPrimePow n → g n = 0) {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    g d = ∑ p ∈ n.primeFactors, (if d.factorization p = 0 then 0 else g (p ^ d.factorization p)) *
      ∏ q ∈ n.primeFactors.erase p, (if d.factorization q = 0 then (1 : ℝ) else 0) := by
  have d0 : d ≠ 0 := fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  by_cases hd1 : d = 1
  · subst hd1; simp [h1]
  by_cases hpd : IsPrimePow d
  · obtain ⟨p0, k, hp0, hk, rfl⟩ := (isPrimePow_nat_iff d).1 hpd
    have hfp : (p0 ^ k).factorization = Finsupp.single p0 k := hp0.factorization_pow
    have hp0n : p0 ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hp0, (dvd_pow_self p0 hk.ne').trans hd, hn⟩
    rw [sum_eq_single p0]
    · simp only [hfp, Finsupp.single_eq_same, if_neg hk.ne']
      rw [prod_eq_one fun q hq => by
        simp only [Finsupp.single_eq_of_ne (mem_erase.1 hq).1, if_true]]
      ring
    · intro p _ hp; simp only [hfp, Finsupp.single_eq_of_ne hp, if_true, zero_mul]
    · intro h; exact absurd hp0n h
  · rw [hpp d hpd]
    symm
    refine sum_eq_zero fun p hp => ?_
    by_cases hdp : d.factorization p = 0
    · rw [if_pos hdp, zero_mul]
    · have : ∃ q ∈ n.primeFactors.erase p, d.factorization q ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hpd
        have hs : d.factorization = Finsupp.single p (d.factorization p) := by
          ext q
          by_cases hqp : q = p
          · subst hqp; simp
          · rw [Finsupp.single_eq_of_ne hqp]
            by_cases hqn : q ∈ n.primeFactors
            · exact hcon q (mem_erase.2 ⟨hqp, hqn⟩)
            · have : q ∉ d.primeFactors := fun h => hqn (Nat.primeFactors_mono hd hn h)
              exact vanish_off this
        rw [Nat.eq_pow_of_factorization_eq_single d0 hs]
        exact (Nat.prime_of_mem_primeFactors hp).isPrimePow.pow hdp
      obtain ⟨q, hq, hq0⟩ := this
      rw [prod_eq_zero hq (if_neg hq0), mul_zero]

/-- **Multiplicativity**: `recF g n = Π_{p|n} recF g (p^{v_p n})`. -/
theorem recF_eq_prod (h0 : g 0 = 0) (h1 : g 1 = 0) (hpp : ∀ n, ¬ IsPrimePow n → g n = 0) (n : ℕ) (hn : n ≠ 0) :
    recF g n = ∏ p ∈ n.primeFactors, recF g (p ^ n.factorization p) := by
  set F : ArithmeticFunction ℝ := ofLocal (fun p k => recF g (p ^ k)) with hF
  have hF0 : ∀ p, (fun p k => recF g (p ^ k)) p 0 = 1 := fun p => by simp [recF_one]
  have hFapp : ∀ m, m ≠ 0 → F m = ∏ p ∈ m.primeFactors, recF g (p ^ m.factorization p) := by
    intro m hm
    rw [hF, ofLocal_apply _ hm, Finsupp.prod, Nat.support_factorization]
  have key : ∀ m, F m = recF g m := by
    intro m
    refine RamanujanTau.QFProof3.recF_unique g h0 h1 F ?_ ?_ m
    · rw [hFapp 1 one_ne_zero]; simp
    · intro m hm
      have hm0 : m ≠ 0 := hm.ne'
      have hFm : F m = ∏ q ∈ m.primeFactors, recF g (q ^ (m.factorization q)) := hFapp m hm0
      -- the convolution as a divisor sum
      rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => toA g h0 a * F b)]
      simp only [toA, coe_mk]
      have hterm : ∀ d ∈ m.divisors, g d * F (m / d) = ∑ p ∈ m.primeFactors,
          ∏ q ∈ m.primeFactors, (if q = p then (if d.factorization q = 0 then 0 else g (q ^ d.factorization q)) *
              recF g (q ^ (m.factorization q - d.factorization q))
            else (if d.factorization q = 0 then (1 : ℝ) else 0) * recF g (q ^ (m.factorization q - d.factorization q))) := by
        intro d hd
        have hdm := Nat.dvd_of_mem_divisors hd
        have hmd0 : m / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hm hdm) (Nat.pos_of_mem_divisors hd))
        have hFd : F (m / d) = ∏ q ∈ m.primeFactors, recF g (q ^ (m.factorization q - d.factorization q)) := by
          rw [hFapp _ hmd0]
          rw [prod_subset (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdm) hm0) fun q _ hq => by
            rw [vanish_off hq]; simp [recF_one]]
          refine prod_congr rfl fun q _ => ?_
          rw [Nat.factorization_div hdm]; rfl
        rw [g_repr g h1 hpp hm0 hdm, hFd, sum_mul]
        refine sum_congr rfl fun p hp => ?_
        have e1 := mul_prod_erase m.primeFactors
          (fun q => recF g (q ^ (m.factorization q - d.factorization q))) hp
        have e2 := mul_prod_erase m.primeFactors (fun q =>
          if q = p then (if d.factorization q = 0 then 0 else g (q ^ d.factorization q)) *
              recF g (q ^ (m.factorization q - d.factorization q))
            else (if d.factorization q = 0 then (1 : ℝ) else 0) *
              recF g (q ^ (m.factorization q - d.factorization q))) hp
        simp only [] at e1 e2
        rw [← e1, ← e2]
        simp only [ite_true]
        have e3 : ∏ x ∈ m.primeFactors.erase p, ((if d.factorization x = 0 then (1 : ℝ) else 0) *
            recF g (x ^ (m.factorization x - d.factorization x))) =
            ∏ x ∈ m.primeFactors.erase p, (if x = p then (if d.factorization x = 0 then 0 else
              g (x ^ d.factorization x)) * recF g (x ^ (m.factorization x - d.factorization x))
            else (if d.factorization x = 0 then (1 : ℝ) else 0) * recF g (x ^ (m.factorization x - d.factorization x))) :=
          prod_congr rfl fun q hq => by rw [if_neg (mem_erase.1 hq).1]
        rw [← e3, prod_mul_distrib]
        ring
      rw [sum_congr rfl hterm, sum_comm]
      rw [hFm, log_eq_sum hm0 (subset_refl _), mul_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [sum_divisors_prod_local hm0 (fun q e =>
        if q = p then (if e = 0 then 0 else g (q ^ e)) * recF g (q ^ (m.factorization q - e))
        else (if e = 0 then (1 : ℝ) else 0) * recF g (q ^ (m.factorization q - e)))]
      rw [← mul_prod_erase m.primeFactors (fun q => ∑ e ∈ Icc 0 (m.factorization q),
        if q = p then (if e = 0 then 0 else g (q ^ e)) * recF g (q ^ (m.factorization q - e))
        else (if e = 0 then (1 : ℝ) else 0) * recF g (q ^ (m.factorization q - e))) hp]
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hloc : ∑ e ∈ Icc 0 (m.factorization p),
          (if e = 0 then 0 else g (p ^ e)) * recF g (p ^ (m.factorization p - e)) =
          (m.factorization p : ℝ) * Real.log p * recF g (p ^ (m.factorization p)) := by
        rw [recF_ppow_rec g h0 h1 hp']
        refine sum_congr rfl fun e _ => ?_
        split_ifs with he
        · subst he; simp [h1]
        · rfl
      have hrest : ∀ q ∈ m.primeFactors.erase p, ∑ e ∈ Icc 0 (m.factorization q),
          (if q = p then (if e = 0 then 0 else g (q ^ e)) * recF g (q ^ (m.factorization q - e))
            else (if e = 0 then (1 : ℝ) else 0) * recF g (q ^ (m.factorization q - e))) = recF g (q ^ (m.factorization q)) := by
        intro q hq
        simp only [if_neg (mem_erase.1 hq).1]
        rw [sum_eq_single 0]
        · simp
        · intro e _ he; rw [if_neg he, zero_mul]
        · intro h; exact absurd (mem_Icc.2 ⟨le_rfl, Nat.zero_le _⟩) h
      simp only [ite_true] at hloc ⊢
      rw [hloc, prod_congr rfl hrest, ← mul_prod_erase m.primeFactors (fun q => recF g (q ^ (m.factorization q))) hp]
      ring
  rw [← key n, hFapp n hn]

end RamanujanTau.QFProof4
