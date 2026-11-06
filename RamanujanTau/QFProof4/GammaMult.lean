/-
# Multiplicativity of the canonical `Γ` in the pair `(u₁,u₂)` (unconditional)

`γ p e i j = Σ_{i'≤i, j'≤j} α(p^{i'})α(p^{j'}) L_p(i'+j', e) Fi(p^{i−i'}) Fi(p^{j−j'})`.

* **`Γc_eq_prod`**: `Γc Ud d u₁ u₂ = Π_{p∈S} γ p (v_p d) (v_p u₁) (v_p u₂)` for `S ⊇` the primes of `u₁u₂d`;
* **`Mass_le_prod`**: `Σ_{u₁,u₂≤y} |Γc Ud d u₁ u₂| ≤ Π_{p∈S} T p (v_p d) (v_p y!)`, `S = primes(y!) ∪ primes(d)`,
  with `T p e N = Σ_{i,j≤N} |γ p e i j|`.
-/
import RamanujanTau.QFProof4.LocalFi

set_option autoImplicit false

namespace RamanujanTau.QFProof4

open Finset ArithmeticFunction RamanujanTau.QFProof RamanujanTau.QFProof3 RamanujanTau.QFProof2
open RamanujanTau.SelbergCoeffs (alpha alpha_ppow alpha_one ofLocal_apply)
open RamanujanTau.SelbergDelange3 (recF recF_one)

/-- The local factor of `Γc Ud`. -/
noncomputable def γl (p e i j : ℕ) : ℝ :=
  ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j, alpha (p ^ a) * alpha (p ^ b) * Lc p (a + b) e *
    Fi (p ^ (i - a)) * Fi (p ^ (j - b))

lemma Fi_one : Fi 1 = 1 := by simp [Fi_apply, recF_one]

lemma alpha_eq_prod {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    alpha n = ∏ p ∈ S, alpha (p ^ n.factorization p) := by
  have h1 : alpha n = ∏ p ∈ n.primeFactors, alpha (p ^ n.factorization p) := by
    rw [RamanujanTau.SelbergCoeffs.alpha, ofLocal_apply _ hn, Finsupp.prod, Nat.support_factorization]
    refine prod_congr rfl fun p hp => ?_
    rw [← alpha_ppow (Nat.prime_of_mem_primeFactors hp)]
    rfl
  rw [h1]
  exact prod_subset hS fun p _ hp => by rw [vanish_off hp, pow_zero, alpha_one]

lemma Fi_eq_prod' {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    Fi n = ∏ p ∈ S, Fi (p ^ n.factorization p) := by
  rw [Fi_eq_prod n hn]
  exact prod_subset hS fun p _ hp => by rw [vanish_off hp, pow_zero, Fi_one]

lemma Ud_eq_prod {h d : ℕ} (hh : h ≠ 0) (hd : d ≠ 0) {S : Finset ℕ}
    (hS : h.primeFactors ∪ d.primeFactors ⊆ S) (hSp : ∀ p ∈ S, p.Prime) :
    Ud h d = ∏ p ∈ S, Lc p (h.factorization p) (d.factorization p) := by
  unfold Ud
  split_ifs with hdh
  · refine prod_subset (subset_union_left.trans hS) fun p hp hph => ?_
    have e1 := vanish_off hph
    have e2 : d.factorization p = 0 := by
      have := (Nat.factorization_le_iff_dvd hd hh).2 hdh p; omega
    rw [e1, e2, Lc_zero_zero (hSp p hp)]
  · symm
    have : ¬ d.factorization ≤ h.factorization := fun hle =>
      hdh ((Nat.factorization_le_iff_dvd hd hh).1 hle)
    rw [Finsupp.le_def] at this
    push Not at this
    obtain ⟨p, hp⟩ := this
    have hpd : p ∈ d.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 (by omega)
    refine prod_eq_zero (hS (mem_union_right _ hpd)) ?_
    simp [Lc, hp]

theorem Γc_eq_prod {d u₁ u₂ : ℕ} (hd : d ≠ 0) (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) {S : Finset ℕ}
    (hS₁ : u₁.primeFactors ⊆ S) (hS₂ : u₂.primeFactors ⊆ S) (hSd : d.primeFactors ⊆ S)
    (hSp : ∀ p ∈ S, p.Prime) :
    Γc Ud d u₁ u₂ = ∏ p ∈ S, γl p (d.factorization p) (u₁.factorization p) (u₂.factorization p) := by
  unfold Γc
  have hterm : ∀ v₁ ∈ u₁.divisors, ∀ v₂ ∈ u₂.divisors,
      alpha v₁ * alpha v₂ * Ud (v₁ * v₂) d * Fi (u₁ / v₁) * Fi (u₂ / v₂) =
      ∏ p ∈ S, (alpha (p ^ v₁.factorization p) * alpha (p ^ v₂.factorization p) *
        Lc p (v₁.factorization p + v₂.factorization p) (d.factorization p) *
        Fi (p ^ (u₁.factorization p - v₁.factorization p)) *
        Fi (p ^ (u₂.factorization p - v₂.factorization p))) := by
    intro v₁ hv₁ v₂ hv₂
    have hd₁ := Nat.dvd_of_mem_divisors hv₁
    have hd₂ := Nat.dvd_of_mem_divisors hv₂
    have v₁0 : v₁ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₁)
    have v₂0 : v₂ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₂)
    have s1 : v₁.primeFactors ⊆ S := (Nat.primeFactors_mono hd₁ h₁).trans hS₁
    have s2 : v₂.primeFactors ⊆ S := (Nat.primeFactors_mono hd₂ h₂).trans hS₂
    have q₁0 : u₁ / v₁ ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h₁) hd₁)
      (Nat.pos_of_ne_zero v₁0))
    have q₂0 : u₂ / v₂ ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h₂) hd₂)
      (Nat.pos_of_ne_zero v₂0))
    rw [alpha_eq_prod v₁0 s1, alpha_eq_prod v₂0 s2,
      Ud_eq_prod (mul_ne_zero v₁0 v₂0) hd (union_subset (by
        rw [Nat.primeFactors_mul v₁0 v₂0]; exact union_subset s1 s2) hSd) hSp,
      Fi_eq_prod' q₁0 ((Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₁) h₁).trans hS₁),
      Fi_eq_prod' q₂0 ((Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₂) h₂).trans hS₂),
      ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_mul v₁0 v₂0, Nat.factorization_div hd₁, Nat.factorization_div hd₂]
    rfl
  rw [sum_congr rfl fun v₁ hv₁ => sum_congr rfl fun v₂ hv₂ => hterm v₁ hv₁ v₂ hv₂]
  rw [sum_congr rfl fun (v₁ : ℕ) _ => sum_divisors_prod_local' h₂ hS₂ (fun p b => alpha (p ^ v₁.factorization p) *
    alpha (p ^ b) * Lc p (v₁.factorization p + b) (d.factorization p) *
    Fi (p ^ (u₁.factorization p - v₁.factorization p)) * Fi (p ^ (u₂.factorization p - b)))]
  rw [sum_divisors_prod_local' h₁ hS₁ (fun p a => ∑ b ∈ Icc 0 (u₂.factorization p),
    alpha (p ^ a) * alpha (p ^ b) * Lc p (a + b) (d.factorization p) *
    Fi (p ^ (u₁.factorization p - a)) * Fi (p ^ (u₂.factorization p - b)))]
  rfl

/-- `T p e N = Σ_{i,j≤N} |γ p e i j|`. -/
noncomputable def Tl (p e N : ℕ) : ℝ := ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, |γl p e i j|

theorem Mass_le_prod {y d : ℕ} (hy : 1 ≤ y) (hd : d ≠ 0) :
    Mass (Γc Ud) y d ≤ ∏ p ∈ (y.factorial).primeFactors ∪ d.primeFactors,
      Tl p (d.factorization p) ((y.factorial).factorization p) := by
  set S := (y.factorial).primeFactors ∪ d.primeFactors with hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    rcases mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hf0 : y.factorial ≠ 0 := Nat.factorial_ne_zero y
  have hsub : Ioc 0 y ⊆ (y.factorial).divisors := fun u hu => by
    have := mem_Ioc.1 hu
    exact Nat.mem_divisors.2 ⟨Nat.dvd_factorial this.1 this.2, hf0⟩
  unfold Mass
  calc ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, |Γc Ud d u₁ u₂|
      ≤ ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors, |Γc Ud d u₁ u₂| := by
        refine (sum_le_sum fun u₁ _ => sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => abs_nonneg _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sum_nonneg fun _ _ => abs_nonneg _
    _ = ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors,
          ∏ p ∈ S, |γl p (d.factorization p) (u₁.factorization p) (u₂.factorization p)| := by
        refine sum_congr rfl fun u₁ hu₁ => sum_congr rfl fun u₂ hu₂ => ?_
        have d₁ := Nat.dvd_of_mem_divisors hu₁
        have d₂ := Nat.dvd_of_mem_divisors hu₂
        rw [Γc_eq_prod hd (Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₁))
          (Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₂))
          ((Nat.primeFactors_mono d₁ hf0).trans subset_union_left)
          ((Nat.primeFactors_mono d₂ hf0).trans subset_union_left) subset_union_right hSp, abs_prod]
    _ = ∏ p ∈ S, Tl p (d.factorization p) ((y.factorial).factorization p) := by
        rw [sum_congr rfl fun (u₁ : ℕ) _ => sum_divisors_prod_local' hf0 subset_union_left
          (fun p j => |γl p (d.factorization p) (u₁.factorization p) j|)]
        rw [sum_divisors_prod_local' hf0 subset_union_left (fun p i => ∑ j ∈ Icc 0 ((y.factorial).factorization p),
          |γl p (d.factorization p) i j|)]
        rfl

end RamanujanTau.QFProof4
