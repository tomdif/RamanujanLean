/-
# `SvStripC`: the Euler-product structure of `Γ^z` (unconditional)

**`Γz_eq_prod`**: for `d, u₁, u₂ ≠ 0` and a set of primes `S ⊇` primes of `u₁u₂d`,

    Γz z d u₁ u₂ = Π_{p∈S} γz z p (v_p d) (v_p u₁) (v_p u₂),

the twisted copy of `QFProof4.Γc_eq_prod`.  Also `UdC_eq_prod`, `tw_eq_prod`.  Level 1.
-/
import RamanujanTau.SvStripC.Defs
import RamanujanTau.QFProof4.GammaMult

set_option autoImplicit false

namespace RamanujanTau.SvStripC

open Complex Finset
open RamanujanTau.SvStripA (UdC LcC LcC_zero_zero natCast_prod_cpow natCast_pow_cpow
  sum_divisors_prod_localR')
open RamanujanTau.QFProof3 (Fi)
open RamanujanTau.QFProof4 (alpha_eq_prod Fi_eq_prod')
open RamanujanTau.SelbergCoeffs (alpha)

lemma vanish_off' {n p : ℕ} (h : p ∉ n.primeFactors) : n.factorization p = 0 :=
  Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])

/-- `m^{iz} = Π_{p∈S} (p^{iz})^{v_p m}`. -/
lemma tw_eq_prod (z : ℂ) {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    tw z n = ∏ p ∈ S, tw z p ^ (n.factorization p) := by
  unfold tw
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, natCast_prod_cpow]
  simp_rw [natCast_pow_cpow]
  exact prod_subset hS fun p _ hpm => by rw [vanish_off' hpm, pow_zero]

lemma UdC_eq_prod (s : ℂ) {h d : ℕ} (hh : h ≠ 0) (hd : d ≠ 0) {S : Finset ℕ}
    (hS : h.primeFactors ∪ d.primeFactors ⊆ S) :
    UdC s h d = ∏ p ∈ S, LcC s p (h.factorization p) (d.factorization p) := by
  unfold UdC
  split_ifs with hdh
  · refine prod_subset (subset_union_left.trans hS) fun p hp hph => ?_
    have e1 := vanish_off' hph
    have e2 : d.factorization p = 0 := by
      have := (Nat.factorization_le_iff_dvd hd hh).2 hdh p; omega
    rw [e1, e2, LcC_zero_zero]
  · symm
    have : ¬ d.factorization ≤ h.factorization := fun hle =>
      hdh ((Nat.factorization_le_iff_dvd hd hh).1 hle)
    rw [Finsupp.le_def] at this
    push Not at this
    obtain ⟨p, hp⟩ := this
    have hpd : p ∈ d.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 (by omega)
    refine prod_eq_zero (hS (mem_union_right _ hpd)) ?_
    simp [LcC, hp]

lemma ofReal_alpha_eq_prod {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    ((alpha n : ℝ) : ℂ) = ∏ p ∈ S, ((alpha (p ^ n.factorization p) : ℝ) : ℂ) := by
  rw [alpha_eq_prod hn hS, ofReal_prod]

lemma ofReal_Fi_eq_prod {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    ((Fi n : ℝ) : ℂ) = ∏ p ∈ S, ((Fi (p ^ n.factorization p) : ℝ) : ℂ) := by
  rw [Fi_eq_prod' hn hS, ofReal_prod]

/-- **Euler product of the twisted `Γ`.** -/
theorem Γz_eq_prod (z : ℂ) {d u₁ u₂ : ℕ} (hd : d ≠ 0) (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) {S : Finset ℕ}
    (hS₁ : u₁.primeFactors ⊆ S) (hS₂ : u₂.primeFactors ⊆ S) (hSd : d.primeFactors ⊆ S) :
    Γz z d u₁ u₂ = ∏ p ∈ S, γz z p (d.factorization p) (u₁.factorization p) (u₂.factorization p) := by
  unfold Γz
  have hterm : ∀ v₁ ∈ u₁.divisors, ∀ v₂ ∈ u₂.divisors,
      ((alpha v₁ * alpha v₂ : ℝ) : ℂ) * Gz z d v₁ v₂ * Fiz z (u₁ / v₁) * (Fi (u₂ / v₂) : ℂ) =
      ∏ p ∈ S, (((alpha (p ^ v₁.factorization p) * alpha (p ^ v₂.factorization p) : ℝ) : ℂ) *
        tw (-z) p ^ v₂.factorization p *
        LcC (1 - z * I) p (v₁.factorization p + v₂.factorization p) (d.factorization p) *
        ((Fi (p ^ (u₁.factorization p - v₁.factorization p)) : ℂ) *
          tw z p ^ (u₁.factorization p - v₁.factorization p)) *
        (Fi (p ^ (u₂.factorization p - v₂.factorization p)) : ℂ)) := by
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
    have t1 : (u₁ / v₁).primeFactors ⊆ S := (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₁) h₁).trans hS₁
    have t2 : (u₂ / v₂).primeFactors ⊆ S := (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₂) h₂).trans hS₂
    unfold Gz Fiz
    rw [ofReal_mul, ofReal_alpha_eq_prod v₁0 s1, ofReal_alpha_eq_prod v₂0 s2,
      tw_eq_prod (-z) v₂0 s2,
      UdC_eq_prod _ (mul_ne_zero v₁0 v₂0) hd (union_subset (by
        rw [Nat.primeFactors_mul v₁0 v₂0]; exact union_subset s1 s2) hSd),
      ofReal_Fi_eq_prod q₁0 t1, tw_eq_prod z q₁0 t1, ofReal_Fi_eq_prod q₂0 t2]
    simp only [← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_mul v₁0 v₂0, Nat.factorization_div hd₁, Nat.factorization_div hd₂]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, ofReal_mul]
    ring
  rw [sum_congr rfl fun v₁ hv₁ => sum_congr rfl fun v₂ hv₂ => hterm v₁ hv₁ v₂ hv₂]
  rw [sum_congr rfl fun (v₁ : ℕ) _ => sum_divisors_prod_localR' h₂ hS₂ (fun p b =>
    ((alpha (p ^ v₁.factorization p) * alpha (p ^ b) : ℝ) : ℂ) * tw (-z) p ^ b *
      LcC (1 - z * I) p (v₁.factorization p + b) (d.factorization p) *
      ((Fi (p ^ (u₁.factorization p - v₁.factorization p)) : ℂ) *
        tw z p ^ (u₁.factorization p - v₁.factorization p)) *
      (Fi (p ^ (u₂.factorization p - b)) : ℂ))]
  rw [sum_divisors_prod_localR' h₁ hS₁ (fun p a => ∑ b ∈ Icc 0 (u₂.factorization p),
    ((alpha (p ^ a) * alpha (p ^ b) : ℝ) : ℂ) * tw (-z) p ^ b *
      LcC (1 - z * I) p (a + b) (d.factorization p) *
      ((Fi (p ^ (u₁.factorization p - a)) : ℂ) * tw z p ^ (u₁.factorization p - a)) *
      (Fi (p ^ (u₂.factorization p - b)) : ℂ))]
  rfl

end RamanujanTau.SvStripC
