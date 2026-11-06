/-
# The derivative columns: `Γc Vd` as a derivation sum of local factors (unconditional)

* `conv_prod`: the two-variable convolution of `α⊗α · Π_q K_q(v_q(v₁v₂), v_q d)` with `Fi⊗Fi`
  is `Π_q γK K q (v_q d)(v_q u₁)(v_q u₂)` (generic kernel `K`);
* `Vd_eq_sum`: `Vd h d = Σ_{p∈S} L'_p Π_{q≠p} L_q`;
* **`MassV_le`**: `Σ_{u₁,u₂≤y} |Γc Vd d u₁ u₂| ≤ Σ_{p∈S} T'_p Π_{q∈S, q≠p} T_q`.
-/
import RamanujanTau.QFProof4.GammaMult

set_option autoImplicit false

namespace RamanujanTau.QFProof4

open Finset ArithmeticFunction RamanujanTau.QFProof RamanujanTau.QFProof3 RamanujanTau.QFProof2
open RamanujanTau.SelbergCoeffs (alpha)

/-- The local factor for a generic kernel `K q a e`. -/
noncomputable def γK (K : ℕ → ℕ → ℕ → ℝ) (p e i j : ℕ) : ℝ :=
  ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j, alpha (p ^ a) * alpha (p ^ b) * K p (a + b) e *
    Fi (p ^ (i - a)) * Fi (p ^ (j - b))

theorem conv_prod (K : ℕ → ℕ → ℕ → ℝ) {d u₁ u₂ : ℕ} (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) {S : Finset ℕ}
    (hS₁ : u₁.primeFactors ⊆ S) (hS₂ : u₂.primeFactors ⊆ S) :
    ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, alpha v₁ * alpha v₂ *
      (∏ q ∈ S, K q (v₁.factorization q + v₂.factorization q) (d.factorization q)) *
      Fi (u₁ / v₁) * Fi (u₂ / v₂) =
    ∏ p ∈ S, γK K p (d.factorization p) (u₁.factorization p) (u₂.factorization p) := by
  have hterm : ∀ v₁ ∈ u₁.divisors, ∀ v₂ ∈ u₂.divisors, alpha v₁ * alpha v₂ *
      (∏ q ∈ S, K q (v₁.factorization q + v₂.factorization q) (d.factorization q)) *
      Fi (u₁ / v₁) * Fi (u₂ / v₂) =
      ∏ p ∈ S, (alpha (p ^ v₁.factorization p) * alpha (p ^ v₂.factorization p) *
        K p (v₁.factorization p + v₂.factorization p) (d.factorization p) *
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
      Fi_eq_prod' q₁0 ((Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₁) h₁).trans hS₁),
      Fi_eq_prod' q₂0 ((Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd₂) h₂).trans hS₂),
      ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_div hd₁, Nat.factorization_div hd₂]
    rfl
  rw [sum_congr rfl fun v₁ hv₁ => sum_congr rfl fun v₂ hv₂ => hterm v₁ hv₁ v₂ hv₂]
  rw [sum_congr rfl fun (v₁ : ℕ) _ => sum_divisors_prod_local' h₂ hS₂ (fun p b => alpha (p ^ v₁.factorization p) *
    alpha (p ^ b) * K p (v₁.factorization p + b) (d.factorization p) *
    Fi (p ^ (u₁.factorization p - v₁.factorization p)) * Fi (p ^ (u₂.factorization p - b)))]
  rw [sum_divisors_prod_local' h₁ hS₁ (fun p a => ∑ b ∈ Icc 0 (u₂.factorization p),
    alpha (p ^ a) * alpha (p ^ b) * K p (a + b) (d.factorization p) *
    Fi (p ^ (u₁.factorization p - a)) * Fi (p ^ (u₂.factorization p - b)))]
  rfl

lemma Lv_zero_zero' {p : ℕ} (hp : p.Prime) : Lv p 0 0 = 0 := Lv_zero_zero p (hp := hp)

lemma Vd_eq_sum {h d : ℕ} (hh : h ≠ 0) (hd : d ≠ 0) {S : Finset ℕ}
    (hS : h.primeFactors ∪ d.primeFactors ⊆ S) (hSp : ∀ p ∈ S, p.Prime) :
    Vd h d = ∑ p ∈ S, Lv p (h.factorization p) (d.factorization p) *
      ∏ q ∈ S.erase p, Lc q (h.factorization q) (d.factorization q) := by
  unfold Vd
  split_ifs with hdh
  · refine sum_erase_ext (subset_union_left.trans hS) (fun p => Lv p (h.factorization p) (d.factorization p))
      (fun q => Lc q (h.factorization q) (d.factorization q)) (fun q hq hqh => ?_) (fun q hq hqh => ?_)
    · have e2 : d.factorization q = 0 := by
        have := (Nat.factorization_le_iff_dvd hd hh).2 hdh q; have := vanish_off hqh; omega
      simp only [vanish_off hqh, e2]; exact Lv_zero_zero' (hSp q hq)
    · have e2 : d.factorization q = 0 := by
        have := (Nat.factorization_le_iff_dvd hd hh).2 hdh q; have := vanish_off hqh; omega
      simp only [vanish_off hqh, e2]; exact Lc_zero_zero (hSp q hq)
  · symm
    have : ¬ d.factorization ≤ h.factorization := fun hle =>
      hdh ((Nat.factorization_le_iff_dvd hd hh).1 hle)
    rw [Finsupp.le_def] at this
    push Not at this
    obtain ⟨p₀, hp₀⟩ := this
    have hpd : p₀ ∈ d.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 (by omega)
    refine sum_eq_zero fun p hp => ?_
    by_cases hpp : p = p₀
    · subst hpp; simp [Lv, hp₀]
    · refine mul_eq_zero_of_right _ (prod_eq_zero (mem_erase.2 ⟨Ne.symm hpp, hS (mem_union_right _ hpd)⟩) ?_)
      simp [Lc, hp₀]

/-- `T' p e N = Σ_{i,j≤N} |γ' p e i j|` (derivative columns). -/
noncomputable def TlV (p e N : ℕ) : ℝ := ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, |γK Lv p e i j|

lemma γK_Lc : γK Lc = γl := rfl

theorem MassV_le {y d : ℕ} (hd : d ≠ 0) :
    Mass (Γc Vd) y d ≤ ∑ p ∈ (y.factorial).primeFactors ∪ d.primeFactors,
      TlV p (d.factorization p) ((y.factorial).factorization p) *
      ∏ q ∈ ((y.factorial).primeFactors ∪ d.primeFactors).erase p,
        Tl q (d.factorization q) ((y.factorial).factorization q) := by
  set S := (y.factorial).primeFactors ∪ d.primeFactors with hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    rcases mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hf0 : y.factorial ≠ 0 := Nat.factorial_ne_zero y
  have hsub : Ioc 0 y ⊆ (y.factorial).divisors := fun u hu => by
    have := mem_Ioc.1 hu
    exact Nat.mem_divisors.2 ⟨Nat.dvd_factorial this.1 this.2, hf0⟩
  -- the kernel for the `p`-th derivative term
  set Kp : ℕ → ℕ → ℕ → ℕ → ℝ := fun p q a e => if q = p then Lv q a e else Lc q a e with hKp
  have hΓ : ∀ u₁ ∈ (y.factorial).divisors, ∀ u₂ ∈ (y.factorial).divisors,
      Γc Vd d u₁ u₂ = ∑ p ∈ S, ∏ q ∈ S, γK (Kp p) q (d.factorization q) (u₁.factorization q)
        (u₂.factorization q) := by
    intro u₁ hu₁ u₂ hu₂
    have h₁ : u₁ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₁)
    have h₂ : u₂ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hu₂)
    have s₁ : u₁.primeFactors ⊆ S := (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hu₁) hf0).trans
      subset_union_left
    have s₂ : u₂.primeFactors ⊆ S := (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hu₂) hf0).trans
      subset_union_left
    have hV : ∀ v₁ ∈ u₁.divisors, ∀ v₂ ∈ u₂.divisors, Vd (v₁ * v₂) d = ∑ p ∈ S,
        ∏ q ∈ S, Kp p q (v₁.factorization q + v₂.factorization q) (d.factorization q) := by
      intro v₁ hv₁ v₂ hv₂
      have v₁0 : v₁ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₁)
      have v₂0 : v₂ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv₂)
      have sv : (v₁ * v₂).primeFactors ⊆ S := by
        rw [Nat.primeFactors_mul v₁0 v₂0]
        exact union_subset ((Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hv₁) h₁).trans s₁)
          ((Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hv₂) h₂).trans s₂)
      rw [Vd_eq_sum (mul_ne_zero v₁0 v₂0) hd (union_subset sv subset_union_right) hSp]
      refine sum_congr rfl fun p hp => ?_
      rw [← mul_prod_erase S _ hp]
      simp only [hKp, if_true, Nat.factorization_mul v₁0 v₂0, Finsupp.add_apply]
      congr 1
      exact prod_congr rfl fun q hq => by rw [if_neg (mem_erase.1 hq).1]
    unfold Γc
    calc ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, alpha v₁ * alpha v₂ * Vd (v₁ * v₂) d *
          Fi (u₁ / v₁) * Fi (u₂ / v₂)
        = ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, ∑ p ∈ S, alpha v₁ * alpha v₂ *
          (∏ q ∈ S, Kp p q (v₁.factorization q + v₂.factorization q) (d.factorization q)) *
          Fi (u₁ / v₁) * Fi (u₂ / v₂) := by
          refine sum_congr rfl fun v₁ hv₁ => sum_congr rfl fun v₂ hv₂ => ?_
          rw [hV v₁ hv₁ v₂ hv₂, mul_sum, sum_mul, sum_mul]
      _ = ∑ p ∈ S, ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, alpha v₁ * alpha v₂ *
          (∏ q ∈ S, Kp p q (v₁.factorization q + v₂.factorization q) (d.factorization q)) *
          Fi (u₁ / v₁) * Fi (u₂ / v₂) := by
          rw [sum_congr rfl fun v₁ _ => sum_comm, sum_comm]
      _ = _ := sum_congr rfl fun p _ => conv_prod (Kp p) h₁ h₂ s₁ s₂
  have hK : ∀ p q e i j, γK (Kp p) q e i j = if q = p then γK Lv q e i j else γl q e i j := by
    intro p q e i j
    split_ifs with hqp
    · subst hqp; unfold γK; simp [hKp]
    · unfold γK γl; simp [hKp, hqp]
  unfold Mass
  calc ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, |Γc Vd d u₁ u₂|
      ≤ ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors, |Γc Vd d u₁ u₂| := by
        refine (sum_le_sum fun u₁ _ => sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => abs_nonneg _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sum_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors, ∑ p ∈ S,
          ∏ q ∈ S, |γK (Kp p) q (d.factorization q) (u₁.factorization q) (u₂.factorization q)| := by
        refine sum_le_sum fun u₁ hu₁ => sum_le_sum fun u₂ hu₂ => ?_
        rw [hΓ u₁ hu₁ u₂ hu₂]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun p _ => abs_prod _ _
    _ = ∑ p ∈ S, ∑ u₁ ∈ (y.factorial).divisors, ∑ u₂ ∈ (y.factorial).divisors,
          ∏ q ∈ S, |γK (Kp p) q (d.factorization q) (u₁.factorization q) (u₂.factorization q)| := by
        rw [sum_congr rfl fun u₁ _ => sum_comm, sum_comm]
    _ = ∑ p ∈ S, ∏ q ∈ S, ∑ i ∈ Icc 0 ((y.factorial).factorization q),
          ∑ j ∈ Icc 0 ((y.factorial).factorization q), |γK (Kp p) q (d.factorization q) i j| := by
        refine sum_congr rfl fun p _ => ?_
        rw [sum_congr rfl fun (u₁ : ℕ) _ => sum_divisors_prod_local' hf0 subset_union_left
          (fun q j => |γK (Kp p) q (d.factorization q) (u₁.factorization q) j|)]
        rw [sum_divisors_prod_local' hf0 subset_union_left (fun q i => ∑ j ∈ Icc 0 ((y.factorial).factorization q),
          |γK (Kp p) q (d.factorization q) i j|)]
    _ = _ := by
        refine sum_congr rfl fun p hp => ?_
        rw [← mul_prod_erase S _ hp]
        simp only [hK, if_true]
        congr 1
        exact prod_congr rfl fun q hq => by simp only [if_neg (mem_erase.1 hq).1]; rfl

end RamanujanTau.QFProof4
