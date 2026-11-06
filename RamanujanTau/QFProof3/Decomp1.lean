/-
# `QDecomp1` for the explicit derivative data (unconditional)

`W1d d = (γ_R/r₀) W(d) + Σ_{p|d} log p · wd_p(v_p d) Π_{q|d, q≠p} W_q(v_q d)`,
`Vd h d = 1_{d|h} Σ_{p|h} L'_p(v_p h, v_p d) Π_{q|h, q≠p} L_q(v_q h, v_q d)`.

**`qDecomp1`**: `QFProof.QDecomp1 Wd W1d Ud Vd`.
-/
import RamanujanTau.QFProof3.DLocal

set_option autoImplicit false

namespace RamanujanTau.QFProof3

open Finset RamanujanTau.HafnerBridge RamanujanTau.QFProof RamanujanTau.QFProof2

noncomputable def W1d (d : ℕ) : ℝ :=
  gamR * Wd d + ∑ p ∈ d.primeFactors, Real.log p * wd (lam p) (Xp p) (d.factorization p) *
    ∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q)

noncomputable def Vd (h d : ℕ) : ℝ :=
  if d ∣ h then ∑ p ∈ h.primeFactors, Lv p (h.factorization p) (d.factorization p) *
    ∏ q ∈ h.primeFactors.erase p, Lc q (h.factorization q) (d.factorization q) else 0

/-! ### Product rules -/

lemma prod_rule3 (S : Finset ℕ) (x y z x' y' z' : ℕ → ℝ) :
    (∑ p ∈ S, x' p * ∏ q ∈ S.erase p, x q) * (∏ q ∈ S, y q) * (∏ q ∈ S, z q) +
      (∏ q ∈ S, x q) * ((∑ p ∈ S, y' p * ∏ q ∈ S.erase p, y q) * (∏ q ∈ S, z q) +
        (∏ q ∈ S, y q) * (∑ p ∈ S, z' p * ∏ q ∈ S.erase p, z q)) =
      ∑ p ∈ S, (x' p * y p * z p + x p * (y' p * z p + y p * z' p)) *
        ∏ q ∈ S.erase p, (x q * y q * z q) := by
  have hA : (∑ p ∈ S, x' p * ∏ q ∈ S.erase p, x q) * (∏ q ∈ S, y q) * (∏ q ∈ S, z q) =
      ∑ p ∈ S, x' p * y p * z p * ∏ q ∈ S.erase p, (x q * y q * z q) := by
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_prod_erase S y hp, ← mul_prod_erase S z hp, prod_mul_distrib, prod_mul_distrib]; ring
  have hB : (∏ q ∈ S, x q) * ((∑ p ∈ S, y' p * ∏ q ∈ S.erase p, y q) * (∏ q ∈ S, z q)) =
      ∑ p ∈ S, x p * y' p * z p * ∏ q ∈ S.erase p, (x q * y q * z q) := by
    rw [sum_mul, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_prod_erase S x hp, ← mul_prod_erase S z hp, prod_mul_distrib, prod_mul_distrib]; ring
  have hC : (∏ q ∈ S, x q) * ((∏ q ∈ S, y q) * (∑ p ∈ S, z' p * ∏ q ∈ S.erase p, z q)) =
      ∑ p ∈ S, x p * y p * z' p * ∏ q ∈ S.erase p, (x q * y q * z q) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_prod_erase S x hp, ← mul_prod_erase S y hp, prod_mul_distrib, prod_mul_distrib]; ring
  rw [mul_add, hA, hB, hC, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by ring

lemma prod_rule2 (S : Finset ℕ) (u v u' v' : ℕ → ℝ) :
    (∑ p ∈ S, u' p * ∏ q ∈ S.erase p, u q) * (∏ q ∈ S, v q) +
      (∏ q ∈ S, u q) * (∑ p ∈ S, v' p * ∏ q ∈ S.erase p, v q) =
      ∑ p ∈ S, (u' p * v p + u p * v' p) * ∏ q ∈ S.erase p, (u q * v q) := by
  have hA : (∑ p ∈ S, u' p * ∏ q ∈ S.erase p, u q) * (∏ q ∈ S, v q) =
      ∑ p ∈ S, u' p * v p * ∏ q ∈ S.erase p, (u q * v q) := by
    rw [sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_prod_erase S v hp, prod_mul_distrib]; ring
  have hB : (∏ q ∈ S, u q) * (∑ p ∈ S, v' p * ∏ q ∈ S.erase p, v q) =
      ∑ p ∈ S, u p * v' p * ∏ q ∈ S.erase p, (u q * v q) := by
    rw [mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_prod_erase S u hp, prod_mul_distrib]; ring
  rw [hA, hB, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by ring

lemma vanish_off {m : ℕ} {p : ℕ} (hp : p ∉ m.primeFactors) : m.factorization p = 0 :=
  Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])

lemma rho1_eq {m : ℕ} {S : Finset ℕ} (hS : m.primeFactors ⊆ S) (hSp : ∀ p ∈ S, p.Prime) :
    rho1 m = ∑ p ∈ S, rhoP' p (m.factorization p) * ∏ q ∈ S.erase p, rhoP q (m.factorization q) := by
  unfold rho1
  have hin : ∀ p ∈ m.primeFactors, ∏ q ∈ m.primeFactors.erase p, rhoP q (m.factorization q) =
      ∏ q ∈ S.erase p, rhoP q (m.factorization q) := fun p _ =>
    prod_subset (erase_subset_erase p hS) fun q hq hq' => by
      have : q ∉ m.primeFactors := fun h => hq' (mem_erase.2 ⟨(mem_erase.1 hq).1, h⟩)
      rw [vanish_off this, rhoP_zero (hSp q (mem_erase.1 hq).2)]
  rw [sum_congr rfl fun p hp => by rw [hin p hp]]
  refine sum_subset hS fun p hp hpm => ?_
  rw [vanish_off hpm, rhoP'_zero (hSp p hp), zero_mul]

lemma log_eq_sum {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    Real.log n = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · rw [sum_subset hS fun p _ hpm => by rw [vanish_off hpm]; simp]
    refine sum_congr rfl fun p _ => ?_
    push_cast; rw [Real.log_pow]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

/-- The local kernel `κ_p(a,b) = X^{max} ρ_p(|a−b|)`. -/
noncomputable def kap (p a b : ℕ) : ℝ := Xp p ^ (max a b) * rhoP p (dist' a b)

/-- `Kq1 = γ Kq + Σ_p κ'_p Π_{q≠p} κ_q`. -/
lemma Kq1_prod {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Kq1 h k = gamR * Kq h k + ∑ p ∈ (h * k).primeFactors,
      kd p (h.factorization p) (k.factorization p) *
        ∏ q ∈ ((h * k).primeFactors).erase p, kap q (h.factorization q) (k.factorization q) := by
  set S := (h * k).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : h ≠ 0 := hh.ne'
  have k0 : k ≠ 0 := hk.ne'
  have hS : S = h.primeFactors ∪ k.primeFactors := Nat.primeFactors_mul h0 k0
  have hg := Nat.gcd_dvd_left h k
  have hg' := Nat.gcd_dvd_right h k
  have hsub1 : (h / Nat.gcd h k).primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hg) h0).trans subset_union_left
  have hsub2 : (k / Nat.gcd h k).primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hg') k0).trans subset_union_right
  have hl0 : Nat.lcm h k ≠ 0 := Nat.lcm_ne_zero h0 k0
  have hsub3 : (Nat.lcm h k).primeFactors ⊆ S :=
    Nat.primeFactors_mono (Nat.lcm_dvd_mul h k) (mul_ne_zero h0 k0)
  set h₁ := h / Nat.gcd h k
  set k₁ := k / Nat.gcd h k
  have h10 : h₁ ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hh hg) (Nat.gcd_pos_of_pos_left k hh))
  have k10 : k₁ ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hk hg') (Nat.gcd_pos_of_pos_left k hh))
  have hsub4 : (h₁ * k₁).primeFactors ⊆ S := by
    rw [Nat.primeFactors_mul h10 k10]; exact union_subset hsub1 hsub2
  -- local exponents
  have ha : ∀ p, h₁.factorization p = h.factorization p - min (h.factorization p) (k.factorization p) := by
    intro p; rw [Nat.factorization_div hg, Nat.factorization_gcd h0 k0]; rfl
  have hb : ∀ p, k₁.factorization p = k.factorization p - min (h.factorization p) (k.factorization p) := by
    intro p; rw [Nat.factorization_div hg', Nat.factorization_gcd h0 k0]; rfl
  have hlcm : ∀ p, (Nat.lcm h k).factorization p = max (h.factorization p) (k.factorization p) := by
    intro p; rw [Nat.factorization_lcm h0 k0]; rfl
  have hloc0 : ∀ p ∈ S, rhoP p (h₁.factorization p) * rhoP p (k₁.factorization p) =
      rhoP p (dist' (h.factorization p) (k.factorization p)) := by
    intro p hp
    rw [ha, hb]; unfold dist'
    split_ifs with hab
    · rw [min_eq_left hab, Nat.sub_self, rhoP_zero (hSp p hp), one_mul]
    · rw [min_eq_right (by omega), Nat.sub_self, rhoP_zero (hSp p hp), mul_one]
  have hloc1 : ∀ p ∈ S, rhoP' p (h₁.factorization p) * rhoP p (k₁.factorization p) +
      rhoP p (h₁.factorization p) * rhoP' p (k₁.factorization p) =
      rhoP' p (dist' (h.factorization p) (k.factorization p)) := by
    intro p hp
    rw [ha, hb]; unfold dist'
    split_ifs with hab
    · rw [min_eq_left hab, Nat.sub_self, rhoP_zero (hSp p hp), rhoP'_zero (hSp p hp)]; ring
    · rw [min_eq_right (by omega), Nat.sub_self, rhoP_zero (hSp p hp), rhoP'_zero (hSp p hp)]; ring
  have hdist : ∀ p, ((h₁ * k₁).factorization p : ℝ) =
      (dist' (h.factorization p) (k.factorization p) : ℝ) := by
    intro p
    rw [Nat.factorization_mul h10 k10, Finsupp.add_apply, ha, hb]; unfold dist'
    split_ifs with hab
    · rw [min_eq_left hab, Nat.sub_self, zero_add]
    · rw [min_eq_right (by omega), Nat.sub_self, add_zero]
  -- assemble
  have hX := inv_cast_eq_prod hl0 hsub3
  have hρ1 := rho_eq_prod hsub1 hSp
  have hρ2 := rho_eq_prod hsub2 hSp
  have hd1 := rho1_eq hsub1 hSp
  have hd2 := rho1_eq hsub2 hSp
  have hL := log_eq_sum (mul_ne_zero h10 k10) hsub4
  have hKq : Kq h k = rho h₁ * rho k₁ * ((Nat.lcm h k : ℝ))⁻¹ := by unfold Kq; rw [div_eq_mul_inv]
  have hpr := prod_rule2 S (fun q => rhoP q (h₁.factorization q)) (fun q => rhoP q (k₁.factorization q))
    (fun q => rhoP' q (h₁.factorization q)) (fun q => rhoP' q (k₁.factorization q))
  unfold Kq1
  rw [hKq, div_eq_mul_inv]
  have key : rho h₁ * rho k₁ * (gamR - 1 / 2 * Real.log ((h₁ * k₁ : ℕ) : ℝ)) + rho1 h₁ * rho k₁ +
      rho h₁ * rho1 k₁ = gamR * (rho h₁ * rho k₁) +
      ∑ p ∈ S, (-(1 / 2) * (dist' (h.factorization p) (k.factorization p) : ℝ) * Real.log p *
        rhoP p (dist' (h.factorization p) (k.factorization p)) +
        rhoP' p (dist' (h.factorization p) (k.factorization p))) *
        ∏ q ∈ S.erase p, rhoP q (dist' (h.factorization q) (k.factorization q)) := by
    have e1 : rho1 h₁ * rho k₁ + rho h₁ * rho1 k₁ = ∑ p ∈ S,
        rhoP' p (dist' (h.factorization p) (k.factorization p)) *
          ∏ q ∈ S.erase p, rhoP q (dist' (h.factorization q) (k.factorization q)) := by
      rw [hd1, hd2, hρ1, hρ2, hpr]
      refine sum_congr rfl fun p hp => ?_
      rw [hloc1 p hp]
      congr 1
      exact prod_congr rfl fun q hq => hloc0 q (mem_erase.1 hq).2
    have e2 : rho h₁ * rho k₁ = ∏ q ∈ S, rhoP q (dist' (h.factorization q) (k.factorization q)) := by
      rw [hρ1, hρ2, ← prod_mul_distrib]
      exact prod_congr rfl fun q hq => hloc0 q hq
    have e3 : Real.log ((h₁ * k₁ : ℕ) : ℝ) * (rho h₁ * rho k₁) = ∑ p ∈ S,
        ((dist' (h.factorization p) (k.factorization p) : ℝ) * Real.log p *
          rhoP p (dist' (h.factorization p) (k.factorization p))) *
          ∏ q ∈ S.erase p, rhoP q (dist' (h.factorization q) (k.factorization q)) := by
      rw [hL, e2, sum_mul]
      refine sum_congr rfl fun p hp => ?_
      rw [hdist p, ← mul_prod_erase S _ hp]; ring
    have : rho h₁ * rho k₁ * (gamR - 1 / 2 * Real.log ((h₁ * k₁ : ℕ) : ℝ)) + rho1 h₁ * rho k₁ +
        rho h₁ * rho1 k₁ = gamR * (rho h₁ * rho k₁) - 1 / 2 * (Real.log ((h₁ * k₁ : ℕ) : ℝ) *
        (rho h₁ * rho k₁)) + (rho1 h₁ * rho k₁ + rho h₁ * rho1 k₁) := by ring
    rw [this, e1, e3, mul_sum, sub_eq_add_neg, ← sum_neg_distrib, add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun p _ => by ring
  rw [key, add_mul, hX]
  simp only [hlcm]
  congr 1
  · ring
  rw [sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← mul_prod_erase S (fun q => Xp q ^ max (h.factorization q) (k.factorization q)) hp]
  unfold kd kap
  rw [prod_mul_distrib]
  ring

lemma sum_erase_ext {T S : Finset ℕ} (hTS : T ⊆ S) (G F : ℕ → ℝ)
    (hG : ∀ q ∈ S, q ∉ T → G q = 0) (hF : ∀ q ∈ S, q ∉ T → F q = 1) :
    ∑ p ∈ T, G p * ∏ q ∈ T.erase p, F q = ∑ p ∈ S, G p * ∏ q ∈ S.erase p, F q := by
  have hin : ∀ p ∈ T, ∏ q ∈ T.erase p, F q = ∏ q ∈ S.erase p, F q := fun p _ =>
    prod_subset (erase_subset_erase p hTS) fun q hq hq' =>
      hF q (mem_erase.1 hq).2 fun h => hq' (mem_erase.2 ⟨(mem_erase.1 hq).1, h⟩)
  rw [sum_congr rfl fun p hp => by rw [hin p hp]]
  exact sum_subset hTS fun p hp hpT => by rw [hG p hp hpT, zero_mul]

/-- **`QDecomp1 Wd W1d Ud Vd`.** -/
theorem qDecomp1 : QDecomp1 Wd W1d Ud Vd := by
  refine ⟨fun h d hd => by simp [Vd, hd], fun h k hh hk => ?_⟩
  set g := Nat.gcd h k with hgdef
  set S := (h * k).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : h ≠ 0 := hh.ne'
  have k0 : k ≠ 0 := hk.ne'
  have g0 : g ≠ 0 := Nat.gcd_ne_zero_left h0
  have hS : S = h.primeFactors ∪ k.primeFactors := Nat.primeFactors_mul h0 k0
  have hgS : g.primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.gcd_dvd_left h k) h0).trans subset_union_left
  set W' : ℕ → ℝ := fun d => ∑ p ∈ d.primeFactors, Real.log p * wd (lam p) (Xp p) (d.factorization p) *
    ∏ q ∈ d.primeFactors.erase p, Wc (lam q) (Xp q) (d.factorization q) with hW'
  have hsplit : ∑ d ∈ h.divisors, (W1d d * Ud h d * Ud k d + Wd d * (Vd h d * Ud k d + Ud h d * Vd k d)) =
      gamR * ∑ d ∈ h.divisors, Wd d * Ud h d * Ud k d +
      ∑ d ∈ g.divisors, (W' d * Ud h d * Ud k d + Wd d * (Vd h d * Ud k d + Ud h d * Vd k d)) := by
    rw [mul_sum]
    have hres : ∑ d ∈ h.divisors, (W' d * Ud h d * Ud k d + Wd d * (Vd h d * Ud k d + Ud h d * Vd k d)) =
        ∑ d ∈ g.divisors, (W' d * Ud h d * Ud k d + Wd d * (Vd h d * Ud k d + Ud h d * Vd k d)) := by
      symm
      refine sum_subset (Nat.divisors_subset_of_dvd h0 (Nat.gcd_dvd_left h k)) fun d hd hdg => ?_
      have hdh := Nat.dvd_of_mem_divisors hd
      have : ¬ d ∣ k := fun hdk => hdg (Nat.mem_divisors.2 ⟨Nat.dvd_gcd hdh hdk, g0⟩)
      simp [Ud, Vd, this]
    rw [← hres, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    simp only [W1d, hW']; ring
  rw [hsplit, ← qDecomp.2 h k hh hk, Kq1_prod hh hk]
  congr 1
  -- the local data at `p`
  set ψ : ℕ → ℕ → ℝ := fun q e => Wc (lam q) (Xp q) e * Lc q (h.factorization q) e *
    Lc q (k.factorization q) e with hψ
  set ψ' : ℕ → ℕ → ℝ := fun q e => Real.log q * wd (lam q) (Xp q) e * Lc q (h.factorization q) e *
    Lc q (k.factorization q) e + Wc (lam q) (Xp q) e * (Lv q (h.factorization q) e *
      Lc q (k.factorization q) e + Lc q (h.factorization q) e * Lv q (k.factorization q) e) with hψ'
  have hterm : ∀ d ∈ g.divisors, W' d * Ud h d * Ud k d + Wd d * (Vd h d * Ud k d + Ud h d * Vd k d) =
      ∑ p ∈ S, ψ' p (d.factorization p) * ∏ q ∈ S.erase p, ψ q (d.factorization q) := by
    intro d hd
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdh : d ∣ h := hdg.trans (Nat.gcd_dvd_left h k)
    have hdk : d ∣ k := hdg.trans (Nat.gcd_dvd_right h k)
    have d0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdS : d.primeFactors ⊆ S := (Nat.primeFactors_mono hdg g0).trans hgS
    have hv : ∀ m : ℕ, m ≠ 0 → d ∣ m → ∀ q, q ∉ m.primeFactors →
        m.factorization q = 0 ∧ d.factorization q = 0 := by
      intro m m0 hdm q hq
      have hm := vanish_off hq
      exact ⟨hm, by have := (Nat.factorization_le_iff_dvd d0 m0).2 hdm q; omega⟩
    have hU : ∀ m : ℕ, m ≠ 0 → d ∣ m → m.primeFactors ⊆ S →
        Ud m d = ∏ q ∈ S, Lc q (m.factorization q) (d.factorization q) := by
      intro m m0 hdm hmS
      unfold Ud; rw [if_pos hdm]
      refine prod_subset hmS fun q hq hqm => ?_
      obtain ⟨e1, e2⟩ := hv m m0 hdm q hqm
      rw [e1, e2, Lc_zero_zero (hSp q hq)]
    have hV : ∀ m : ℕ, m ≠ 0 → d ∣ m → m.primeFactors ⊆ S →
        Vd m d = ∑ p ∈ S, Lv p (m.factorization p) (d.factorization p) *
          ∏ q ∈ S.erase p, Lc q (m.factorization q) (d.factorization q) := by
      intro m m0 hdm hmS
      unfold Vd; rw [if_pos hdm]
      refine sum_erase_ext hmS (fun p => Lv p (m.factorization p) (d.factorization p))
        (fun q => Lc q (m.factorization q) (d.factorization q)) (fun q hq hqm => ?_) (fun q hq hqm => ?_)
      · obtain ⟨e1, e2⟩ := hv m m0 hdm q hqm
        simp only [e1, e2]; exact Lv_zero_zero q (hp := hSp q hq)
      · obtain ⟨e1, e2⟩ := hv m m0 hdm q hqm
        simp only [e1, e2]; exact Lc_zero_zero (hSp q hq)
    have hW : Wd d = ∏ q ∈ S, Wc (lam q) (Xp q) (d.factorization q) := by
      unfold Wd
      exact prod_subset hdS fun q _ hq => by rw [vanish_off hq]; rfl
    have hW1 : W' d = ∑ p ∈ S, Real.log p * wd (lam p) (Xp p) (d.factorization p) *
        ∏ q ∈ S.erase p, Wc (lam q) (Xp q) (d.factorization q) := by
      simp only [hW']
      refine sum_erase_ext hdS (fun p => Real.log p * wd (lam p) (Xp p) (d.factorization p))
        (fun q => Wc (lam q) (Xp q) (d.factorization q)) (fun q _ hq => ?_) (fun q _ hq => ?_)
      · simp only [vanish_off hq, wd, mul_zero]
      · show Wc (lam q) (Xp q) (d.factorization q) = 1
        rw [vanish_off hq]; rfl
    have hhS : h.primeFactors ⊆ S := by rw [hS]; exact subset_union_left
    have hkS : k.primeFactors ⊆ S := by rw [hS]; exact subset_union_right
    rw [hU h h0 hdh hhS, hU k k0 hdk hkS, hV h h0 hdh hhS, hV k k0 hdk hkS, hW, hW1]
    rw [prod_rule3]
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun p hp => ?_
  set φ : ℕ → ℕ → ℝ := fun q e => if q = p then ψ' q e else ψ q e with hφ
  have hrw : ∀ d ∈ g.divisors, ψ' p (d.factorization p) * ∏ q ∈ S.erase p, ψ q (d.factorization q) =
      ∏ q ∈ S, φ q (d.factorization q) := by
    intro d _
    rw [← mul_prod_erase S (fun q => φ q (d.factorization q)) hp]
    simp only [hφ, if_true]
    congr 1
    exact prod_congr rfl fun q hq => by rw [if_neg (mem_erase.1 hq).1]
  rw [sum_congr rfl hrw, sum_divisors_prod_local' g0 hgS φ,
    ← mul_prod_erase S (fun q => ∑ e ∈ Icc 0 (g.factorization q), φ q e) hp]
  have hgp : ∀ q, g.factorization q = min (h.factorization q) (k.factorization q) := by
    intro q; rw [hgdef, Nat.factorization_gcd h0 k0]; rfl
  simp only [hφ, if_true]
  congr 1
  · rw [hgp]; exact (dloc_sym (hSp p hp) _ _).symm
  · refine prod_congr rfl fun q hq => ?_
    rw [sum_congr rfl fun e _ => if_neg (mem_erase.1 hq).1, hgp]
    exact (loc_chol_sym (hSp q (mem_erase.1 hq).2) _ _).symm

end RamanujanTau.QFProof3
