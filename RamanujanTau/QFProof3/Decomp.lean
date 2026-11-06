/-
# `QDecomp` for the explicit Cholesky data (unconditional)

`Wd d = Π_{p^e∥d} W_p(e)`, `Ud h d = 1_{d|h} Π_{p^a∥h} L_p(a, v_p d)` with
`L_p(a,0) = X^a ρ_p(a)`, `L_p(a,e) = X^{a−e} λ(p^{a−e})` (`1 ≤ e ≤ a`), `0` for `a < e`.

**`qDecomp`**: `QFProof.QDecomp Wd Ud`.
-/
import RamanujanTau.QFProof.Reduction
import RamanujanTau.QFProof.LocalChol
import RamanujanTau.QFProof2.DivProd

set_option autoImplicit false

namespace RamanujanTau.QFProof3

open Finset RamanujanTau.HafnerBridge RamanujanTau.QFProof RamanujanTau.QFProof2

/-- `X_p = 1/p`. -/
noncomputable abbrev Xp (p : ℕ) : ℝ := (p : ℝ)⁻¹

/-- The local Cholesky columns. -/
noncomputable def Lc (p a e : ℕ) : ℝ :=
  if a < e then 0 else if e = 0 then Xp p ^ a * rhoP p a else Xp p ^ (a - e) * lam (p ^ (a - e))

/-- The pivots `W(d)`. -/
noncomputable def Wd (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, Wc (lam p) (Xp p) (d.factorization p)

/-- The columns `U(h,d)`. -/
noncomputable def Ud (h d : ℕ) : ℝ :=
  if d ∣ h then ∏ p ∈ h.primeFactors, Lc p (h.factorization p) (d.factorization p) else 0

/-- `Σ_{d|g} Π_{p∈S} φ(p,v_p d) = Π_{p∈S} Σ_{e≤v_p g} φ(p,e)` for `S ⊇` the prime factors of `g`. -/
theorem sum_divisors_prod_local' {g : ℕ} (hg : g ≠ 0) {S : Finset ℕ} (hS : g.primeFactors ⊆ S)
    (φ : ℕ → ℕ → ℝ) :
    ∑ d ∈ g.divisors, ∏ p ∈ S, φ p (d.factorization p) =
      ∏ p ∈ S, ∑ e ∈ Icc 0 (g.factorization p), φ p e := by
  have hsplit : ∀ d ∈ g.divisors, ∏ p ∈ S, φ p (d.factorization p) =
      (∏ p ∈ g.primeFactors, φ p (d.factorization p)) * ∏ p ∈ S \ g.primeFactors, φ p 0 := by
    intro d hd
    rw [← prod_sdiff hS, mul_comm]
    congr 1
    refine prod_congr rfl fun p hp => ?_
    have hp' : p ∉ g.primeFactors := (mem_sdiff.1 hp).2
    have hdg := Nat.dvd_of_mem_divisors hd
    have : d.factorization p = 0 := by
      have h1 := (Nat.factorization_le_iff_dvd (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)) hg).2 hdg p
      have h2 : g.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
      omega
    rw [this]
  rw [sum_congr rfl hsplit, ← sum_mul, sum_divisors_prod_local hg, ← prod_sdiff hS, mul_comm]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hp' : p ∉ g.primeFactors := (mem_sdiff.1 hp).2
  have h2 : g.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [h2]; simp

lemma Lc_zero_zero {p : ℕ} (hp : p.Prime) : Lc p 0 0 = 1 := by
  simp [Lc, rhoP_zero hp]

/-- Local Cholesky: `Σ_{e≤a} W_e L(a,e) L(a+n,e) = X^{a+n} ρ_p(n)`. -/
lemma loc_chol {p : ℕ} (hp : p.Prime) (a n : ℕ) :
    ∑ e ∈ Icc 0 a, Wc (lam p) (Xp p) e * Lc p a e * Lc p (a + n) e = Xp p ^ (a + n) * rhoP p n := by
  rw [chol_rhoP hp n a]
  have hI : Icc 0 a = range (a + 1) := by ext; simp only [mem_Icc, mem_range]; omega
  rw [hI, sum_range_succ']
  have h0 : Wc (lam p) (Xp p) 0 * Lc p a 0 * Lc p (a + n) 0 =
      Xp p ^ (2 * a + n) * rhoP p a * rhoP p (a + n) := by
    simp only [Lc, Nat.not_lt_zero, if_false, if_true, Wc] <;> ring
  rw [h0, add_comm]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hia : i < a := mem_range.1 hi
  rw [show a - 1 - i + 1 = a - i by omega]
  have e1 : ¬ a < a - i := by omega
  have e2 : ¬ a + n < a - i := by omega
  have e3 : a - i ≠ 0 := by omega
  simp only [Lc, e1, e2, e3, if_false]
  rw [show a - (a - i) = i by omega, show a + n - (a - i) = i + n by omega]
  rw [show n + 2 * i = i + (i + n) by ring, pow_add]
  ring

lemma loc_chol_le {p : ℕ} (hp : p.Prime) {a b : ℕ} (hab : a ≤ b) :
    ∑ e ∈ Icc 0 (min a b), Wc (lam p) (Xp p) e * Lc p a e * Lc p b e =
      Xp p ^ (max a b) * rhoP p (b - a) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  rw [min_eq_left hab, max_eq_right hab, loc_chol hp, Nat.add_sub_cancel_left]

lemma loc_chol_sym {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ∑ e ∈ Icc 0 (min a b), Wc (lam p) (Xp p) e * Lc p a e * Lc p b e =
      Xp p ^ (max a b) * rhoP p (if a ≤ b then b - a else a - b) := by
  split_ifs with hab
  · exact loc_chol_le hp hab
  · have hba : b ≤ a := by omega
    have := loc_chol_le hp hba
    rw [min_comm, max_comm, ← this]
    exact sum_congr rfl fun e _ => by ring

lemma rho_eq_prod {m : ℕ} {S : Finset ℕ} (hS : m.primeFactors ⊆ S) (hSp : ∀ p ∈ S, p.Prime) :
    rho m = ∏ p ∈ S, rhoP p (m.factorization p) := by
  unfold rho
  refine prod_subset hS fun p hp hpm => ?_
  have : m.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [this, rhoP_zero (hSp p hp)]

lemma inv_cast_eq_prod {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) :
    ((n : ℝ))⁻¹ = ∏ p ∈ S, Xp p ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, ← prod_inv_distrib]
  rw [prod_subset hS fun p _ hpm => by
    have : n.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [this]; simp]
  refine prod_congr rfl fun p _ => ?_
  push_cast; rw [inv_pow]

/-- The kernel as a product of local kernels over `S = primes of hk`. -/
lemma Kq_prod {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Kq h k = ∏ p ∈ (h * k).primeFactors,
      Xp p ^ (max (h.factorization p) (k.factorization p)) *
        rhoP p (if h.factorization p ≤ k.factorization p then k.factorization p - h.factorization p
          else h.factorization p - k.factorization p) := by
  set S := (h * k).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : h ≠ 0 := hh.ne'
  have k0 : k ≠ 0 := hk.ne'
  have hS : S = h.primeFactors ∪ k.primeFactors := Nat.primeFactors_mul h0 k0
  have hg := Nat.gcd_dvd_left h k
  have hg' := Nat.gcd_dvd_right h k
  have g0 : Nat.gcd h k ≠ 0 := Nat.gcd_ne_zero_left h0
  have hsub1 : (h / Nat.gcd h k).primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hg) h0).trans subset_union_left
  have hsub2 : (k / Nat.gcd h k).primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hg') k0).trans subset_union_right
  have hl0 : Nat.lcm h k ≠ 0 := Nat.lcm_ne_zero h0 k0
  have hsub3 : (Nat.lcm h k).primeFactors ⊆ S :=
    Nat.primeFactors_mono (Nat.lcm_dvd_mul h k) (mul_ne_zero h0 k0)
  unfold Kq
  rw [div_eq_mul_inv, rho_eq_prod hsub1 hSp, rho_eq_prod hsub2 hSp, inv_cast_eq_prod hl0 hsub3,
    ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_div hg, Nat.factorization_div hg', Nat.factorization_lcm h0 k0,
    Nat.factorization_gcd h0 k0]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply, Finsupp.sup_apply]
  have hz := rhoP_zero (hSp p ‹_›)
  split_ifs with hab
  · rw [inf_eq_left.2 hab, sup_eq_right.2 hab, Nat.sub_self, hz]
    try simp only [max_eq_right hab]
    ring
  · push Not at hab
    rw [inf_eq_right.2 hab.le, sup_eq_left.2 hab.le, Nat.sub_self, hz]
    try simp only [max_eq_left hab.le]
    ring

/-- **`QDecomp Wd Ud`.** -/
theorem qDecomp : QDecomp Wd Ud := by
  refine ⟨fun h d hd => by simp [Ud, hd], fun h k hh hk => ?_⟩
  set g := Nat.gcd h k with hgdef
  set S := (h * k).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : h ≠ 0 := hh.ne'
  have k0 : k ≠ 0 := hk.ne'
  have g0 : g ≠ 0 := Nat.gcd_ne_zero_left h0
  have hS : S = h.primeFactors ∪ k.primeFactors := Nat.primeFactors_mul h0 k0
  -- restrict to `d | g`
  have hres : ∑ d ∈ h.divisors, Wd d * Ud h d * Ud k d = ∑ d ∈ g.divisors, Wd d * Ud h d * Ud k d := by
    symm
    refine sum_subset (Nat.divisors_subset_of_dvd h0 (Nat.gcd_dvd_left h k)) fun d hd hdg => ?_
    have hdh := Nat.dvd_of_mem_divisors hd
    have : ¬ d ∣ k := fun hdk => hdg (Nat.mem_divisors.2 ⟨Nat.dvd_gcd hdh hdk, g0⟩)
    simp [Ud, this]
  rw [hres, Kq_prod hh hk]
  have hgS : g.primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.gcd_dvd_left h k) h0).trans subset_union_left
  -- each term as a product over `S`
  have hterm : ∀ d ∈ g.divisors, Wd d * Ud h d * Ud k d =
      ∏ p ∈ S, Wc (lam p) (Xp p) (d.factorization p) * Lc p (h.factorization p) (d.factorization p) *
        Lc p (k.factorization p) (d.factorization p) := by
    intro d hd
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdh : d ∣ h := hdg.trans (Nat.gcd_dvd_left h k)
    have hdk : d ∣ k := hdg.trans (Nat.gcd_dvd_right h k)
    have d0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdS : d.primeFactors ⊆ S := (Nat.primeFactors_mono hdg g0).trans hgS
    have hvd : ∀ p, p ∉ d.primeFactors → d.factorization p = 0 := fun p hp =>
      Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    have ext_h : ∀ m : ℕ, m ≠ 0 → d ∣ m → m.primeFactors ⊆ S →
        ∏ p ∈ m.primeFactors, Lc p (m.factorization p) (d.factorization p) =
        ∏ p ∈ S, Lc p (m.factorization p) (d.factorization p) := by
      intro m m0 hdm hmS
      refine prod_subset hmS fun p hp hpm => ?_
      have hm : m.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
      have hd' : d.factorization p = 0 := by
        have := (Nat.factorization_le_iff_dvd d0 m0).2 hdm p; omega
      rw [hm, hd', Lc_zero_zero (hSp p hp)]
    unfold Wd Ud
    rw [if_pos hdh, if_pos hdk, ext_h h h0 hdh (by rw [hS]; exact subset_union_left),
      ext_h k k0 hdk (by rw [hS]; exact subset_union_right)]
    rw [prod_subset hdS fun p hp hpd => by rw [hvd p hpd]; rfl, ← prod_mul_distrib, ← prod_mul_distrib]
  rw [sum_congr rfl hterm, sum_divisors_prod_local' g0 hgS
    (fun p e => Wc (lam p) (Xp p) e * Lc p (h.factorization p) e * Lc p (k.factorization p) e)]
  refine prod_congr rfl fun p hp => ?_
  have hgp : g.factorization p = min (h.factorization p) (k.factorization p) := by
    rw [hgdef, Nat.factorization_gcd h0 k0]; rfl
  rw [hgp, loc_chol_sym (hSp p hp)]

end RamanujanTau.QFProof3
