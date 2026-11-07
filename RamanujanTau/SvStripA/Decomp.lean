/-
# `SvStripA` step 2b: the global Cholesky decomposition of the `s`-twisted kernel (unconditional)

For complex `s` put `x_p = p^{−s}` and

    K^{[s]}(h,k) = [h,k]^{−s} ρ(h₁, s) ρ(k₁, s)        (h₁ = h/(h,k), k₁ = k/(h,k)),

with `ρ = rhoCF` the closed-form local factors (`Local.lean`; `= rhoC` for `Re s > 11/20`).
Columns `L_p(a,0) = x^a ρ_p(a,x)`, `L_p(a,e) = x^{a−e} λ(p^{a−e})` (`1 ≤ e ≤ a`), `0` (`a < e`);
pivots `W(d) = Π_{p^e∥d} W_p(e; x_p)`; `U(h,d) = 1_{d|h} Π_{p^a∥h} L_p(a, v_p d)`.

**`qDecompC`** (for `Re s > 0`): `K^{[s]}(h,k) = Σ_{d|h} W(d) U(h,d) U(k,d)`, `U(h,d) = 0` unless
`d | h`.  This is the complex (`1/p ↦ p^{−s}`) copy of `QFProof3.qDecomp`.  Level 1.
-/
import RamanujanTau.SvStripA.Local

set_option autoImplicit false

namespace RamanujanTau.SvStripA

open Complex Finset
open RamanujanTau.HafnerBridge (lam lam_one)

/-! ### Divisor sums of products of local factors (any commutative semiring) -/

theorem sum_divisors_prod_localR {R : Type*} [CommSemiring R] {g : ℕ} (hg : g ≠ 0) (φ : ℕ → ℕ → R) :
    ∑ d ∈ g.divisors, ∏ p ∈ g.primeFactors, φ p (d.factorization p) =
      ∏ p ∈ g.primeFactors, ∑ e ∈ Icc 0 (g.factorization p), φ p e := by
  classical
  rw [Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hg, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_attach (Iic g.factorization)
    (fun f : ℕ →₀ ℕ => ∏ p ∈ g.primeFactors, φ p ((f.prod (· ^ ·)).factorization p))]
  have h1 : ∀ f ∈ Iic g.factorization,
      ∏ p ∈ g.primeFactors, φ p ((f.prod (· ^ ·)).factorization p) =
      ∏ p ∈ g.primeFactors, φ p (f p) := by
    intro f hf
    have hle : f ≤ g.factorization := mem_Iic.1 hf
    have hpr : ∀ p ∈ f.support, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (by
        rw [← Nat.support_factorization]
        exact Finsupp.support_mono hle hp)
    rw [Nat.prod_pow_factorization_eq_self hpr]
  rw [sum_congr rfl h1, prod_sum]
  have hI : Iic g.factorization = Icc 0 g.factorization := by
    ext f; simp
  rw [hI, Finsupp.Icc_eq, Finsupp.support_zero, empty_union, Nat.support_factorization]
  have hR : (⇑(Finsupp.rangeIcc 0 g.factorization)) = fun p => Icc 0 (g.factorization p) := by
    funext p; rw [Finsupp.coe_rangeIcc]; rfl
  unfold Finset.finsupp
  rw [sum_map, hR]
  refine sum_congr (by convert rfl) fun x _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← prod_attach g.primeFactors]
  refine prod_congr rfl fun p _ => ?_
  rw [Finsupp.indicator_of_mem p.2]

theorem sum_divisors_prod_localR' {R : Type*} [CommSemiring R] {g : ℕ} (hg : g ≠ 0) {S : Finset ℕ}
    (hS : g.primeFactors ⊆ S) (φ : ℕ → ℕ → R) :
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
  rw [sum_congr rfl hsplit, ← sum_mul, sum_divisors_prod_localR hg, ← prod_sdiff hS, mul_comm]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hp' : p ∉ g.primeFactors := (mem_sdiff.1 hp).2
  have h2 : g.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [h2]; simp

/-! ### Local data -/

/-- `x_p = p^{−s}`. -/
noncomputable abbrev xs (p : ℕ) (s : ℂ) : ℂ := (p : ℂ) ^ (-s)

/-- The local Cholesky columns at `x_p = p^{−s}`. -/
noncomputable def LcC (s : ℂ) (p a e : ℕ) : ℂ :=
  if a < e then 0 else if e = 0 then xs p s ^ a * rhoPx p a (xs p s)
  else xs p s ^ (a - e) * (lam (p ^ (a - e)) : ℂ)

/-- The pivots `W(d)`. -/
noncomputable def WdC (s : ℂ) (d : ℕ) : ℂ :=
  ∏ p ∈ d.primeFactors, WcK (lam p : ℂ) (xs p s) (d.factorization p)

/-- The columns `U(h,d)`. -/
noncomputable def UdC (s : ℂ) (h d : ℕ) : ℂ :=
  if d ∣ h then ∏ p ∈ h.primeFactors, LcC s p (h.factorization p) (d.factorization p) else 0

/-- The `s`-twisted kernel `K^{[s]}(h,k) = [h,k]^{−s} ρ(h₁,s) ρ(k₁,s)`. -/
noncomputable def KqC (s : ℂ) (h k : ℕ) : ℂ :=
  ((Nat.lcm h k : ℕ) : ℂ) ^ (-s) * rhoCF (h / Nat.gcd h k) s * rhoCF (k / Nat.gcd h k) s

lemma one_add_xs_ne {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) : 1 + xs p s ≠ 0 :=
  one_add_ne_zero (norm_xs_lt_one hp hs)

lemma LcC_zero_zero (s : ℂ) (p : ℕ) : LcC s p 0 0 = 1 := by
  simp [LcC, rhoPx_zero]

/-- **Complex local Cholesky**: `Σ_{e≤a} W_e L(a,e) L(a+n,e) = x^{a+n} ρ_p(n, x)`. -/
theorem loc_cholC {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) (a n : ℕ) :
    ∑ e ∈ Icc 0 a, WcK (lam p : ℂ) (xs p s) e * LcC s p a e * LcC s p (a + n) e =
      xs p s ^ (a + n) * rhoPx p n (xs p s) := by
  have hc := cholK (lam p : ℂ) (xs p s) (muC p) (muC_zero p) (muC_one p) (muC_rec hp)
    (one_add_xs_ne hp hs) n a
  rw [show rrK (xs p s) (muC p) n = rhoPx p n (xs p s) from rfl,
    show rrK (xs p s) (muC p) a = rhoPx p a (xs p s) from rfl,
    show rrK (xs p s) (muC p) (a + n) = rhoPx p (a + n) (xs p s) from rfl] at hc
  rw [hc]
  have hI : Icc 0 a = range (a + 1) := by ext; simp only [mem_Icc, mem_range]; omega
  rw [hI, sum_range_succ']
  have h0 : WcK (lam p : ℂ) (xs p s) 0 * LcC s p a 0 * LcC s p (a + n) 0 =
      xs p s ^ (2 * a + n) * rhoPx p a (xs p s) * rhoPx p (a + n) (xs p s) := by
    simp only [LcC, Nat.not_lt_zero, if_false, if_true, WcK]
    rw [show 2 * a + n = a + (a + n) by ring, pow_add]; ring
  rw [h0, add_comm]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hia : i < a := mem_range.1 hi
  rw [show a - 1 - i + 1 = a - i by omega]
  have e1 : ¬ a < a - i := by omega
  have e2 : ¬ a + n < a - i := by omega
  have e3 : a - i ≠ 0 := by omega
  simp only [LcC, e1, e2, e3, if_false]
  rw [show a - (a - i) = i by omega, show a + n - (a - i) = i + n by omega, muC_succ,
    show i + n + 1 = (i + n) + 1 by ring, muC_succ]
  rw [show n + 2 * i = i + (i + n) by ring, pow_add]
  ring

lemma loc_cholC_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) {a b : ℕ} (hab : a ≤ b) :
    ∑ e ∈ Icc 0 (min a b), WcK (lam p : ℂ) (xs p s) e * LcC s p a e * LcC s p b e =
      xs p s ^ (max a b) * rhoPx p (b - a) (xs p s) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  rw [min_eq_left hab, max_eq_right hab, loc_cholC hp hs, Nat.add_sub_cancel_left]

lemma loc_cholC_sym {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) (a b : ℕ) :
    ∑ e ∈ Icc 0 (min a b), WcK (lam p : ℂ) (xs p s) e * LcC s p a e * LcC s p b e =
      xs p s ^ (max a b) * rhoPx p (if a ≤ b then b - a else a - b) (xs p s) := by
  split_ifs with hab
  · exact loc_cholC_le hp hs hab
  · have hba : b ≤ a := by omega
    have := loc_cholC_le hp hs hba
    rw [min_comm, max_comm, ← this]
    exact sum_congr rfl fun e _ => by ring

/-! ### `n^{−s}` and `ρ` as products over a set of primes -/

lemma natCast_prod_cpow (S : Finset ℕ) (f : ℕ → ℕ) (w : ℂ) :
    (((∏ p ∈ S, f p : ℕ) : ℂ)) ^ w = ∏ p ∈ S, ((f p : ℕ) : ℂ) ^ w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih => rw [prod_insert hq, prod_insert hq, Nat.cast_mul, natCast_mul_natCast_cpow, ih]

lemma natCast_pow_cpow (p e : ℕ) (w : ℂ) : (((p ^ e : ℕ)) : ℂ) ^ w = ((p : ℂ) ^ w) ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

lemma cpow_eq_prod {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : n.primeFactors ⊆ S) (s : ℂ) :
    ((n : ℕ) : ℂ) ^ (-s) = ∏ p ∈ S, xs p s ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, natCast_prod_cpow]
  simp_rw [natCast_pow_cpow]
  refine prod_subset hS fun p _ hpm => ?_
  have : n.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [this, pow_zero]

lemma rhoCF_eq_prod {m : ℕ} {S : Finset ℕ} (hS : m.primeFactors ⊆ S) (s : ℂ) :
    rhoCF m s = ∏ p ∈ S, rhoPx p (m.factorization p) (xs p s) := by
  unfold rhoCF
  refine prod_subset hS fun p hp hpm => ?_
  have : m.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [this, rhoPx_zero]

/-- The twisted kernel as a product of local kernels over the primes of `hk`. -/
lemma KqC_prod (s : ℂ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    KqC s h k = ∏ p ∈ (h * k).primeFactors,
      xs p s ^ (max (h.factorization p) (k.factorization p)) *
        rhoPx p (if h.factorization p ≤ k.factorization p then k.factorization p - h.factorization p
          else h.factorization p - k.factorization p) (xs p s) := by
  set S := (h * k).primeFactors with hSdef
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
  unfold KqC
  rw [rhoCF_eq_prod hsub1, rhoCF_eq_prod hsub2, cpow_eq_prod hl0 hsub3,
    ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_div hg, Nat.factorization_div hg', Nat.factorization_lcm h0 k0,
    Nat.factorization_gcd h0 k0]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply, Finsupp.sup_apply]
  have hz := rhoPx_zero p (xs p s)
  split_ifs with hab
  · rw [inf_eq_left.2 hab, sup_eq_right.2 hab, Nat.sub_self, hz]
    try simp only [max_eq_right hab]
    ring
  · push Not at hab
    rw [inf_eq_right.2 hab.le, sup_eq_left.2 hab.le, Nat.sub_self, hz]
    try simp only [max_eq_left hab.le]
    ring

/-- **`QDecomp` for the `s`-twisted kernel** (`Re s > 0`): `K^{[s]}(h,k) = Σ_{d|h} W(d)U(h,d)U(k,d)`. -/
theorem qDecompC {s : ℂ} (hs : 0 < s.re) :
    (∀ h d, ¬ d ∣ h → UdC s h d = 0) ∧
      ∀ h k, 0 < h → 0 < k → KqC s h k = ∑ d ∈ h.divisors, WdC s d * UdC s h d * UdC s k d := by
  refine ⟨fun h d hd => by simp [UdC, hd], fun h k hh hk => ?_⟩
  set g := Nat.gcd h k with hgdef
  set S := (h * k).primeFactors with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : h ≠ 0 := hh.ne'
  have k0 : k ≠ 0 := hk.ne'
  have g0 : g ≠ 0 := Nat.gcd_ne_zero_left h0
  have hS : S = h.primeFactors ∪ k.primeFactors := Nat.primeFactors_mul h0 k0
  have hres : ∑ d ∈ h.divisors, WdC s d * UdC s h d * UdC s k d =
      ∑ d ∈ g.divisors, WdC s d * UdC s h d * UdC s k d := by
    symm
    refine sum_subset (Nat.divisors_subset_of_dvd h0 (Nat.gcd_dvd_left h k)) fun d hd hdg => ?_
    have hdh := Nat.dvd_of_mem_divisors hd
    have : ¬ d ∣ k := fun hdk => hdg (Nat.mem_divisors.2 ⟨Nat.dvd_gcd hdh hdk, g0⟩)
    simp [UdC, this]
  rw [hres, KqC_prod s hh hk]
  have hgS : g.primeFactors ⊆ S := by
    rw [hS]; exact (Nat.primeFactors_mono (Nat.gcd_dvd_left h k) h0).trans subset_union_left
  have hterm : ∀ d ∈ g.divisors, WdC s d * UdC s h d * UdC s k d =
      ∏ p ∈ S, WcK (lam p : ℂ) (xs p s) (d.factorization p) * LcC s p (h.factorization p) (d.factorization p) *
        LcC s p (k.factorization p) (d.factorization p) := by
    intro d hd
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdh : d ∣ h := hdg.trans (Nat.gcd_dvd_left h k)
    have hdk : d ∣ k := hdg.trans (Nat.gcd_dvd_right h k)
    have d0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdS : d.primeFactors ⊆ S := (Nat.primeFactors_mono hdg g0).trans hgS
    have hvd : ∀ p, p ∉ d.primeFactors → d.factorization p = 0 := fun p hp =>
      Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    have ext_h : ∀ m : ℕ, m ≠ 0 → d ∣ m → m.primeFactors ⊆ S →
        ∏ p ∈ m.primeFactors, LcC s p (m.factorization p) (d.factorization p) =
        ∏ p ∈ S, LcC s p (m.factorization p) (d.factorization p) := by
      intro m m0 hdm hmS
      refine prod_subset hmS fun p hp hpm => ?_
      have hm : m.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
      have hd' : d.factorization p = 0 := by
        have := (Nat.factorization_le_iff_dvd d0 m0).2 hdm p; omega
      rw [hm, hd', LcC_zero_zero]
    unfold WdC UdC
    rw [if_pos hdh, if_pos hdk, ext_h h h0 hdh (by rw [hS]; exact subset_union_left),
      ext_h k k0 hdk (by rw [hS]; exact subset_union_right)]
    rw [prod_subset hdS fun p hp hpd => by rw [hvd p hpd]; rfl, ← prod_mul_distrib, ← prod_mul_distrib]
  rw [sum_congr rfl hterm, sum_divisors_prod_localR' g0 hgS
    (fun p e => WcK (lam p : ℂ) (xs p s) e * LcC s p (h.factorization p) e * LcC s p (k.factorization p) e)]
  refine prod_congr rfl fun p hp => ?_
  have hgp : g.factorization p = min (h.factorization p) (k.factorization p) := by
    rw [hgdef, Nat.factorization_gcd h0 k0]; rfl
  rw [hgp, loc_cholC_sym (hSp p hp) hs]

end RamanujanTau.SvStripA
