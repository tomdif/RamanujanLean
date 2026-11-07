/-
# `SvStripD` step 3: the twisted Euler assembly (`[DeligneBound]`)

Let `0 ≤ t ≤ 1/4`, `X_p = p^{−1+t}` (`Xt t p`; for the strip `t = −Im z` and `X_p = ‖p^{−s}‖`).
Let `T p e ≥ 0`, `W p e ≥ 0` be any local masses / pivots with the bounds of `Local.lean`:

    T p 0 ≤ 1 + 23914855 X²,  T p 1 ≤ |λ(p)| + 23914845 X,  T p e ≤ 10628820 (e+1)^6,
    W p 1 ≤ X + 25X²,          W p e ≤ 56 X^e.

**`euler_strip`**: there is an absolute `A` with, for all such data and `y ≥ 2`,

    Σ_{d≤y²} (Π_{p|d} W p (v_p d)) (Π_{p∈primes(y!)∪primes(d)} T p (v_p d))²  ≤  A y^{4t} log y.

Proof: off `d` the product is `≤ exp(23914855 Σ_p p^{−3/2})`; at `p^e ∥ d`,
`W T² ≤ p^{2te} g(p,e)/p^e` with `g(p,1) = λ(p)² + K/p`, `g(p,e) = B(3/2)^e`; `Π_{p|d} p^{2te} = d^{2t}
≤ y^{4t}`; and `Σ_{d≤y²} f(d)/d ≪ log y` for `f = ofLocal g` (`logmean_geo` + Mertens for `λ²`).
-/
import RamanujanTau.SvStripD.Local
import RamanujanTau.QFProof5.Assemble

set_option autoImplicit false

namespace RamanujanTau.SvStripD

open Finset ArithmeticFunction
open RamanujanTau.SelbergCoeffs3 (PrimesTo sum_inv_sq_PrimesTo_le)
open RamanujanTau.SelbergCoeffs (ofLocal ofLocal_apply ofLocal_ppow isMultiplicative_ofLocal)
open RamanujanTau.HafnerBridge (lam)
open RamanujanTau.QFProof3 (Xp)

/-! ### `X_p = p^{−1+t}` -/

/-- `X_p = p^{t−1}`. -/
noncomputable def Xt (t : ℝ) (p : ℕ) : ℝ := Real.exp ((t - 1) * Real.log p)

lemma Xt_pos (t : ℝ) (p : ℕ) : 0 < Xt t p := Real.exp_pos _

lemma Et_ge_one {t : ℝ} (ht : 0 ≤ t) (p : ℕ) : 1 ≤ Real.exp (t * Real.log p) :=
  Real.one_le_exp (mul_nonneg ht (Real.log_natCast_nonneg p))

lemma Xt_eq (t : ℝ) {p : ℕ} (hp : p.Prime) : Xt t p = Xp p * Real.exp (t * Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold Xt Xp
  rw [show (t - 1) * Real.log p = t * Real.log p + -Real.log p by ring, Real.exp_add, Real.exp_neg,
    Real.exp_log hp0]; ring

lemma Xt_le_one {t : ℝ} (ht : t ≤ 1) (p : ℕ) : Xt t p ≤ 1 :=
  Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_natCast_nonneg p))

lemma Xt_pow (t : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    Xt t p ^ e = Xp p ^ e * Real.exp (t * e * Real.log p) := by
  rw [Xt_eq t hp, mul_pow, ← Real.exp_nat_mul]; ring_nf

lemma Xt_sq_le {t : ℝ} (ht : t ≤ 1 / 4) {p : ℕ} (hp : p.Prime) :
    Xt t p ^ 2 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl := Real.log_natCast_nonneg p
  rw [Real.rpow_def_of_pos hp0, Xt, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.2 (by push_cast; nlinarith)

/-! ### Constants and the Euler majorant -/

noncomputable def K1 : ℝ := 4 * 23914845 + 23914845 ^ 2
noncomputable def Kz : ℝ := 26 * K1 + 100
noncomputable def Bz : ℝ := 56 * 10628820 ^ 2 * (100 / 3 : ℝ) ^ 12

lemma K1_nonneg : 0 ≤ K1 := by unfold K1; norm_num
lemma Kz_nonneg : 0 ≤ Kz := by unfold Kz; have := K1_nonneg; positivity
lemma Bz_nonneg : 0 ≤ Bz := by unfold Bz; positivity

/-- The local Euler majorant `g(p,e)`. -/
noncomputable def gZ (p e : ℕ) : ℝ :=
  if e = 0 then 1 else if e = 1 then lam p ^ 2 + Kz * Xp p else Bz * (3 / 2 : ℝ) ^ e

lemma gZ_nonneg (p e : ℕ) : 0 ≤ gZ p e := by
  unfold gZ Xp
  have := Kz_nonneg; have := Bz_nonneg
  split_ifs <;> positivity

noncomputable def fZ : ArithmeticFunction ℝ := ofLocal gZ

lemma fZ_nonneg (n : ℕ) : 0 ≤ fZ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [fZ, ofLocal_apply _ hn, Finsupp.prod]
  exact prod_nonneg fun _ _ => gZ_nonneg _ _

lemma fZ_eq {n : ℕ} (hn : n ≠ 0) : fZ n = ∏ p ∈ n.primeFactors, gZ p (n.factorization p) := by
  rw [fZ, ofLocal_apply _ hn, Finsupp.prod, Nat.support_factorization]

lemma fZ_ppow {p : ℕ} (hp : p.Prime) (k : ℕ) : fZ (p ^ k) = gZ p k :=
  ofLocal_ppow (h := gZ) (fun p => by simp [gZ]) hp k

section Deligne

variable [DeligneBound]

/-- **The Euler sum** `Σ_{d≤y²} f(d)/d ≤ A log y`. -/
theorem euler_fZ : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y → ∑ d ∈ Icc 1 (y ^ 2), fZ d / d ≤ A * Real.log y := by
  obtain ⟨Cm, hCm⟩ := RamanujanTau.SelbergCoeffs2.mertens2_bound
  have hB0 := Bz_nonneg
  have hK : (0 : ℝ) ≤ Kz := Kz_nonneg
  have hS : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, fZ p / p ≤ 1 * Real.log (Real.log M) + (Cm + Kz) := by
    intro M hM
    have hm := (abs_le.1 (hCm M)).2
    have hpt : ∀ p ∈ PrimesTo M, fZ p / p ≤ RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p +
        Kz * (1 / (p : ℝ) ^ 2) := by
      intro p hpP
      have hp : p.Prime := (mem_filter.mp hpP).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have h := fZ_ppow hp 1
      rw [pow_one] at h
      rw [h]
      simp only [gZ, one_ne_zero, if_false, if_true]
      rw [RamanujanTau.QFProof5.lam_prime_eq hp]
      unfold Xp; field_simp; rfl
    have hsq := sum_inv_sq_PrimesTo_le M
    calc ∑ p ∈ PrimesTo M, fZ p / p
        ≤ ∑ p ∈ PrimesTo M, (RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p + Kz * (1 / (p : ℝ) ^ 2)) :=
          sum_le_sum hpt
      _ = ∑ p ∈ PrimesTo M, RamanujanTau.EdgeNonvanishing.lam p ^ 2 / p +
            Kz * ∑ p ∈ PrimesTo M, 1 / (p : ℝ) ^ 2 := by rw [sum_add_distrib, mul_sum]
      _ ≤ (Real.log (Real.log M) + Cm) + Kz * 1 := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hsq hK)
          have : PrimesTo M = (Ioc 0 M).filter Nat.Prime := rfl
          rw [this]; linarith
      _ = _ := by ring
  have hL := RamanujanTau.QFProof5.logmean_geo fZ isMultiplicative_ofLocal fZ_nonneg hB0
    (fun p k hp hk => by
      rw [fZ_ppow hp]; simp [gZ, show k ≠ 0 by omega, show k ≠ 1 by omega]) hS
  refine ⟨2 * Real.exp (Cm + Kz + 9 * Bz), by positivity, fun y hy => ?_⟩
  have hy2 : 2 ≤ y ^ 2 := by nlinarith
  have h := hL (y ^ 2) hy2
  rw [Real.rpow_one] at h
  have hI : Icc 1 (y ^ 2) = Ioc 0 (y ^ 2) := by ext; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI]
  refine h.trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]; push_cast; ring

/-! ### Pointwise prime-power bounds -/

/-- `e = 1`: `W T² ≤ p^{2t} g(p,1)/p`. -/
lemma loc_one {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) {p : ℕ} (hp : p.Prime) {w T : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ Xt t p + 25 * Xt t p ^ 2) (hT0 : 0 ≤ T)
    (hT : T ≤ |lam p| + 23914845 * Xt t p) :
    w * T ^ 2 ≤ Real.exp (2 * t * 1 * Real.log p) * gZ p 1 * Xp p ^ 1 := by
  set X := Xt t p with hXd
  have hX0 : 0 < X := Xt_pos t p
  have hX1 : X ≤ 1 := Xt_le_one (by linarith) p
  have hl := RamanujanTau.QFProof5.abs_lam_le_two hp
  have hl0 := abs_nonneg (lam p)
  have hK1 := K1_nonneg
  have hT2 : T ^ 2 ≤ lam p ^ 2 + K1 * X := by
    have h1 : T ^ 2 ≤ (|lam p| + 23914845 * X) ^ 2 := pow_le_pow_left₀ hT0 hT 2
    have h2 : (|lam p| + 23914845 * X) ^ 2 = lam p ^ 2 + 2 * 23914845 * |lam p| * X +
        23914845 ^ 2 * X ^ 2 := by rw [add_sq, sq_abs]; ring
    have h3 : 2 * 23914845 * |lam p| * X ≤ 4 * 23914845 * X := by nlinarith
    have h4 : (23914845 : ℝ) ^ 2 * X ^ 2 ≤ 23914845 ^ 2 * X := by nlinarith
    unfold K1; nlinarith
  have hT20 : 0 ≤ T ^ 2 := sq_nonneg T
  have hl2 : lam p ^ 2 ≤ 4 := by nlinarith [sq_abs (lam p)]
  have hA : w * T ^ 2 ≤ X * lam p ^ 2 + Kz * X ^ 2 := by
    have := mul_le_mul hw hT2 hT20 (by positivity)
    have e : (X + 25 * X ^ 2) * (lam p ^ 2 + K1 * X) =
        X * lam p ^ 2 + X ^ 2 * (K1 + 25 * lam p ^ 2 + 25 * K1 * X) := by ring
    have : K1 + 25 * lam p ^ 2 + 25 * K1 * X ≤ Kz := by unfold Kz; nlinarith
    nlinarith [sq_nonneg X]
  have hE := Et_ge_one ht0 p
  set E := Real.exp (t * Real.log p) with hEd
  have hXE : X = Xp p * E := Xt_eq t hp
  have hXp0 : 0 < Xp p := inv_pos.2 (by exact_mod_cast hp.pos)
  have hE2 : Real.exp (2 * t * 1 * Real.log p) = E * E := by
    rw [hEd, ← Real.exp_add]; ring_nf
  rw [hE2, pow_one]
  simp only [gZ, one_ne_zero, if_false, if_true]
  refine hA.trans ?_
  rw [hXE]
  have hKz := Kz_nonneg
  have : 0 ≤ lam p ^ 2 := sq_nonneg _
  have hEE : E ≤ E * E := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hXp0.le this) (by linarith : (0 : ℝ) ≤ E * E - E),
    mul_nonneg (mul_nonneg hKz (sq_nonneg (Xp p))) (sq_nonneg E)]

/-- `e ≥ 2`: `W T² ≤ p^{2te} g(p,e)/p^e`. -/
lemma loc_ge_two {t : ℝ} (ht0 : 0 ≤ t) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 2 ≤ e) {w T : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ 56 * Xt t p ^ e) (hT0 : 0 ≤ T) (hT : T ≤ 10628820 * ((e : ℝ) + 1) ^ 6) :
    w * T ^ 2 ≤ Real.exp (2 * t * e * Real.log p) * gZ p e * Xp p ^ e := by
  have hXe : 0 ≤ Xt t p ^ e := by have := Xt_pos t p; positivity
  have hT2 : T ^ 2 ≤ 10628820 ^ 2 * ((e : ℝ) + 1) ^ 12 := by
    have := pow_le_pow_left₀ hT0 hT 2
    rw [mul_pow, ← pow_mul] at this; exact this
  have hpg := RamanujanTau.QFProof5.poly_le_geom e
  have hA : w * T ^ 2 ≤ Bz * (3 / 2 : ℝ) ^ e * Xt t p ^ e := by
    have := mul_le_mul hw hT2 (sq_nonneg T) (by positivity)
    have h2 : 56 * Xt t p ^ e * (10628820 ^ 2 * ((e : ℝ) + 1) ^ 12) ≤
        Bz * (3 / 2 : ℝ) ^ e * Xt t p ^ e := by
      unfold Bz
      have : 0 ≤ 56 * Xt t p ^ e * 10628820 ^ 2 := by positivity
      nlinarith
    linarith
  simp only [gZ, show e ≠ 0 by omega, show e ≠ 1 by omega, if_false]
  refine hA.trans ?_
  rw [Xt_pow t hp]
  have hE : Real.exp (t * e * Real.log p) ≤ Real.exp (2 * t * e * Real.log p) := by
    apply Real.exp_le_exp.2
    have := mul_nonneg (mul_nonneg ht0 (Nat.cast_nonneg (α := ℝ) e)) (Real.log_natCast_nonneg p)
    nlinarith
  have hB : 0 ≤ Bz * (3 / 2 : ℝ) ^ e * Xp p ^ e := by
    have := Bz_nonneg; unfold Xp; positivity
  nlinarith

/-! ### Products over `d` -/

lemma exp_log_d {t : ℝ} {d : ℕ} (hd : d ≠ 0) :
    ∏ p ∈ d.primeFactors, Real.exp (2 * t * (d.factorization p : ℝ) * Real.log p) =
      Real.exp (2 * t * Real.log d) := by
  rw [← Real.exp_sum, RamanujanTau.QFProof3.log_eq_sum hd subset_rfl, mul_sum]
  congr 1; refine sum_congr rfl fun p _ => by ring

/-- `Π_{p|d} W T² ≤ d^{2t} f(d)/d`. -/
lemma prod_local_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) {d : ℕ} (hd : d ≠ 0)
    (T W : ℕ → ℕ → ℝ) (hT0 : ∀ p e, 0 ≤ T p e) (hW0 : ∀ p e, 0 ≤ W p e)
    (hT1 : ∀ p, p.Prime → T p 1 ≤ |lam p| + 23914845 * Xt t p)
    (hTe : ∀ p e, p.Prime → T p e ≤ 10628820 * ((e : ℝ) + 1) ^ 6)
    (hW1 : ∀ p, p.Prime → W p 1 ≤ Xt t p + 25 * Xt t p ^ 2)
    (hWe : ∀ p e, p.Prime → W p e ≤ 56 * Xt t p ^ e) :
    (∏ p ∈ d.primeFactors, W p (d.factorization p)) * (∏ p ∈ d.primeFactors, T p (d.factorization p)) ^ 2
      ≤ Real.exp (2 * t * Real.log d) * (fZ d / d) := by
  rw [← prod_pow, ← prod_mul_distrib, div_eq_mul_inv, fZ_eq hd,
    RamanujanTau.QFProof3.inv_cast_eq_prod hd subset_rfl, ← exp_log_d hd, ← prod_mul_distrib,
    ← prod_mul_distrib]
  refine prod_le_prod (fun p _ => mul_nonneg (hW0 _ _) (sq_nonneg _)) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he := RamanujanTau.QFProof5.mem_pf_fac_ne hp
  set e := d.factorization p
  rcases Nat.lt_or_ge e 2 with h2 | h2
  · have he1 : e = 1 := by omega
    have := loc_one ht0 ht hpp (hW0 p 1) (hW1 p hpp) (hT0 p 1) (hT1 p hpp)
    rw [he1]; push_cast
    linarith
  · have := loc_ge_two ht0 hpp h2 (hW0 p e) (hWe p e hpp) (hT0 p e) (hTe p e hpp)
    linarith

/-- The off-`d` product is bounded by an absolute constant. -/
lemma Z0_summable : Summable fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
  Real.summable_nat_rpow.2 (by norm_num)

noncomputable def Z0 : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))

lemma sum_Xt_sq_le {t : ℝ} (ht : t ≤ 1 / 4) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, Xt t p ^ 2 ≤ Z0 := by
  refine (sum_le_sum fun p hp => Xt_sq_le ht (hS p hp)).trans ?_
  exact Z0_summable.sum_le_tsum S (fun n _ => by positivity)

lemma prod_off_le {t : ℝ} (ht : t ≤ 1 / 4) (T : ℕ → ℕ → ℝ) (hT0 : ∀ p e, 0 ≤ T p e)
    (hT00 : ∀ p, p.Prime → T p 0 ≤ 1 + 23914855 * Xt t p ^ 2) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, T p 0 ≤ Real.exp (23914855 * Z0) := by
  calc ∏ p ∈ S, T p 0 ≤ ∏ p ∈ S, Real.exp (23914855 * Xt t p ^ 2) := by
        refine prod_le_prod (fun _ _ => hT0 _ _) fun p hp => (hT00 p (hS p hp)).trans ?_
        have := Real.add_one_le_exp (23914855 * Xt t p ^ 2); linarith
    _ = Real.exp (23914855 * ∑ p ∈ S, Xt t p ^ 2) := by rw [← Real.exp_sum, mul_sum]
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sum_Xt_sq_le ht S hS) (by norm_num))

/-- **The twisted Euler assembly.** -/
theorem euler_strip : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ∀ y : ℕ, 2 ≤ y →
    ∀ T W : ℕ → ℕ → ℝ, (∀ p e, 0 ≤ T p e) → (∀ p e, 0 ≤ W p e) →
    (∀ p, p.Prime → T p 0 ≤ 1 + 23914855 * Xt t p ^ 2) →
    (∀ p, p.Prime → T p 1 ≤ |lam p| + 23914845 * Xt t p) →
    (∀ p e, p.Prime → T p e ≤ 10628820 * ((e : ℝ) + 1) ^ 6) →
    (∀ p, p.Prime → W p 1 ≤ Xt t p + 25 * Xt t p ^ 2) →
    (∀ p e, p.Prime → W p e ≤ 56 * Xt t p ^ e) →
    ∑ d ∈ Icc 1 (y ^ 2), (∏ p ∈ d.primeFactors, W p (d.factorization p)) *
      (∏ p ∈ (y.factorial).primeFactors ∪ d.primeFactors, T p (d.factorization p)) ^ 2 ≤
      A * Real.exp (4 * t * Real.log y) * Real.log y := by
  obtain ⟨A, hA0, hA⟩ := euler_fZ
  refine ⟨Real.exp (23914855 * Z0) ^ 2 * A, by positivity, fun t ht0 ht y hy T W hT0 hW0 hT00 hT1 hTe
    hW1 hWe => ?_⟩
  set E := Real.exp (23914855 * Z0) with hE
  have hpt : ∀ d ∈ Icc 1 (y ^ 2), (∏ p ∈ d.primeFactors, W p (d.factorization p)) *
      (∏ p ∈ (y.factorial).primeFactors ∪ d.primeFactors, T p (d.factorization p)) ^ 2 ≤
      E ^ 2 * Real.exp (4 * t * Real.log y) * (fZ d / d) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
    set S := (y.factorial).primeFactors ∪ d.primeFactors
    have hsplit : ∏ p ∈ S, T p (d.factorization p) =
        (∏ p ∈ S.filter (· ∈ d.primeFactors), T p (d.factorization p)) *
          ∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p) :=
      (prod_filter_mul_prod_filter_not S _ _).symm
    have hf : S.filter (· ∈ d.primeFactors) = d.primeFactors := RamanujanTau.QFProof5.filter_S_eq
    have hoff : ∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p) ≤ E := by
      have e1 : ∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p) =
          ∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p 0 :=
        prod_congr rfl fun p hp => by
          rw [Finsupp.notMem_support_iff.1 (by rw [Nat.support_factorization]; exact (mem_filter.1 hp).2)]
      rw [e1]
      refine prod_off_le ht T hT0 hT00 _ fun p hp => ?_
      rcases mem_union.1 (mem_filter.1 hp).1 with h | h <;> exact Nat.prime_of_mem_primeFactors h
    have hon := prod_local_le ht0 ht hd0 T W hT0 hW0 hT1 hTe hW1 hWe
    have hP0 : 0 ≤ ∏ p ∈ d.primeFactors, T p (d.factorization p) := prod_nonneg fun _ _ => hT0 _ _
    have hQ0 : 0 ≤ ∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p) :=
      prod_nonneg fun _ _ => hT0 _ _
    have hW : 0 ≤ ∏ p ∈ d.primeFactors, W p (d.factorization p) := prod_nonneg fun _ _ => hW0 _ _
    have hlog : Real.exp (2 * t * Real.log d) ≤ Real.exp (4 * t * Real.log y) := by
      apply Real.exp_le_exp.2
      have := RamanujanTau.QFProof5.log_le_two_log hd
      nlinarith
    have hfd : 0 ≤ fZ d / d := div_nonneg (fZ_nonneg d) (Nat.cast_nonneg _)
    rw [hsplit, hf, mul_pow]
    calc (∏ p ∈ d.primeFactors, W p (d.factorization p)) *
          ((∏ p ∈ d.primeFactors, T p (d.factorization p)) ^ 2 *
            (∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p)) ^ 2)
        = ((∏ p ∈ d.primeFactors, W p (d.factorization p)) *
            (∏ p ∈ d.primeFactors, T p (d.factorization p)) ^ 2) *
            (∏ p ∈ S.filter (fun p => ¬ p ∈ d.primeFactors), T p (d.factorization p)) ^ 2 := by ring
      _ ≤ (Real.exp (2 * t * Real.log d) * (fZ d / d)) * E ^ 2 :=
          mul_le_mul hon (pow_le_pow_left₀ hQ0 hoff 2) (sq_nonneg _) (by positivity)
      _ ≤ (Real.exp (4 * t * Real.log y) * (fZ d / d)) * E ^ 2 := by gcongr
      _ = _ := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  have := hA y hy
  calc E ^ 2 * Real.exp (4 * t * Real.log y) * ∑ d ∈ Icc 1 (y ^ 2), fZ d / d
      ≤ E ^ 2 * Real.exp (4 * t * Real.log y) * (A * Real.log y) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

end Deligne

end RamanujanTau.SvStripD
