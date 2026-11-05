/-
# `log (ζ(2s) R(s)) = ∑ cR(n) n^{−s}` on `Re s > 1`, without Deligne

Normalized Rankin–Selberg series `R(s) = ∑ τ(n)² n^{−11−s}` (`EdgeNonvanishing.RS`).
Its local factor times that of `ζ(2s)` is `((1−Y)²(1−α²Y)(1−β²Y))⁻¹`, `Y = p^{−s}`
(`EdgeNonvanishing.rs_local`), whose logarithm is `∑_k A_k² Y^k / k` with
`A_k = α_p^k + β_p^k` (real).  So

  `cR (p^k) = A_k(p)² / k ≥ 0`,   `vR (p^k) = A_k(p)² log p ≥ 0`   (`vR = log · cR`).

Absolute convergence on `Re s > 1` uses only Rankin (`∑_p λ(p)² p^{−a} < ∞`, `a > 1`) and the
Satake bound `‖α_p‖² ≤ p` together with `‖α_p‖² ≤ 2λ(p)² + 2`; no Deligne.

* `exp_LSeries_cR`: `exp (∑ cR(n) n^{−s}) = ζ(2s) R(s)` for `Re s > 1`.
-/
import RamanujanTau.TauPNT.PrimeSum
import RamanujanTau.EdgeNonvanishing.Main

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL RamanujanTau.TauPNT

/-- Coefficients of `log (ζ(2s)R(s))`: `cR (p^k) = A_k(p)²/k`. -/
noncomputable def cR (n : ℕ) : ℝ :=
  if IsPrimePow n then AA n.minFac (n.factorization n.minFac) ^ 2 / (n.factorization n.minFac)
  else 0

/-- The von Mangoldt function of `ζ(2s)R(s)`: `vR (p^k) = A_k(p)² log p`. -/
noncomputable def vR (n : ℕ) : ℝ :=
  if IsPrimePow n then AA n.minFac (n.factorization n.minFac) ^ 2 * Real.log n.minFac else 0

lemma cR_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cR (p ^ (k + 1)) = AA p (k + 1) ^ 2 / (k + 1 : ℕ) := by
  have hpp : IsPrimePow (p ^ (k + 1)) := (Nat.Prime.isPrimePow hp).pow (by omega)
  simp only [cR, hpp, if_true, minFac_pow hp (by omega : k + 1 ≠ 0), factorization_pow_self hp]

lemma vR_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    vR (p ^ (k + 1)) = AA p (k + 1) ^ 2 * Real.log p := by
  have hpp : IsPrimePow (p ^ (k + 1)) := (Nat.Prime.isPrimePow hp).pow (by omega)
  simp only [vR, hpp, if_true, minFac_pow hp (by omega : k + 1 ≠ 0), factorization_pow_self hp]

lemma cR_of_not {n : ℕ} (h : ¬ IsPrimePow n) : cR n = 0 := by simp [cR, h]

lemma vR_of_not {n : ℕ} (h : ¬ IsPrimePow n) : vR n = 0 := by simp [vR, h]

lemma vR_nonneg (n : ℕ) : 0 ≤ vR n := by
  unfold vR
  split_ifs with h
  · exact mul_nonneg (sq_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (Nat.minFac_prime h.ne_one).one_lt.le))
  · exact le_rfl

lemma cR_nonneg (n : ℕ) : 0 ≤ cR n := by
  unfold cR
  split_ifs
  · positivity
  · exact le_rfl

lemma vR_prime {p : ℕ} (hp : p.Prime) : vR p = lam p ^ 2 * Real.log p := by
  have := vR_pow hp 0
  simpa [AA_one] using this

/-- `vR = log · cR`. -/
lemma vR_eq_logMul : (fun n => (vR n : ℂ)) = logMul (fun n => (cR n : ℂ)) := by
  funext n
  simp only [logMul]
  by_cases h : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [vR_pow hp, cR_pow hp]
    have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((p ^ (j + 1) : ℕ) : ℂ) = (((p : ℝ) ^ (j + 1) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity), Real.log_pow]
    push_cast
    field_simp
  · rw [vR_of_not h, cR_of_not h]; simp

lemma term_cR_ppow (s : ℂ) (q : Nat.Primes × ℕ) :
    term (fun n => (cR n : ℂ)) s (ppow q) =
      ((AA q.1 (q.2 + 1) : ℂ) ^ 2 / (q.2 + 1 : ℕ)) * ((q.1 : ℂ) ^ (-s)) ^ (q.2 + 1) := by
  obtain ⟨p, k⟩ := q
  have hp := p.2
  simp only [ppow]
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), cR_pow hp, Nat.cast_pow,
    ← natCast_cpow_natCast_mul, mul_comm ((k + 1 : ℕ) : ℂ), cpow_mul_nat, div_eq_mul_inv,
    ← inv_pow, ← cpow_neg]
  push_cast
  ring

lemma term_cR_zero_of_not {s : ℂ} {n : ℕ} (h : n ∉ Set.range ppow) :
    term (fun n => (cR n : ℂ)) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, cR_of_not (range_ppow h)]; simp

/-- `‖α_p‖² ≤ 2λ(p)² + 2` (from `α = λ − β`, `‖β‖ ≤ 1`). -/
lemma norm_sa_sq_le_lam (p : ℕ) : ‖sa p‖ ^ 2 ≤ 2 * lam p ^ 2 + 2 := by
  have h1 : sa p = (lam p : ℂ) - sb p := by
    have := (sab p).2.1; linear_combination this
  have h2 : ‖sa p‖ ≤ |lam p| + 1 := by
    rw [h1]
    calc ‖(lam p : ℂ) - sb p‖ ≤ ‖(lam p : ℂ)‖ + ‖sb p‖ := norm_sub_le _ _
      _ ≤ |lam p| + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; linarith [(sab p).2.2.2]
  have h3 : 0 ≤ ‖sa p‖ := norm_nonneg _
  have h4 := pow_le_pow_left₀ h3 h2 2
  nlinarith [sq_abs (lam p), abs_nonneg (lam p), sq_nonneg (|lam p| - 1)]

lemma p_mul_rpow {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    (p : ℝ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (1 - σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [sub_eq_add_neg, Real.rpow_add hp0, Real.rpow_one]

lemma p_mul_rpow_sq {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    (p : ℝ) * ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hp0.le,
    show -(2 * σ - 1) = 1 + (-σ * ((2 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_add hp0,
    Real.rpow_one]

/-- **Absolute convergence over prime powers**, `Re s > 1` (no Deligne). -/
lemma summable_norm_term_cR_ppow {s : ℂ} (hs : 1 < s.re) :
    Summable fun q : Nat.Primes × ℕ => ‖term (fun n => (cR n : ℂ)) s (ppow q)‖ := by
  set σ := s.re
  set q0 : ℝ := (2 : ℝ) ^ (1 - σ)
  have hq0 : q0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0p : 0 < q0 := Real.rpow_pos_of_pos (by norm_num) _
  set B1 : Nat.Primes × ℕ → ℝ := fun q => if q.2 = 0 then lam q.1 ^ 2 * (q.1 : ℝ) ^ (-σ) else 0
  set B2 : Nat.Primes × ℕ → ℝ := fun q =>
    ((4 / q0) * ((2 * lam q.1 ^ 2 + 2) * (q.1 : ℝ) ^ (-(2 * σ - 1)))) * q0 ^ q.2
  have hB1 : Summable B1 := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p, 0)) := fun a b h => by
      simpa using h
    refine (hinj.summable_iff (fun q hq => ?_)).mp ?_
    · simp only [B1]
      split_ifs with h
      · exact absurd ⟨q.1, by ext <;> simp [h]⟩ hq
      · rfl
    · simpa [B1, Function.comp_def] using summable_lam_sq hs
  have hB2 : Summable B2 := by
    refine Summable.mul_of_nonneg
      (f := fun p : Nat.Primes => (4 / q0) * ((2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1))))
      (g := fun k : ℕ => q0 ^ k) ?_ (summable_geometric_of_lt_one hq0p.le hq0) ?_ ?_
    · have h1 := (summable_lam_sq (a := 2 * σ - 1) (by linarith)).mul_left 2
      have h2 := (summable_primes_rpow (a := 2 * σ - 1) (by linarith)).mul_left 2
      refine ((h1.add h2).mul_left (4 / q0)).congr fun p => ?_
      ring
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hB1.add hB2)
  obtain ⟨p, k⟩ := q
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [term_cR_ppow]
  simp only [B1, B2]
  have hY : ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-σ) := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast, hY, sq_abs]
  set y : ℝ := (p : ℝ) ^ (-σ)
  have hy0 : 0 ≤ y := by positivity
  have hB2nn : 0 ≤ (4 / q0) * ((2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1))) * q0 ^ k := by
    positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [if_true, zero_add, pow_one, Nat.cast_one, div_one, AA_one]
    linarith
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [hk0, if_false, zero_add]
    set x : ℝ := ‖sa p‖ ^ 2 * y
    have hx0 : 0 ≤ x := by positivity
    have hxq : x ≤ q0 := by
      have h1 : x ≤ (p : ℝ) * y := mul_le_mul_of_nonneg_right (norm_sa_sq_le hp) hy0
      rw [p_mul_rpow hp] at h1
      exact h1.trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith))
    have hxsq : x ^ 2 ≤ (2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1)) := by
      have h1 : x ^ 2 = ‖sa p‖ ^ 2 * (‖sa p‖ ^ 2 * y ^ 2) := by simp only [x]; ring
      have h2 : ‖sa p‖ ^ 2 * y ^ 2 ≤ (p : ℝ) * y ^ 2 :=
        mul_le_mul_of_nonneg_right (norm_sa_sq_le hp) (by positivity)
      rw [p_mul_rpow_sq hp] at h2
      rw [h1]
      exact mul_le_mul (norm_sa_sq_le_lam p) h2 (by positivity) (by positivity)
    have hA : AA p (k + 1) ^ 2 ≤ 4 * (‖sa p‖ ^ 2) ^ (k + 1) := by
      have h := abs_AA_le p (k + 1)
      have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at h'
      calc AA p (k + 1) ^ 2 ≤ (2 * ‖sa p‖ ^ (k + 1)) ^ 2 := h'
        _ = 4 * (‖sa p‖ ^ 2) ^ (k + 1) := by ring
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    have e1 : AA p (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ≤ 4 * (‖sa p‖ ^ 2) ^ (k + 1) :=
      (div_le_self (sq_nonneg _) hk1).trans hA
    have e3 : x ^ (k + 1) ≤ (2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1)) * q0 ^ (k - 1) := by
      have : x ^ (k + 1) = x ^ 2 * x ^ (k - 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_le_mul hxsq (pow_le_pow_left₀ hx0 hxq _) (by positivity) (by positivity)
    have e4 : q0 ^ k = q0 * q0 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    calc AA p (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) * y ^ (k + 1)
        ≤ 4 * (‖sa p‖ ^ 2) ^ (k + 1) * y ^ (k + 1) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = 4 * x ^ (k + 1) := by simp only [x]; rw [mul_pow]; ring
      _ ≤ 4 * ((2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1)) * q0 ^ (k - 1)) := by linarith
      _ = (4 / q0) * ((2 * lam p ^ 2 + 2) * (p : ℝ) ^ (-(2 * σ - 1))) * q0 ^ k := by
          rw [e4]; field_simp

/-- `∑ cR(n) n^{−s}` converges absolutely for `Re s > 1`. -/
theorem LSeriesSummable_cR {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (cR n : ℂ)) s := by
  have h := (summable_norm_term_cR_ppow hs).of_norm
  exact (ppow_injective.summable_iff (fun _ hn => term_cR_zero_of_not hn)).mp h

lemma abscissa_cR_le : abscissaOfAbsConv (fun n => (cR n : ℂ)) ≤ 1 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_cR (by simpa using hy)

lemma abscissa_vR_le : abscissaOfAbsConv (fun n => (vR n : ℂ)) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  rw [vR_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re
    (abscissa_cR_le.trans_lt (by simpa using (by exact_mod_cast hy : (1 : EReal) < y)))

lemma LSeriesSummable_vR {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (vR n : ℂ)) s := by
  rw [vR_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re (abscissa_cR_le.trans_lt (by exact_mod_cast hs))

/-- The local logarithm of `ζ(2s)R(s)`. -/
lemma local_logR {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∃ ℓ : ℂ, HasSum (fun k => term (fun n => (cR n : ℂ)) s (ppow (p, k))) ℓ ∧
      cexp ℓ = fR s p := by
  have hp := p.2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set Y := ((p : ℕ) : ℂ) ^ (-s)
  have hYn : ‖Y‖ = (p : ℝ) ^ (-s.re) := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  have hpY : (p : ℝ) * ‖Y‖ < 1 := by
    rw [hYn, p_mul_rpow hp]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hY1 : ‖Y‖ < 1 := by nlinarith [norm_nonneg Y]
  have hαY : ‖sa p ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]
    have := mul_le_mul_of_nonneg_right (norm_sa_sq_le hp) (norm_nonneg Y)
    linarith
  have hβY : ‖sb p ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]
    have hb : ‖sb p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (sb p), (sab p).2.2.2]
    have := mul_le_mul_of_nonneg_right hb (norm_nonneg Y)
    linarith
  obtain ⟨h1, h2⟩ := list_log [Y, Y, sa p ^ 2 * Y, sb p ^ 2 * Y] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hY1
    · exact hY1
    · exact hαY
    · exact hβY)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one] at h1 h2
  refine ⟨_, ?_, h2.symm.trans ?_⟩
  · have h1' := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
      sub_zero] at h1'
    convert h1' using 1
    funext k
    rw [term_cR_ppow, AA_eq]
    have hab : sa p ^ (k + 1) * sb p ^ (k + 1) = 1 := by rw [← mul_pow, (sab p).1, one_pow]
    have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    simp only [mul_pow, ← pow_mul]
    push_cast at hk ⊢
    field_simp
    have e1 : sa p ^ (2 * (k + 1)) = (sa p ^ (k + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
    have e2 : sb p ^ (2 * (k + 1)) = (sb p ^ (k + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e1, e2]
    linear_combination (2 * Y ^ (k + 1)) * hab
  · rw [fR, rs_local hs hp (sab p).1 (sab p).2.1 (norm_sa_sq_le hp) (sab p).2.2.2]
    ring

/-- **`exp(∑ cR(n) n^{−s}) = ζ(2s) R(s)`** for `Re s > 1` (no Deligne). -/
theorem exp_LSeries_cR {s : ℂ} (hs : 1 < s.re) :
    cexp (LSeries (fun n => (cR n : ℂ)) s) = riemannZeta (2 * s) * RS s := by
  choose ℓ hℓ1 hℓ2 using fun p : Nat.Primes => local_logR hs p
  have hsum : HasSum (term (fun n => (cR n : ℂ)) s) (LSeries (fun n => (cR n : ℂ)) s) :=
    (LSeriesSummable_cR hs).LSeriesHasSum
  have hprod : HasSum (term (fun n => (cR n : ℂ)) s ∘ ppow) (LSeries (fun n => (cR n : ℂ)) s) :=
    (ppow_injective.hasSum_iff (fun _ hn => term_cR_zero_of_not hn)).mpr hsum
  have hfib : HasSum ℓ (LSeries (fun n => (cR n : ℂ)) s) :=
    hprod.prod_fiberwise fun p => hℓ1 p
  have hE := hfib.cexp
  have heq : (cexp ∘ ℓ) = fun p : Nat.Primes => fR s p := funext fun p => hℓ2 p
  rw [heq] at hE
  exact hE.unique (fR_hasProd hs)

end RamanujanTau.TauPNTUncond
