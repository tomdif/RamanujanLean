/-
# `log L(s) = ∑ cc(n) n^{−s}` on `Re s > 1`

For `Re s > 1` (normalized), the series `∑ cc(n) n^{−s}` converges absolutely, using only
Rankin's `∑ |τ(n)| n^{−σ−11/2} < ∞` (for the primes) and the Satake bound `‖α_p‖² ≤ p`
(for the higher prime powers); no Deligne.  Its exponential is `L(s)`:

`exp (∑ cc(n) n^{−s}) = L(s)`   (`exp_LSeries_cc`).
-/
import RamanujanTau.TauPNT.Defs

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- `|λ(p)| p^{−σ} = |τ(p)| / p^{σ+11/2}`. -/
lemma abs_lam_mul_rpow {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    |lam p| * (p : ℝ) ^ (-σ) = |(tau p : ℝ)| / (p : ℝ) ^ (σ + 11 / 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [lam, uu, pow_one, rr]
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp0 _), Real.rpow_add hp0,
    Real.rpow_neg hp0.le, Real.rpow_neg hp0.le]
  field_simp

/-- `∑_p |λ(p)| p^{−σ} < ∞` for `σ > 1` (Rankin). -/
lemma summable_abs_lam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => |lam p| * (p : ℝ) ^ (-σ) := by
  have h := (HeckeConvex.summable_abs_tau_div_rpow (σ := σ + 11 / 2) (by linarith)).comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  refine h.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [abs_lam_mul_rpow p.2]

/-- `∑_p p^{−a} < ∞` for `a > 1`. -/
lemma summable_primes_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun p : Nat.Primes => (p : ℝ) ^ (-a) :=
  (Real.summable_nat_rpow.mpr (by linarith)).comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))

lemma term_cc_ppow (s : ℂ) (q : Nat.Primes × ℕ) :
    term (fun n => (cc n : ℂ)) s (ppow q) =
      ((AA q.1 (q.2 + 1) : ℂ) / (q.2 + 1 : ℕ)) * ((q.1 : ℂ) ^ (-s)) ^ (q.2 + 1) := by
  obtain ⟨p, k⟩ := q
  have hp := p.2
  simp only [ppow]
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), cc_pow hp, Nat.cast_pow,
    ← natCast_cpow_natCast_mul, mul_comm ((k + 1 : ℕ) : ℂ), cpow_mul_nat, div_eq_mul_inv,
    ← inv_pow, ← cpow_neg]
  push_cast
  ring

lemma term_cc_zero_of_not {s : ℂ} {n : ℕ} (h : n ∉ Set.range ppow) :
    term (fun n => (cc n : ℂ)) s n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, cc_of_not (range_ppow h)]; simp

/-- `‖α_p p^{−s}‖² ≤ p^{1−2σ}`. -/
lemma norm_sa_Y_sq {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (‖sa p‖ * ‖(p : ℂ) ^ (-s)‖) ^ 2 ≤ (p : ℝ) ^ (1 - 2 * s.re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [norm_natCast_cpow_of_pos hp.pos, neg_re, mul_pow]
  have h1 : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
  rw [h1, show (1 - 2 * s.re) = 1 + (-(2 * s.re)) by ring, Real.rpow_add hp0, Real.rpow_one]
  exact mul_le_mul_of_nonneg_right (norm_sa_sq_le hp) (by positivity)

/-- The uniform ratio `q₀ = 2^{(1−2σ)/2} < 1`. -/
lemma norm_sa_Y_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖sa p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ ((1 - 2 * s.re) / 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h := norm_sa_Y_sq hp s
  have h2 : (p : ℝ) ^ (1 - 2 * s.re) ≤ (2 : ℝ) ^ (1 - 2 * s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h3 : ((2 : ℝ) ^ ((1 - 2 * s.re) / 2)) ^ 2 = (2 : ℝ) ^ (1 - 2 * s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  have h0 : 0 ≤ ‖sa p‖ * ‖(p : ℂ) ^ (-s)‖ := by positivity
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((1 - 2 * s.re) / 2)]

lemma q0_lt_one {σ : ℝ} (hσ : 1 < σ) : (2 : ℝ) ^ ((1 - 2 * σ) / 2) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- **Absolute convergence over prime powers**, `Re s > 1`. -/
lemma summable_norm_term_cc_ppow {s : ℂ} (hs : 1 < s.re) :
    Summable fun q : Nat.Primes × ℕ => ‖term (fun n => (cc n : ℂ)) s (ppow q)‖ := by
  set σ := s.re
  set q0 : ℝ := (2 : ℝ) ^ ((1 - 2 * σ) / 2)
  have hq0 : q0 < 1 := q0_lt_one hs
  have hq0p : 0 < q0 := Real.rpow_pos_of_pos (by norm_num) _
  -- majorant
  set B1 : Nat.Primes × ℕ → ℝ := fun q => if q.2 = 0 then |lam q.1| * (q.1 : ℝ) ^ (-σ) else 0
  set B2 : Nat.Primes × ℕ → ℝ := fun q => ((2 / q0) * (q.1 : ℝ) ^ (1 - 2 * σ)) * q0 ^ q.2
  have hB1 : Summable B1 := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p, 0)) := fun a b h => by
      simpa using h
    refine (hinj.summable_iff (fun q hq => ?_)).mp ?_
    · simp only [B1]
      split_ifs with h
      · exact absurd ⟨q.1, by ext <;> simp [h]⟩ hq
      · rfl
    · simpa [B1, Function.comp_def] using summable_abs_lam hs
  have hB2 : Summable B2 := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => (2 / q0) * (p : ℝ) ^ (1 - 2 * σ))
      (g := fun k : ℕ => q0 ^ k) ?_ (summable_geometric_of_lt_one hq0p.le hq0) ?_ ?_
    · have := (summable_primes_rpow (a := 2 * σ - 1) (by linarith)).mul_left (2 / q0)
      refine this.congr fun p => ?_
      congr 2; ring
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hB1.add hB2)
  obtain ⟨p, k⟩ := q
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [term_cc_ppow]
  simp only [B1, B2]
  set x := ‖sa p‖ * ‖(p : ℂ) ^ (-s)‖
  have hx0 : 0 ≤ x := by positivity
  have hxq : x ≤ q0 := norm_sa_Y_le hp hs
  have hxsq : x ^ 2 ≤ (p : ℝ) ^ (1 - 2 * σ) := norm_sa_Y_sq hp s
  have hY : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-σ) := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [if_true, zero_add, pow_one, Nat.cast_one, div_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, hY, AA_one, pow_zero, mul_one]
    have : 0 ≤ (2 / q0) * (p : ℝ) ^ (1 - 2 * σ) := by positivity
    linarith
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [hk0, if_false, zero_add]
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hA := abs_AA_le p (k + 1)
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    have e1 : |AA p (k + 1)| / ((k + 1 : ℕ) : ℝ) ≤ 2 * ‖sa p‖ ^ (k + 1) :=
      (div_le_self (abs_nonneg _) hk1).trans hA
    have e2 : 2 * ‖sa p‖ ^ (k + 1) * ‖(p : ℂ) ^ (-s)‖ ^ (k + 1) = 2 * x ^ (k + 1) := by
      simp only [x]; rw [mul_pow]; ring
    have e3 : x ^ (k + 1) ≤ (p : ℝ) ^ (1 - 2 * σ) * q0 ^ (k - 1) := by
      have : x ^ (k + 1) = x ^ 2 * x ^ (k - 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_le_mul hxsq (pow_le_pow_left₀ hx0 hxq _) (by positivity) (by positivity)
    have e4 : q0 ^ k = q0 * q0 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    calc |AA p (k + 1)| / ((k + 1 : ℕ) : ℝ) * ‖(p : ℂ) ^ (-s)‖ ^ (k + 1)
        ≤ 2 * ‖sa p‖ ^ (k + 1) * ‖(p : ℂ) ^ (-s)‖ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = 2 * x ^ (k + 1) := e2
      _ ≤ 2 * ((p : ℝ) ^ (1 - 2 * σ) * q0 ^ (k - 1)) := by linarith
      _ = 2 / q0 * (p : ℝ) ^ (1 - 2 * σ) * q0 ^ k := by rw [e4]; field_simp

/-- `∑ cc(n) n^{−s}` converges absolutely for `Re s > 1`. -/
theorem LSeriesSummable_cc {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (cc n : ℂ)) s := by
  have h := (summable_norm_term_cc_ppow hs).of_norm
  exact (ppow_injective.summable_iff (fun _ hn => term_cc_zero_of_not hn)).mp h

lemma abscissa_cc_le : abscissaOfAbsConv (fun n => (cc n : ℂ)) ≤ 1 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_cc (by simpa using hy)

/-- The local logarithm `ℓ_p(s) = −log(1 − α_p p^{−s}) − log(1 − β_p p^{−s})`. -/
noncomputable def ellp (s : ℂ) (p : ℕ) : ℂ :=
  -log (1 - sa p * (p : ℂ) ^ (-s)) + -log (1 - sb p * (p : ℂ) ^ (-s))

lemma local_log {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    HasSum (fun k => term (fun n => (cc n : ℂ)) s (ppow (p, k))) (ellp s p) ∧
      cexp (ellp s p) = (HeckeZeros.localPoly (s + 11 / 2) p)⁻¹ := by
  have hp := p.2
  set Y := ((p : ℕ) : ℂ) ^ (-s)
  have hxq := norm_sa_Y_le hp hs
  have hq := q0_lt_one hs
  have hαY : ‖sa p * Y‖ < 1 := by rw [norm_mul]; linarith
  have hβY : ‖sb p * Y‖ < 1 := by
    rw [norm_mul]
    have h1 : ‖sb p‖ * ‖Y‖ ≤ ‖sa p‖ * ‖Y‖ :=
      mul_le_mul_of_nonneg_right ((sab p).2.2.2.trans (sab p).2.2.1) (norm_nonneg _)
    linarith
  obtain ⟨h1, h2⟩ := list_log [sa p * Y, sb p * Y] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hαY
    · exact hβY)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one] at h1 h2
  refine ⟨?_, ?_⟩
  · have h1' := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
      sub_zero] at h1'
    convert h1' using 1
    funext k
    rw [term_cc_ppow, AA_eq]
    simp only [mul_pow]
    push_cast
    ring
  · rw [ellp, ← h2, tau_local (s + 11 / 2) hp (sab p).1 (sab p).2.1]
    have : (p : ℂ) ^ (-(s + 11 / 2 - 11 / 2)) = Y := by congr 1; ring
    rw [this]

/-- **`exp(∑ cc(n)n^{−s}) = L(s)`** for `Re s > 1`. -/
theorem exp_LSeries_cc {s : ℂ} (hs : 1 < s.re) :
    cexp (LSeries (fun n => (cc n : ℂ)) s) = Lnorm s := by
  have hsum : HasSum (term (fun n => (cc n : ℂ)) s) (LSeries (fun n => (cc n : ℂ)) s) :=
    (LSeriesSummable_cc hs).LSeriesHasSum
  have hprod : HasSum (term (fun n => (cc n : ℂ)) s ∘ ppow) (LSeries (fun n => (cc n : ℂ)) s) :=
    (ppow_injective.hasSum_iff (fun _ hn => term_cc_zero_of_not hn)).mpr hsum
  have hfib : HasSum (fun p : Nat.Primes => ellp s p) (LSeries (fun n => (cc n : ℂ)) s) :=
    hprod.prod_fiberwise fun p => (local_log hs p).1
  have hE := hfib.cexp
  have hs' : 13 / 2 < (s + 11 / 2).re := by simp; linarith
  have hL := HeckeZeros.tauL_eulerProduct hs'
  have heq : (cexp ∘ fun p : Nat.Primes => ellp s p) = fun p : Nat.Primes =>
      (1 - tauC p * (p : ℂ) ^ (-(s + 11 / 2)) +
        (p : ℂ) ^ 11 * ((p : ℂ) ^ (-(s + 11 / 2))) ^ 2)⁻¹ := by
    funext p
    simp only [Function.comp_apply, (local_log hs p).2, HeckeZeros.localPoly]
  rw [heq] at hE
  exact hE.unique hL

end RamanujanTau.TauPNT
