/-
# PNT machinery for abstract normalized data (generalizes `TauPNT/Defs, LogEuler, LogDeriv, PrimeSum`)

Satake parameters `α_p, β_p` (`α_pβ_p = 1`, `α_p + β_p = λ(p)`, `‖α_p‖² ≤ p` without Deligne),
`A_k(p) = α_p^k + β_p^k`, `cc(p^k) = A_k/k`, `vM(p^k) = A_k log p`;

* `exp_LSeries_cc`: `exp(∑ cc(n)n^{−s}) = L(s)` on `Re s > 1`;
* `negLogDeriv_eq_LSeries`: `−L'/L = ∑ vM(n) n^{−s}` on `Re s > 1`;
* `continuousOn_negLogDeriv` (`[RealEdge]`): `−L'/L` continuous on `Re s ≥ 1`;
* `primeSum_tendsto` (`[RealEdge]`): the smoothed PNT `∑_p λ(p) log p p^{−σ} → finite` as `σ → 1⁺`.

`RealEdge` is the single named hypothesis `L(1) ≠ 0` (the real edge point; see `RealPoint.lean`).
Proofs copied from `TauPNT/` with `τ`-specific inputs replaced by the `EData` fields.
-/
import RamanujanTau.EigenformEdge.Edge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.EigenformEdge

open Complex Filter Topology LSeries
open EData

variable [EData]

/-- **Named hypothesis**: the real edge value `L(1) ≠ 0` (i.e. `L(f,(k+1)/2) ≠ 0`). -/
class RealEdge [EData] : Prop where
  ne : EData.L 1 ≠ 0



/-- The normalized L-function. -/
noncomputable def Lnorm (s : ℂ) : ℂ := L s

lemma Lnorm_differentiable : Differentiable ℂ Lnorm := L_diff

lemma Lnorm_ne_zero [RealEdge] {s : ℂ} (hs : 1 ≤ s.re) : Lnorm s ≠ 0 :=
  L_ne_zero_of_ge RealEdge.ne hs

/-- Satake parameter `α_p`. -/
noncomputable def sa (p : ℕ) : ℂ := Classical.choose (EdgeNonvanishing.satake (lam p))

/-- Satake parameter `β_p`. -/
noncomputable def sb (p : ℕ) : ℂ := Classical.choose (Classical.choose_spec (EdgeNonvanishing.satake (lam p)))

lemma sab (p : ℕ) :
    sa p * sb p = 1 ∧ sa p + sb p = lam p ∧ 1 ≤ ‖sa p‖ ∧ ‖sb p‖ ≤ 1 :=
  Classical.choose_spec (Classical.choose_spec (EdgeNonvanishing.satake (lam p)))

lemma norm_sa_sq_le {p : ℕ} (hp : p.Prime) : ‖sa p‖ ^ 2 ≤ p :=
  alpha_sq_le hp (sab p).1 (sab p).2.1 (sab p).2.2.2

/-- `A_k(p) = α_p^k + β_p^k`, as a real number. -/
noncomputable def AA (p k : ℕ) : ℝ := EdgeNonvanishing.pseq (lam p) k

lemma AA_eq (p k : ℕ) : (AA p k : ℂ) = sa p ^ k + sb p ^ k :=
  (EdgeNonvanishing.pow_add_pow_eq_pseq (sab p).2.1 (sab p).1 k).symm

lemma AA_one (p : ℕ) : AA p 1 = lam p := rfl

lemma AA_two (p : ℕ) : AA p 2 = lam p ^ 2 - 2 := by
  simp only [AA, EdgeNonvanishing.pseq]; ring

lemma abs_AA_le (p k : ℕ) : |AA p k| ≤ 2 * ‖sa p‖ ^ k := by
  have h := AA_eq p k
  have h1 : |AA p k| = ‖sa p ^ k + sb p ^ k‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  have hb : ‖sb p‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (sab p).2.2.2
  have ha : 1 ≤ ‖sa p‖ ^ k := one_le_pow₀ (sab p).2.2.1
  calc ‖sa p ^ k + sb p ^ k‖ ≤ ‖sa p‖ ^ k + ‖sb p‖ ^ k := by
        rw [← norm_pow, ← norm_pow]; exact norm_add_le _ _
    _ ≤ 2 * ‖sa p‖ ^ k := by linarith

/-- Prime powers: `minFac (p^k) = p` and `v_p(p^k) = k`. -/
lemma minFac_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (p ^ k).minFac = p :=
  Nat.Prime.pow_minFac hp hk

lemma factorization_pow_self {p k : ℕ} (hp : p.Prime) : (p ^ k).factorization p = k := by
  rw [Nat.Prime.factorization_pow hp]; simp

/-- Coefficients of `log L`: `cc (p^k) = A_k(p)/k`. -/
noncomputable def cc (n : ℕ) : ℝ :=
  if IsPrimePow n then AA n.minFac (n.factorization n.minFac) / (n.factorization n.minFac) else 0

/-- The von Mangoldt function of `Δ`: `vM (p^k) = A_k(p) log p`. -/
noncomputable def vM (n : ℕ) : ℝ :=
  if IsPrimePow n then AA n.minFac (n.factorization n.minFac) * Real.log n.minFac else 0

lemma cc_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : cc (p ^ (k + 1)) = AA p (k + 1) / (k + 1 : ℕ) := by
  have hpp : IsPrimePow (p ^ (k + 1)) := (Nat.Prime.isPrimePow hp).pow (by omega)
  simp only [cc, hpp, if_true, minFac_pow hp (by omega : k + 1 ≠ 0), factorization_pow_self hp]

lemma vM_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : vM (p ^ (k + 1)) = AA p (k + 1) * Real.log p := by
  have hpp : IsPrimePow (p ^ (k + 1)) := (Nat.Prime.isPrimePow hp).pow (by omega)
  simp only [vM, hpp, if_true, minFac_pow hp (by omega : k + 1 ≠ 0), factorization_pow_self hp]

lemma vM_prime {p : ℕ} (hp : p.Prime) : vM p = lam p * Real.log p := by
  have := vM_pow hp 0
  simpa [AA_one] using this

lemma cc_of_not {n : ℕ} (h : ¬ IsPrimePow n) : cc n = 0 := by simp [cc, h]

lemma vM_of_not {n : ℕ} (h : ¬ IsPrimePow n) : vM n = 0 := by simp [vM, h]

/-- `vM = log · cc`. -/
lemma vM_eq_logMul : (fun n => (vM n : ℂ)) = logMul (fun n => (cc n : ℂ)) := by
  funext n
  simp only [logMul]
  by_cases h : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [vM_pow hp, cc_pow hp]
    have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((p ^ (j + 1) : ℕ) : ℂ) = (((p : ℝ) ^ (j + 1) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity), Real.log_pow]
    push_cast
    field_simp
  · rw [vM_of_not h, cc_of_not h]; simp

/-- The prime-power embedding `(p, k) ↦ p^{k+1}`. -/
def ppow (q : Nat.Primes × ℕ) : ℕ := (q.1 : ℕ) ^ (q.2 + 1)

lemma ppow_injective : Function.Injective ppow := by
  rintro ⟨p, k⟩ ⟨q, l⟩ h
  simp only [ppow] at h
  have hp := p.2
  have hq := q.2
  have h1 : p = q := by
    apply Subtype.ext
    have := congrArg Nat.minFac h
    rwa [minFac_pow hp (by omega), minFac_pow hq (by omega)] at this
  subst h1
  have := congrArg (fun n => n.factorization p) h
  simp only [factorization_pow_self hp] at this
  simp only [Prod.mk.injEq, true_and]
  omega

lemma range_ppow {n : ℕ} (h : n ∉ Set.range ppow) : ¬ IsPrimePow n := by
  intro hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn
  exact h ⟨(⟨p, hp⟩, k - 1), by simp only [ppow]; congr 1; omega⟩





/-- `∑_p |λ(p)| p^{−σ} < ∞` for `σ > 1`. -/
lemma summable_abs_lam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => |lam p| * (p : ℝ) ^ (-σ) := by
  have h := (summable_abs_lam_rpow hσ).comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  refine h.congr fun p => ?_
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hp0.le, div_eq_mul_inv]

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
      cexp (ellp s p) = (localPoly s p)⁻¹ := by
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
  obtain ⟨h1, h2⟩ := EdgeNonvanishing.list_log [sa p * Y, sb p * Y] (by
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
  · rw [ellp, ← h2, L_local s p (sab p).1 (sab p).2.1]

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
  have hL := L_eulerProduct hs
  have heq : (cexp ∘ fun p : Nat.Primes => ellp s p) = fun p : Nat.Primes => (localPoly s p)⁻¹ := by
    funext p
    simp only [Function.comp_apply, (local_log hs p).2]
  rw [heq] at hE
  exact hE.unique hL





/-- `−L'/L`. -/
noncomputable def negLogDeriv (s : ℂ) : ℂ := -deriv Lnorm s / Lnorm s

lemma abscissa_vM_le : abscissaOfAbsConv (fun n => (vM n : ℂ)) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  rw [vM_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re (abscissa_cc_le.trans_lt (by simpa using (by exact_mod_cast hy : (1 : EReal) < y)))

lemma LSeriesSummable_vM {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (vM n : ℂ)) s := by
  rw [vM_eq_logMul]
  exact LSeriesSummable_logMul_of_lt_re (abscissa_cc_le.trans_lt (by exact_mod_cast hs))

/-- **`−L'/L(s) = ∑ Λ_Δ(n) n^{−s}`** for `Re s > 1`. -/
theorem negLogDeriv_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    negLogDeriv s = LSeries (fun n => (vM n : ℂ)) s := by
  set G := LSeries (fun n => (cc n : ℂ))
  have hab : abscissaOfAbsConv (fun n => (cc n : ℂ)) < s.re :=
    abscissa_cc_le.trans_lt (by exact_mod_cast hs)
  have hG : HasDerivAt G (-LSeries (logMul fun n => (cc n : ℂ)) s) s := LSeries_hasDerivAt hab
  have hev : (fun z => cexp (G z)) =ᶠ[𝓝 s] Lnorm := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact exp_LSeries_cc hz
  have hd : HasDerivAt Lnorm (cexp (G s) * -LSeries (logMul fun n => (cc n : ℂ)) s) s :=
    (hG.cexp).congr_of_eventuallyEq hev.symm
  have hE : cexp (G s) = Lnorm s := exp_LSeries_cc hs
  rw [negLogDeriv, hd.deriv, hE, vM_eq_logMul]
  have h0 : Lnorm s ≠ 0 := L_ne_zero_of_gt hs
  field_simp

lemma deriv_Lnorm_continuous : Continuous (deriv Lnorm) :=
  continuousOn_univ.mp
    ((Lnorm_differentiable.differentiableOn (s := Set.univ)).deriv isOpen_univ).continuousOn

/-- **`−L'/L` is continuous on `Re s ≥ 1`** (no pole: `L(1+it) ≠ 0`). -/
theorem continuousOn_negLogDeriv [RealEdge] : ContinuousOn negLogDeriv {s | 1 ≤ s.re} := by
  intro s hs
  have h0 : Lnorm s ≠ 0 := Lnorm_ne_zero hs
  exact ((deriv_Lnorm_continuous.continuousAt.neg).div
    Lnorm_differentiable.continuous.continuousAt h0).continuousWithinAt

lemma continuousAt_negLogDeriv [RealEdge] {s : ℂ} (hs : 1 ≤ s.re) : ContinuousAt negLogDeriv s :=
  (deriv_Lnorm_continuous.continuousAt.neg).div Lnorm_differentiable.continuous.continuousAt
    (Lnorm_ne_zero hs)





/-- The smoothed prime sum `∑_p λ(p) log p · p^{−σ}`. -/
noncomputable def primeSum (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, lam p * Real.log p * (p : ℝ) ^ (-σ)

/-- The map `(p, k) ↦ p^{k+2}`. -/
def ppow2 (q : Nat.Primes × ℕ) : ℕ := (q.1 : ℕ) ^ (q.2 + 2)

lemma ppow2_injective : Function.Injective ppow2 := by
  have h : ppow2 = ppow ∘ fun q : Nat.Primes × ℕ => (q.1, q.2 + 1) := by
    funext q; simp [ppow2, ppow]
  rw [h]
  refine ppow_injective.comp fun a b hab => ?_
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.1 (by omega)

/-- The ratio `r = 2^{−1/2}`. -/
noncomputable def rr2 : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))

lemma rr2_pos : 0 < rr2 := Real.rpow_pos_of_pos (by norm_num) _

lemma rr2_lt_one : rr2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The dominating function for the tail. -/
noncomputable def Mb (q : Nat.Primes × ℕ) : ℝ :=
  (if q.2 = 0 then 4 * (lam q.1 ^ 2 + 2) * (q.1 : ℝ) ^ (-(7 / 4 : ℝ)) else 0) +
    (8 / rr2) * (q.1 : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ q.2

lemma summable_lam_sq {a : ℝ} (ha : 1 < a) :
    Summable fun p : Nat.Primes => lam p ^ 2 * (p : ℝ) ^ (-a) := by
  have h := (rs_summable (s := (a : ℂ)) (by simpa using ha)).norm.comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  refine h.congr fun p => ?_
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [Function.comp_apply, norm_term_eq, hp.ne_zero, if_false, ofReal_re]
  have e : rsb (p : ℕ) = lam p ^ 2 := rfl
  rw [rsB, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rsb_nonneg _), e,
    Real.rpow_neg hp0.le, div_eq_mul_inv]

lemma summable_Mb : Summable Mb := by
  have hB1 : Summable fun q : Nat.Primes × ℕ =>
      if q.2 = 0 then 4 * (lam q.1 ^ 2 + 2) * (q.1 : ℝ) ^ (-(7 / 4 : ℝ)) else 0 := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p, 0)) := fun a b h => by
      simpa using h
    refine (hinj.summable_iff (fun q hq => ?_)).mp ?_
    · split_ifs with h
      · exact absurd ⟨q.1, by ext <;> simp [h]⟩ hq
      · rfl
    · simp only [Function.comp_def, if_true]
      have h1 := (summable_lam_sq (a := 7 / 4) (by norm_num)).mul_left 4
      have h2 := (summable_primes_rpow (a := 7 / 4) (by norm_num)).mul_left 8
      refine (h1.add h2).congr fun p => ?_
      ring
  have hB2 : Summable fun q : Nat.Primes × ℕ => (8 / rr2) * (q.1 : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ q.2 := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => (8 / rr2) * (p : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => rr2 ^ k) ((summable_primes_rpow (a := 5 / 4) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one rr2_pos.le rr2_lt_one) ?_ ?_
    · intro p; simp only [Pi.zero_apply]; have := rr2_pos; positivity
    · intro k; simp only [Pi.zero_apply]; have := rr2_pos; positivity
  exact hB1.add hB2

lemma norm_sa_le_sqrt {p : ℕ} (hp : p.Prime) : ‖sa p‖ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsq : ((p : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have := norm_sa_sq_le hp
  rw [← hsq] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp this

lemma log_le_quarter {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 4)
  linarith [show x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) by ring]

/-- **Uniform domination of the tail on `σ ≥ 1`.** -/
lemma norm_term_vM_ppow2_le {σ : ℝ} (hσ : 1 ≤ σ) (q : Nat.Primes × ℕ) :
    ‖term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q)‖ ≤ Mb q := by
  obtain ⟨p, k⟩ := q
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog := log_le_quarter hp0.le
  simp only [ppow2, Mb]
  rw [norm_term_eq, if_neg (pow_ne_zero _ hp.ne_zero), ofReal_re, vM_pow hp (k + 1),
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0]
  set N : ℝ := ((p ^ (k + 2) : ℕ) : ℝ)
  have hN : N = (p : ℝ) ^ (k + 2) := by simp [N]
  have hN1 : 1 ≤ N := by rw [hN]; exact one_le_pow₀ hp1
  have hNσ : N ≤ N ^ σ := Real.self_le_rpow_of_one_le hN1 hσ
  have hNpos : 0 < N := by linarith
  have step1 : |AA p (k + 1 + 1)| * Real.log p / N ^ σ ≤ |AA p (k + 2)| * Real.log p / N :=
    div_le_div_of_nonneg_left (by positivity) hNpos hNσ
  refine step1.trans ?_
  have hB2 : 0 ≤ 8 / rr2 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ k := by
    have := rr2_pos; positivity
  have h74 : (p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hp0]; norm_num
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [if_true, zero_add]
    have hA : |AA p 2| ≤ lam p ^ 2 + 2 := by
      rw [AA_two, abs_le]; constructor <;> nlinarith [sq_nonneg (lam p)]
    have : |AA p 2| * Real.log p / N ≤ 4 * (lam p ^ 2 + 2) * (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
      rw [hN, ← h74, div_le_iff₀ (by positivity)]
      have e : 4 * (lam p ^ 2 + 2) * ((p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ 2) * (p : ℝ) ^ 2 =
          (lam p ^ 2 + 2) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) := by field_simp
      rw [e]
      exact mul_le_mul hA hlog hlog0 (by positivity)
    linarith
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [hk0, if_false, zero_add]
    set t : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
    have ht0 : 0 ≤ t := by positivity
    have htr : t ≤ rr2 := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have hat : ‖sa p‖ / p ≤ t := by
      rw [div_le_iff₀ hp0]
      have : t * p = (p : ℝ) ^ (1 / 2 : ℝ) := by
        simp only [t]
        rw [show (p : ℝ) ^ (-(1 / 2 : ℝ)) * p = (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hp0]
        norm_num
      rw [this]; exact norm_sa_le_sqrt hp
    have hA : |AA p (k + 2)| / N ≤ 2 * t ^ (k + 2) := by
      rw [hN, div_le_iff₀ (by positivity)]
      calc |AA p (k + 2)| ≤ 2 * ‖sa p‖ ^ (k + 2) := abs_AA_le p (k + 2)
        _ = 2 * (‖sa p‖ / p) ^ (k + 2) * (p : ℝ) ^ (k + 2) := by
          rw [div_pow]; field_simp
        _ ≤ 2 * t ^ (k + 2) * (p : ℝ) ^ (k + 2) := by
          gcongr
    have ht3 : t ^ 3 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      simp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    have htk : t ^ (k + 2) ≤ t ^ 3 * rr2 ^ (k - 1) := by
      have : t ^ (k + 2) = t ^ 3 * t ^ (k - 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 htr _) (by positivity)
    have hrk : rr2 ^ k = rr2 * rr2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have h54 : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) = (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hp0]; norm_num
    have hr0 := rr2_pos
    calc |AA p (k + 2)| * Real.log p / N = (|AA p (k + 2)| / N) * Real.log p := by ring
      _ ≤ (2 * t ^ (k + 2)) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hA hlog hlog0 (by positivity)
      _ ≤ (2 * (t ^ 3 * rr2 ^ (k - 1))) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * ((p : ℝ) ^ (1 / 4 : ℝ) * t ^ 3) * rr2 ^ (k - 1) := by ring
      _ = 8 / rr2 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ k := by
          rw [ht3, h54, hrk]; field_simp

/-- The prime-power tail `T(σ) = ∑_{p,k≥2} Λ_Δ(p^k) p^{−kσ}`. -/
noncomputable def tail (σ : ℝ) : ℂ :=
  ∑' q : Nat.Primes × ℕ, term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q)

lemma tendsto_tail : Tendsto tail (𝓝[>] 1) (𝓝 (tail 1)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := Mb) summable_Mb (fun q => ?_) ?_
  · have hn : ppow2 q ≠ 0 := pow_ne_zero _ q.1.2.ne_zero
    have hc : Continuous fun σ : ℝ => term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q) := by
      simp only [term_of_ne_zero hn]
      refine continuous_const.div ?_ fun σ => ?_
      · exact continuous_ofReal.const_cpow (.inl (by exact_mod_cast hn))
      · rw [Ne, cpow_eq_zero_iff]
        exact fun h => (by exact_mod_cast hn : ((ppow2 q : ℕ) : ℂ) ≠ 0) h.1
    exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ) q
    exact norm_term_vM_ppow2_le hσ.le q

/-- `∑ Λ_Δ(n) n^{−σ} = (prime sum) + (tail)` for `σ > 1`. -/
lemma LSeries_vM_split {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => (vM n : ℂ)) σ = (primeSum σ : ℂ) + tail σ := by
  set f := term (fun n => (vM n : ℂ)) (σ : ℂ)
  have hf : Summable f := LSeriesSummable_vM (by simpa using hσ)
  have hsupp : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    apply hn
    simp only [f, term_def, vM_of_not h]; simp
  have h := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hf hsupp
  have hprod : Summable fun q : Nat.Primes × ℕ => f (ppow2 q) := hf.comp_injective ppow2_injective
  have e2 : ∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 2)) = tail σ := by
    rw [tail, hprod.tsum_prod]; rfl
  have e1 : ∑' p : Nat.Primes, f p = (primeSum σ : ℂ) := by
    rw [primeSum, Complex.ofReal_tsum]
    congr 1; funext p
    have hp := p.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [f, term_of_ne_zero hp.ne_zero, vM_prime hp]
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    push_cast
    rw [Complex.ofReal_cpow hp0.le]
    push_cast; rfl
  rw [LSeries, h, e1, e2]

/-- **Smoothed prime number theorem for `τ` (unconditional).**
`∑_p τ(p) p^{−11/2} log p · p^{−σ}` converges to a finite limit as `σ → 1⁺`
(whereas `∑_p log p · p^{−σ} ∼ 1/(σ−1)`). -/
theorem primeSum_tendsto [RealEdge] : Tendsto primeSum (𝓝[>] 1) (𝓝 ((negLogDeriv 1 - tail 1).re)) := by
  have hL : Tendsto (fun σ : ℝ => negLogDeriv σ) (𝓝[>] 1) (𝓝 (negLogDeriv 1)) := by
    have h := (continuousAt_negLogDeriv (s := 1) (by simp)).tendsto.comp
      (continuous_ofReal.tendsto 1)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun σ : ℝ => (primeSum σ : ℂ)) (𝓝[>] 1) (𝓝 (negLogDeriv 1 - tail 1)) := by
    refine (hL.sub tendsto_tail).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [negLogDeriv_eq_LSeries (by simpa using hσ), LSeries_vM_split hσ]
    ring
  have := (Complex.continuous_re.tendsto _).comp hc
  simpa [Function.comp_def] using this

/-- In particular the smoothed prime sum is bounded as `σ → 1⁺`: it is `o(1/(σ−1))`. -/
theorem primeSum_bounded [RealEdge] : ∃ M : ℝ, ∀ᶠ σ in 𝓝[>] (1 : ℝ), |primeSum σ| ≤ M :=
  ⟨|(negLogDeriv 1 - tail 1).re| + 1,
    (primeSum_tendsto.abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le⟩



end RamanujanTau.EigenformEdge
