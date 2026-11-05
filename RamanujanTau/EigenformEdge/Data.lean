/-
# Abstract normalized GL(2) data, and its Euler products

`EData` packages exactly what the edge non-vanishing proof (`EdgeNonvanishing/`) and the
prime number theorem (`TauPNT/`) use about `Δ`, in the *normalized* coordinates
(edge `Re s = 1`):

* real coefficients `λ(n)`, `λ(1) = 1`, `λ(0) = 0`, multiplicative, with the normalized Hecke
  recursion `λ(p^{e+2}) = λ(p)λ(p^{e+1}) − λ(p^e)`;
* Rankin's theorem with exponent `3/5`: `|∑_{n≤N} λ(n)² − cN| ≤ C N^{3/5}`, `c > 0`;
* an entire function `L` with `L(s) = ∑ λ(n) n^{−s}` on `Re s > 1` and `L(s̄) = conj L(s)`.

For an eigenform `f` of weight `k` these are `λ(n) = a_f(n) n^{−(k−1)/2}`,
`L(s) = L(f, s + (k−1)/2)` (see `Eigenform.lean`).  Everything in this file is proved from the
fields; nothing about modular forms is used.

Contents: the Rankin–Selberg series `R(s) = ∑ λ(n)² n^{−s}` (summability, Abel bound
`R − cζ = O(‖s‖/(σ − 3/5))`, Euler product), absolute convergence of `∑ λ(n) n^{−s}` on
`Re s > 1`, the Euler product `L(s) = ∏_p (1 − λ(p)p^{−s} + p^{−2s})^{−1}` and `L(s) ≠ 0` on
`Re s > 1`, Satake parameters with `‖α_p‖² ≤ p` (no Deligne), and the local factors.
-/
import RamanujanTau.EdgeNonvanishing.Main

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.EigenformEdge

open Complex Finset Filter Asymptotics MeasureTheory LSeries
open scoped ComplexConjugate

/-- Normalized GL(2) data (see the module docstring). -/
class EData where
  /-- normalized real coefficients `λ(n)` -/
  lam : ℕ → ℝ
  lam_zero : lam 0 = 0
  lam_one : lam 1 = 1
  lam_mul : ∀ {m n : ℕ}, m.Coprime n → lam (m * n) = lam m * lam n
  lam_rec : ∀ {p : ℕ}, p.Prime → ∀ e : ℕ,
    lam (p ^ (e + 2)) = lam p * lam (p ^ (e + 1)) - lam (p ^ e)
  /-- Rankin's constant -/
  rsc : ℝ
  rsc_pos : 0 < rsc
  rs_partial : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Icc 1 N, lam n ^ 2 - rsc * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5)
  /-- the entire normalized L-function -/
  L : ℂ → ℂ
  L_diff : Differentiable ℂ L
  L_eq : ∀ s : ℂ, 1 < s.re → L s = LSeries (fun n => (lam n : ℂ)) s
  L_conj : ∀ s : ℂ, L (conj s) = conj (L s)

variable [EData]

open EData

/-! ## The Rankin–Selberg series -/

/-- `b(n) = λ(n)²`. -/
noncomputable def rsb (n : ℕ) : ℝ := lam n ^ 2

noncomputable def rsB (n : ℕ) : ℂ := (rsb n : ℂ)

/-- `R(s) = ∑ λ(n)² n^{−s}`. -/
noncomputable def RS (s : ℂ) : ℂ := LSeries rsB s

lemma rsb_nonneg (n : ℕ) : 0 ≤ rsb n := sq_nonneg _

lemma rsb_zero : rsb 0 = 0 := by simp [rsb, lam_zero]

lemma rs_partial' :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, rsb n - rsc * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC⟩ := rs_partial
  refine ⟨C, ?_, fun N hN => by simpa [rsb] using hC N hN⟩
  have := hC 1 le_rfl
  simp at this
  exact (abs_nonneg _).trans this

lemma rs_partial_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, rsb n ≤ K * N := by
  obtain ⟨C, hC0, hC⟩ := rs_partial'
  refine ⟨|rsc| + C, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := hC N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ ((3 : ℝ) / 5) ≤ N := by
    calc (N : ℝ) ^ ((3 : ℝ) / 5) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have h1 := (abs_le.mp h).2
  have h2 : rsc * N ≤ |rsc| * N := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  nlinarith

lemma rs_le_linear : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, rsb n ≤ K * n := by
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  refine ⟨K, hK0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rsb_zero]
  calc rsb n ≤ ∑ k ∈ Icc 1 n, rsb k :=
        single_le_sum (fun k _ => rsb_nonneg k) (mem_Icc.mpr ⟨hn, le_rfl⟩)
    _ ≤ K * n := hK n

lemma rs_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable rsB s := by
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, rsb k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_of_nonneg (sum_nonneg fun k _ => rsb_nonneg k),
      Real.norm_of_nonneg (by positivity)]
    exact hK n
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO rsb_nonneg zero_le_one hs

/-- **Abel summation bound**: `‖R(s) − c ζ(s)‖ ≤ K‖s‖/(Re s − 3/5)` on `Re s > 1`. -/
theorem rs_sub_zeta_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 < s.re →
      ‖RS s - rsc * riemannZeta s‖ ≤ K * ‖s‖ / (s.re - 3 / 5) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial'
  refine ⟨C, hC0, fun s hs => ?_⟩
  set f : ℕ → ℂ := fun n => rsB n - (rsc : ℂ)
  have hf1 : LSeriesSummable (fun _ : ℕ => (rsc : ℂ)) s := by
    have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
    have := h1.smul (rsc : ℂ)
    convert this using 1
    funext n; simp
  have hfS : LSeriesSummable f s := (rs_summable hs).sub hf1
  have hLf : LSeries f s = RS s - rsc * riemannZeta s := by
    have : f = rsB - (rsc : ℂ) • (1 : ℕ → ℂ) := by funext n; simp [f]
    rw [this, LSeries_sub (rs_summable hs), LSeries_smul, LSeries_one_eq_riemannZeta hs]
    · rfl
    · have := (LSeriesSummable_one_iff.mpr hs).smul (rsc : ℂ); exact this
  have hpart : ∀ N : ℕ, ‖∑ k ∈ Icc 1 N, f k‖ ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have : ∑ k ∈ Icc 1 N, f k = ((∑ n ∈ Icc 1 N, rsb n - rsc * N : ℝ) : ℂ) := by
      simp [f, rsB, sum_sub_distrib, mul_comm]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hC N hN
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 5) := by
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpart n
  have hs35 : (3 : ℝ) / 5 < s.re := by linarith
  rw [← hLf, LSeries_eq_mul_integral f (by norm_num) hs35 hfS hO, norm_mul]
  set a : ℝ := (3 : ℝ) / 5 - s.re - 1
  have ha : a < -1 := by simp only [a]; linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ a) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  have hbound : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), C * t ^ a := by
    refine norm_integral_le_of_norm_le hint ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 1 < t) => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have h1 : ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤ C * t ^ ((3 : ℝ) / 5) :=
      (hpart _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hfl (by norm_num)) hC0)
    have h2 : t ^ a = t ^ ((3 : ℝ) / 5) * t ^ (-(s + 1)).re := by
      rw [← Real.rpow_add ht0]; congr 1; simp [a]; ring
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hval : ∫ t in Set.Ioi (1 : ℝ), C * t ^ a = C / (s.re - 3 / 5) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]
    have : a + 1 = -(s.re - 3 / 5) := by simp only [a]; ring
    rw [this]; field_simp
  rw [hval] at hbound
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (C / (s.re - 3 / 5)) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = C * ‖s‖ / (s.re - 3 / 5) := by ring

lemma rsb_mul_coprime {m n : ℕ} (h : m.Coprime n) : rsb (m * n) = rsb m * rsb n := by
  simp only [rsb, lam_mul h]
  ring

/-- **Euler product** of `R(s)` on `Re s > 1`. -/
theorem rs_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e, term rsB s (p ^ e)) (RS s) := by
  have hf1 : term rsB s 1 = 1 := by
    simp [term_of_ne_zero, rsB, rsb, lam_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → term rsB s (m * n) = term rsB s m * term rsB s n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp
    rw [term_of_ne_zero (Nat.mul_ne_zero hm.ne' hn.ne'), term_of_ne_zero hm.ne',
      term_of_ne_zero hn.ne', rsB, rsb_mul_coprime hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
    simp only [rsB]; push_cast; field_simp
  have hsum : Summable (‖term rsB s ·‖) := summable_norm_iff.mpr (rs_summable hs)
  exact EulerProduct.eulerProduct_hasProd hf1 hmul hsum (term_zero _ _)

/-! ## Absolute convergence and the Euler product of `L` -/

/-- The complex coefficients. -/
noncomputable def lamC (n : ℕ) : ℂ := (lam n : ℂ)

/-- `∑ λ(n) n^{−s}` converges absolutely on `Re s > 1` (`|λ| ≤ (1 + λ²)/2`). -/
theorem lam_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable lamC s := by
  have h1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr hs)
  have h2 : Summable fun n => ‖term rsB s n‖ := summable_norm_iff.mpr (rs_summable hs)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  simp only [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, if_false]
  have hpos : 0 < (n : ℝ) ^ s.re := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  rw [lamC, rsB, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (rsb_nonneg n), Pi.one_apply, norm_one]
  rw [← add_div, div_div, div_le_div_iff₀ hpos (by positivity)]
  have : |lam n| * 2 ≤ 1 + rsb n := by
    simp only [rsb]; nlinarith [sq_abs (lam n), sq_nonneg (|lam n| - 1)]
  nlinarith

lemma summable_abs_lam_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  have h := (lam_summable (s := (σ : ℂ)) (by simpa using hσ)).norm
  refine h.congr fun n => ?_
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [lam_zero]
  · rw [if_neg hn]; simp [lamC]

/-- The normalized local polynomial `P_p(s) = 1 − λ(p)p^{−s} + p^{−2s}`. -/
noncomputable def localPoly (s : ℂ) (p : ℕ) : ℂ :=
  1 - lamC p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2

lemma term_pow' (s : ℂ) (a : ℕ → ℂ) {p : ℕ} (hp : p ≠ 0) (e : ℕ) :
    term a s (p ^ e) = a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_of_ne_zero (pow_ne_zero _ hp), Nat.cast_pow, ← natCast_cpow_natCast_mul,
    mul_comm (e : ℂ), cpow_mul_nat, div_eq_mul_inv, ← inv_pow, ← cpow_neg]

theorem localPoly_mul_tsum {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e, term lamC s (p ^ e)) * localPoly s p = 1 := by
  set x := (p : ℂ) ^ (-s)
  set a : ℕ → ℂ := fun e => lamC (p ^ e)
  have hsum : Summable fun e => a e * x ^ e := by
    have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
    have := (lam_summable hs).comp_injective hinj
    simpa [Function.comp_def, term_pow' s _ hp.ne_zero, a, x] using this
  simp_rw [term_pow' s _ hp.ne_zero]
  set S := ∑' e, a e * x ^ e
  have ha0 : a 0 = 1 := by simp [a, lamC, lam_one]
  have ha1 : a 1 = lamC p := by simp [a]
  have hrec : ∀ e, a (e + 2) = lamC p * a (e + 1) - a e := fun e => by
    simp only [a, lamC]; rw [lam_rec hp e]; push_cast; ring
  have h1 : S = a 0 + ∑' e, a (e + 1) * x ^ (e + 1) := hsum.tsum_eq_zero_add.trans (by simp)
  have hsum1 : Summable fun e => a (e + 1) * x ^ (e + 1) := (summable_nat_add_iff 1).mpr hsum
  have h2 : ∑' e, a (e + 1) * x ^ (e + 1) = a 1 * x + ∑' e, a (e + 2) * x ^ (e + 2) :=
    hsum1.tsum_eq_zero_add.trans (by simp)
  have h3 : ∑' e, a (e + 2) * x ^ (e + 2) =
      lamC p * x * ∑' e, a (e + 1) * x ^ (e + 1) - x ^ 2 * S := by
    simp_rw [hrec]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub]
    · congr 1; funext e; ring
    · exact hsum1.mul_left _
    · exact hsum.mul_left _
  have h1' : S = 1 + ∑' e, a (e + 1) * x ^ (e + 1) := by rw [h1, ha0]
  rw [ha1] at h2
  simp only [localPoly]
  linear_combination (1 - lamC p * x) * h1' + h2 + h3

lemma localPoly_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) : localPoly s p ≠ 0 :=
  right_ne_zero_of_mul_eq_one (localPoly_mul_tsum hs hp)

/-- **Euler product of `L` on `Re s > 1`.** -/
theorem L_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (localPoly s p)⁻¹) (L s) := by
  have hf1 : term lamC s 1 = 1 := by simp [term_of_ne_zero, lamC, lam_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → term lamC s (m * n) = term lamC s m * term lamC s n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp
    rw [term_of_ne_zero (Nat.mul_ne_zero hm.ne' hn.ne'), term_of_ne_zero hm.ne', term_of_ne_zero hn.ne',
      lamC, lam_mul hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
    simp only [lamC]; push_cast; field_simp
  have hsum : Summable (‖term lamC s ·‖) := summable_norm_iff.mpr (lam_summable hs)
  have := EulerProduct.eulerProduct_hasProd hf1 hmul hsum (term_zero _ _)
  rw [L_eq s hs]
  convert this using 1
  funext p
  exact (eq_inv_of_mul_eq_one_left (localPoly_mul_tsum hs p.2)).symm

lemma summable_localPoly_sub_one {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => ‖localPoly s p - 1‖ := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hA : Summable fun p : Nat.Primes => ‖lamC p * (p : ℂ) ^ (-s)‖ := by
    have h := ((lam_summable hs).norm).comp_injective hinj
    refine h.congr fun p => ?_
    have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
    simp only [Function.comp_apply, term_of_ne_zero hp0, cpow_neg, div_eq_mul_inv]
  have hB : Summable fun p : Nat.Primes => ‖((p : ℂ) ^ (-s)) ^ 2‖ := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine (h.comp_injective hinj).congr fun p => ?_
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    simp only [Function.comp_apply, norm_pow]
    rw [norm_natCast_cpow_of_pos p.2.pos, neg_re, ← Real.rpow_natCast,
      ← Real.rpow_mul hp.le]
    congr 1; push_cast; ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hA.add hB)
  have : localPoly s p - 1 = -(lamC p * (p : ℂ) ^ (-s)) + ((p : ℂ) ^ (-s)) ^ 2 := by
    simp only [localPoly]; ring
  rw [this]
  exact (norm_add_le _ _).trans (by rw [norm_neg])

/-- **`L(s) ≠ 0` on `Re s > 1`.** -/
theorem L_ne_zero_of_gt {s : ℂ} (hs : 1 < s.re) : L s ≠ 0 := by
  set f : Nat.Primes → ℂ := fun p => localPoly s p - 1
  have hf : ∀ p, 1 + f p ≠ 0 := fun p => by
    simpa [f] using localPoly_ne_zero hs p.2
  have hQ : ∏' p, (1 + f p) ≠ 0 := tprod_one_add_ne_zero_of_summable hf (summable_localPoly_sub_one hs)
  have hP : HasProd (fun p => 1 + f p) (∏' p, (1 + f p)) :=
    (multipliable_one_add_of_summable (summable_localPoly_sub_one hs)).hasProd
  have hprod := hP.mul (L_eulerProduct hs)
  have h1 : (fun p : Nat.Primes => (1 + f p) * (localPoly s p)⁻¹) = fun _ => 1 := by
    funext p
    simp only [f, add_sub_cancel]
    exact mul_inv_cancel₀ (localPoly_ne_zero hs p.2)
  rw [h1] at hprod
  have h := hprod.unique hasProd_one
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-! ## Satake parameters and local factors -/

/-- `u_k = λ(p^k)`. -/
noncomputable def uu (p k : ℕ) : ℝ := lam (p ^ k)

lemma uu_zero (p : ℕ) : uu p 0 = 1 := by simp [uu, lam_one]

lemma uu_one (p : ℕ) : uu p 1 = lam p := by simp [uu]

lemma uu_rec {p : ℕ} (hp : p.Prime) (k : ℕ) : uu p (k + 2) = lam p * uu p (k + 1) - uu p k :=
  lam_rec hp k

lemma rsb_pow (p k : ℕ) : rsb (p ^ k) = uu p k ^ 2 := rfl

/-- **`‖α‖² ≤ p` without Deligne.** -/
theorem alpha_sq_le {p : ℕ} (hp : p.Prime) {α β : ℂ} (hab : α * β = 1) (hs : α + β = lam p)
    (hβ : ‖β‖ ≤ 1) : ‖α‖ ^ 2 ≤ p := by
  obtain ⟨K, hK0, hK⟩ := rs_le_linear
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have key : ∀ k, (uu p (k + 1) : ℂ) - β * uu p k = α ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      simp only [uu_zero, zero_add, pow_one, uu_one]; push_cast
      rw [← hs]; ring
    | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by ring, uu_rec hp, pow_succ, ← ih]
      push_cast
      rw [← hs]
      linear_combination (uu p k : ℂ) * hab
  have hu : ∀ k, uu p k ^ 2 ≤ K * (p : ℝ) ^ k := by
    intro k
    rw [← rsb_pow p k]
    have := hK (p ^ k); push_cast at this; exact this
  have hbd : ∀ k, (‖α‖ ^ 2 / p) ^ (k + 1) ≤ 4 * K := by
    intro k
    have h1 : ‖α‖ ^ (k + 1) ≤ |uu p (k + 1)| + |uu p k| := by
      rw [← norm_pow, ← key]
      calc ‖(uu p (k + 1) : ℂ) - β * uu p k‖ ≤ ‖(uu p (k + 1) : ℂ)‖ + ‖β * uu p k‖ := norm_sub_le _ _
        _ ≤ |uu p (k + 1)| + |uu p k| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
          nlinarith [abs_nonneg (uu p k)]
    have h2 : (‖α‖ ^ (k + 1)) ^ 2 ≤ 2 * (uu p (k + 1) ^ 2 + uu p k ^ 2) := by
      have := pow_le_pow_left₀ (by positivity) h1 2
      nlinarith [sq_abs (uu p (k + 1)), sq_abs (uu p k), sq_nonneg (|uu p (k + 1)| - |uu p k|)]
    have h3 : (p : ℝ) ^ k ≤ (p : ℝ) ^ (k + 1) := pow_le_pow_right₀ hp1 (by omega)
    have h4 := hu (k + 1)
    have h5 := hu k
    have hpk : 0 < (p : ℝ) ^ (k + 1) := by positivity
    rw [div_pow, div_le_iff₀ hpk, ← pow_mul, mul_comm 2 (k + 1), pow_mul]
    nlinarith
  by_contra hcon
  push Not at hcon
  have hq : 1 < ‖α‖ ^ 2 / p := by rw [lt_div_iff₀ hp0]; linarith
  obtain ⟨n, hn1, hn2⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (4 * K)).and
    (eventually_ge_atTop 1) |>.exists
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  linarith [hbd k]

/-- The local polynomial of `L` factors over the Satake parameters. -/
theorem L_local (s : ℂ) (p : ℕ) {α β : ℂ} (hab : α * β = 1) (hs : α + β = lam p) :
    localPoly s p = (1 - α * (p : ℂ) ^ (-s)) * (1 - β * (p : ℂ) ^ (-s)) := by
  rw [localPoly, lamC, ← hs]
  linear_combination (-((p : ℂ) ^ (-s)) ^ 2) * hab

lemma term_rs_pow (s : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    term rsB s (p ^ e) = ((uu p e ^ 2 : ℝ) : ℂ) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_pow' s _ hp.ne_zero, rsB, rsb_pow]

/-- The `ζ(2s) R(s)` local factor. -/
theorem rs_local {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) {α β : ℂ} (hab : α * β = 1)
    (hsum : α + β = lam p) (hα : ‖α‖ ^ 2 ≤ p) (hβ : ‖β‖ ≤ 1) :
    (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, term rsB s (p ^ e) =
      ((1 - (p : ℂ) ^ (-s)) ^ 2 * (1 - α ^ 2 * (p : ℂ) ^ (-s)) * (1 - β ^ 2 * (p : ℂ) ^ (-s)))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set Y := (p : ℂ) ^ (-s)
  have hY : ‖Y‖ * p < 1 := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
    have : (p : ℝ) ^ (-s.re) * p = (p : ℝ) ^ (1 - s.re) := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]; field_simp
    rw [this]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hY1 : ‖Y‖ < 1 := by nlinarith [norm_nonneg Y]
  have hαY : ‖α ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]; nlinarith [norm_nonneg Y]
  have hβY : ‖β ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]
    have : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
    nlinarith [norm_nonneg Y]
  have ne1 : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := fun z hz h => by
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz; exact lt_irrefl _ hz
  have hY2 : (p : ℂ) ^ (-(2 * s)) = Y ^ 2 := by
    rw [show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul]
  set v : ℕ → ℂ := fun k => ((uu p k ^ 2 : ℝ) : ℂ)
  set g : ℕ → ℂ := fun k => v k * Y ^ k
  have hsumg : Summable g := by
    have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
    have := (rs_summable hs).comp_injective hinj
    simpa [Function.comp_def, term_rs_pow s hp, g, v] using this
  have hT : ∑' e, term rsB s (p ^ e) = ∑' k, g k := by
    congr 1; funext e; exact term_rs_pow s hp e
  set c : ℂ := ((lam p : ℝ) : ℂ) ^ 2 - 1
  have hrec : ∀ k, g (k + 3) = c * Y * g (k + 2) - c * Y ^ 2 * g (k + 1) + Y ^ 3 * g k := by
    intro k
    have e2 := uu_rec hp k
    have e3 := uu_rec hp (k + 1)
    have hv : uu p (k + 3) ^ 2 = (lam p ^ 2 - 1) * uu p (k + 2) ^ 2 - (lam p ^ 2 - 1) * uu p (k + 1) ^ 2
        + uu p k ^ 2 := by
      rw [show k + 1 + 2 = k + 3 by ring] at e3
      rw [e3, e2]; ring
    simp only [g, v, c]
    rw [hv]; push_cast; ring
  set S := ∑' k, g k
  have g0 : g 0 = 1 := by simp [g, v, uu_zero]
  have g1 : g 1 = ((lam p : ℝ) : ℂ) ^ 2 * Y := by
    simp only [g, v, uu_one, pow_one]; push_cast; ring
  have g2 : g 2 = c ^ 2 * Y ^ 2 := by
    simp only [g, v, c]
    have := uu_rec hp 0
    simp only [uu_zero, zero_add, uu_one] at this
    rw [this]
    push_cast; ring
  have hs1 : Summable fun k => g (k + 1) := (summable_nat_add_iff 1).mpr hsumg
  have hs2 : Summable fun k => g (k + 2) := (summable_nat_add_iff 2).mpr hsumg
  have e1 : S = g 0 + ∑' k, g (k + 1) := hsumg.tsum_eq_zero_add
  have e2 : ∑' k, g (k + 1) = g 1 + ∑' k, g (k + 2) := hs1.tsum_eq_zero_add
  have e3 : ∑' k, g (k + 2) = g 2 + ∑' k, g (k + 3) := hs2.tsum_eq_zero_add
  have e4 : ∑' k, g (k + 3) = c * Y * ∑' k, g (k + 2) - c * Y ^ 2 * ∑' k, g (k + 1) + Y ^ 3 * S := by
    simp_rw [hrec]
    rw [Summable.tsum_add, Summable.tsum_sub, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    · exact hs2.mul_left _
    · exact hs1.mul_left _
    · exact (hs2.mul_left _).sub (hs1.mul_left _)
    · exact hsumg.mul_left _
  have hcub : S * (1 - c * Y + c * Y ^ 2 - Y ^ 3) = 1 + Y := by
    rw [g0] at e1; rw [g1] at e2; rw [g2] at e3
    have hl : ((lam p : ℝ) : ℂ) ^ 2 = c + 1 := by simp only [c]; ring
    linear_combination (1 - c * Y + c * Y ^ 2) * e1 + (1 - c * Y) * e2 + e3 + e4 + (Y - c * Y ^ 2) * hl
  have hfac : 1 - c * Y + c * Y ^ 2 - Y ^ 3 = (1 - Y) * (1 - α ^ 2 * Y) * (1 - β ^ 2 * Y) := by
    simp only [c]
    rw [← hsum]
    linear_combination (-2 * Y - (α * β - 1) * Y ^ 2 + (α * β + 1) * Y ^ 3) * hab
  have hA := ne1 _ hY1
  have hB := ne1 _ hαY
  have hC := ne1 _ hβY
  have hD : 1 + Y ≠ 0 := by
    have := ne1 (-Y) (by rwa [norm_neg]); rwa [sub_neg_eq_add] at this
  rw [hT, hY2]
  rw [hfac] at hcub
  have hS : S = (1 + Y) / ((1 - Y) * (1 - α ^ 2 * Y) * (1 - β ^ 2 * Y)) := by
    rw [eq_div_iff (by simp [hA, hB, hC])]; exact hcub
  rw [hS]
  have h1Y : 1 - Y ^ 2 = (1 - Y) * (1 + Y) := by ring
  rw [h1Y]
  field_simp

end RamanujanTau.EigenformEdge
