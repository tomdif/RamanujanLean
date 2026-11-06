/-
# The Dirichlet coefficients `α(n)` of `L(Δ,s)^{−1/2}`

* `alpha n = ∏_{p^k ∥ n} alphaLoc (λ(p)) k` (multiplicative; `λ(p) = τ(p)p^{−11/2}`);
* `muD n = ∏_{p^k ∥ n} [1, −λ(p), 1, 0, …]_k`, the coefficients of `L(Δ,s)^{−1}`;
* `lamN n = τ(n) n^{−11/2}`, the coefficients of `L(Δ,s)` in the analytic normalization.

Headlines:
* `alpha_mul_alpha : alpha * alpha = muD` and `lamN_mul_muD : lamN * muD = 1`, hence
  `lamN_mul_alpha_mul_alpha : lamN * alpha * alpha = 1` (Dirichlet convolution; `1 = δ`):
  `α` *is* the coefficient sequence of `L^{−1/2}`;
* `abs_alpha_le_one [DeligneBound] : |α(n)| ≤ 1` for all `n`;
* `alpha_sq_le_self : α(n)² ≤ n` **unconditionally** (Satake `‖α_p‖² ≤ p` from Rankin's linear
  bound, `EdgeNonvanishing.alpha_sq_le`), so `|α(n)| ≤ n^{1/2}`.
-/
import RamanujanTau.SelbergCoeffs.Local
import RamanujanTau.EdgeNonvanishing.PrimeLocal
import RamanujanTau.Deligne
import RamanujanTau.HeckeQExp

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs

open Finset ArithmeticFunction
open RamanujanTau.EdgeNonvanishing (lam rr uu uu_rec rr_sq satake alpha_sq_le uu_zero)

noncomputable section

/-! ## Multiplicative functions from local data -/

/-- The multiplicative function with `f(p^k) = h p k`. -/
def ofLocal (h : ℕ → ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod h, if_pos rfl⟩

lemma ofLocal_apply (h : ℕ → ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ofLocal h n = n.factorization.prod h := if_neg hn

lemma ofLocal_ppow {h : ℕ → ℕ → ℝ} (h0 : ∀ p, h p 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ofLocal h (p ^ k) = h p k := by
  rw [ofLocal_apply h (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (h0 p)]

lemma isMultiplicative_ofLocal {h : ℕ → ℕ → ℝ} : (ofLocal h).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [ofLocal_apply h one_ne_zero]; simp, fun {m n} hm hn hmn => ?_⟩
  rw [ofLocal_apply h (mul_ne_zero hm hn), ofLocal_apply h hm, ofLocal_apply h hn,
    Nat.factorization_mul_of_coprime hmn]
  apply Finsupp.prod_add_index_of_disjoint
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hmn.disjoint_primeFactors

/-- Dirichlet convolution at a prime power. -/
lemma mul_ppow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ q ∈ antidiagonal k, f (p ^ q.1) * g (p ^ q.2) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p ^ i) * g (p ^ j))]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-! ## The coefficient sequences -/

/-- **The coefficients `α(n)` of `L(Δ,s)^{−1/2}`** (normalized: `L = Σ λ(n) n^{−s}`). -/
def alpha : ArithmeticFunction ℝ := ofLocal fun p k => alphaLoc (lam p) k

/-- The coefficients of `L(Δ,s)^{−1} = ∏_p (1 − λ(p)p^{−s} + p^{−2s})`. -/
def muD : ArithmeticFunction ℝ := ofLocal fun p k => Gc (lam p) k

lemma alpha_ppow {p : ℕ} (hp : p.Prime) (k : ℕ) : alpha (p ^ k) = alphaLoc (lam p) k :=
  ofLocal_ppow (fun _ => alphaLoc_zero _) hp k

lemma muD_ppow {p : ℕ} (hp : p.Prime) (k : ℕ) : muD (p ^ k) = Gc (lam p) k :=
  ofLocal_ppow (fun _ => by simp [Gc]) hp k

lemma alpha_mult : alpha.IsMultiplicative := isMultiplicative_ofLocal
lemma muD_mult : muD.IsMultiplicative := isMultiplicative_ofLocal

lemma alpha_one : alpha 1 = 1 := alpha_mult.map_one

lemma alpha_prime {p : ℕ} (hp : p.Prime) : alpha p = -lam p / 2 := by
  have := alpha_ppow hp 1
  rw [pow_one] at this; rw [this, alphaLoc_one]

/-- **`α ∗ α = μ_Δ`**: the square of the Dirichlet series `Σ α(n)n^{−s}` is `L(Δ,s)^{−1}`
(coefficientwise). -/
theorem alpha_mul_alpha : alpha * alpha = muD := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (alpha_mult.mul alpha_mult) _ muD_mult]
  intro p k hp
  rw [mul_ppow _ _ hp, muD_ppow hp, ← alphaLoc_sq_sum]
  exact sum_congr rfl fun q _ => by rw [alpha_ppow hp, alpha_ppow hp]

/-- `λ(n) = τ(n) n^{−11/2}`. -/
def lamN : ArithmeticFunction ℝ :=
  ⟨fun n => (tau n : ℝ) * (n : ℝ) ^ (-(11 / 2 : ℝ)), by simp [tau_zero]⟩

lemma lamN_apply (n : ℕ) : lamN n = (tau n : ℝ) * (n : ℝ) ^ (-(11 / 2 : ℝ)) := rfl

lemma lamN_mult : lamN.IsMultiplicative := by
  refine ⟨by simp [lamN_apply, tau_one], fun {m n} hmn => ?_⟩
  simp only [lamN_apply]
  rw [tau_mul_coprime hmn, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  push_cast; ring

lemma lamN_ppow {p : ℕ} (_hp : p.Prime) (k : ℕ) : lamN (p ^ k) = uu p k := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [lamN_apply, uu, rr, Nat.cast_pow, ← Real.rpow_natCast ((p : ℝ) ^ (-(11 / 2 : ℝ))),
    ← Real.rpow_mul hp0, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm (k : ℝ)]

lemma lamN_prime {p : ℕ} (hp : p.Prime) : lamN p = lam p := by
  have := lamN_ppow hp 1; rw [pow_one] at this; rw [this]; rfl

/-- **`λ ∗ μ_Δ = δ`** (Hecke relations): `μ_Δ` is the Dirichlet inverse of `λ`. -/
theorem lamN_mul_muD : lamN * muD = 1 := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (lamN_mult.mul muD_mult) _
    isMultiplicative_one]
  intro p k hp
  rw [mul_ppow _ _ hp, one_apply]
  simp_rw [lamN_ppow hp, muD_ppow hp]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => uu p i * Gc (lam p) j)]
  rcases k with _ | _ | n
  · simp [uu_zero, Gc]
  · simp [Finset.sum_range_succ, uu_zero, Gc]
    rw [if_neg hp.one_lt.ne']
    simp [lam]
  · rw [if_neg (by
      intro h
      have := Nat.pow_right_injective hp.two_le (h.trans (pow_zero p).symm)
      omega)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hz : ∑ x ∈ range n, uu p x * Gc (lam p) (n + 1 + 1 - x) = 0 := by
      refine sum_eq_zero fun x hx => ?_
      rw [mem_range] at hx
      have : Gc (lam p) (n + 1 + 1 - x) = 0 := by
        simp only [Gc]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, mul_zero]
    rw [hz, show n + 1 + 1 - n = 2 by omega, show n + 1 + 1 - (n + 1) = 1 by omega,
      show n + 1 + 1 - (n + 1 + 1) = 0 by omega]
    simp only [Gc]; norm_num
    have := uu_rec hp n
    linarith

/-- **`λ ∗ α ∗ α = δ`**: `Σ α(n) n^{−s} = L(Δ,s)^{−1/2}` (formally, as Dirichlet series). -/
theorem lamN_mul_alpha_mul_alpha : lamN * alpha * alpha = 1 := by
  rw [mul_assoc, alpha_mul_alpha, lamN_mul_muD]

/-! ## Coefficient bounds -/

/-- Deligne in the normalized form `λ(p)² ≤ 4`. -/
lemma lam_sq_le_four [DeligneBound] {p : ℕ} (hp : p.Prime) : lam p ^ 2 ≤ 4 := by
  have hD : ((tau p : ℤ) : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 11 := by
    exact_mod_cast DeligneBound.bound p hp
  have hr := rr_sq hp
  have : lam p ^ 2 = ((tau p : ℤ) : ℝ) ^ 2 * rr p ^ 2 := by
    simp only [lam, uu, pow_one]; ring
  rw [this]
  have hr2 : 0 ≤ rr p ^ 2 := sq_nonneg _
  nlinarith

lemma abs_finsupp_prod (f : ℕ →₀ ℕ) (h : ℕ → ℕ → ℝ) : |f.prod h| = f.prod fun p k => |h p k| := by
  simp only [Finsupp.prod]; exact Finset.abs_prod _ _

/-- **Under Deligne, `|α(n)| ≤ 1` for every `n`.** -/
theorem abs_alpha_le_one [DeligneBound] (n : ℕ) : |alpha n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [alpha, ofLocal_apply _ hn, abs_finsupp_prod]
  refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p hp => ?_
  rw [Nat.support_factorization] at hp
  exact abs_alphaLoc_le_one (lam_sq_le_four (Nat.prime_of_mem_primeFactors hp)) _

/-- Unconditional local bound: `α(p^k)² ≤ p^k` (Satake `‖α_p‖² ≤ p`, no Deligne). -/
lemma alphaLoc_sq_le {p : ℕ} (hp : p.Prime) (k : ℕ) : alphaLoc (lam p) k ^ 2 ≤ (p : ℝ) ^ k := by
  obtain ⟨a, b, hab, hs, ha, hb⟩ := satake (lam p)
  have hA := alpha_sq_le hp hab hs hb
  have h := abs_alphaLoc_le_pow hs hab le_rfl (hb.trans ha) k
  have h2 : alphaLoc (lam p) k ^ 2 ≤ (‖a‖ ^ k) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc alphaLoc (lam p) k ^ 2 ≤ (‖a‖ ^ k) ^ 2 := h2
    _ = (‖a‖ ^ 2) ^ k := by ring
    _ ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hA k

/-- **Unconditionally, `α(n)² ≤ n`.** -/
theorem alpha_sq_le_self (n : ℕ) : alpha n ^ 2 ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [alpha, ofLocal_apply _ hn]
  have hself : (n : ℝ) = n.factorization.prod fun p k => (p : ℝ) ^ k := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    simp only [Finsupp.prod]; push_cast; rfl
  rw [hself]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun p hp => ?_
  rw [Nat.support_factorization] at hp
  exact alphaLoc_sq_le (Nat.prime_of_mem_primeFactors hp) _

theorem abs_alpha_le_sqrt (n : ℕ) : |alpha n| ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (alpha_sq_le_self n)

end

end RamanujanTau.SelbergCoeffs
