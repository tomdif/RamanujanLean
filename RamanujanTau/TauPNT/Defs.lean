/-
# Definitions for the prime number theorem for `τ`

Normalized `L(s) = L(Δ, s + 11/2)` (edge `Re s = 1`), Satake parameters `α_p, β_p`
(`α_p β_p = 1`, `α_p + β_p = λ(p) = τ(p)p^{−11/2}`, `‖β_p‖ ≤ 1 ≤ ‖α_p‖`, `‖α_p‖² ≤ p`),
power sums `A_k(p) = α_p^k + β_p^k` (real), and the two prime-power-supported sequences

* `cc (p^k) = A_k(p) / k`   (coefficients of `log L`),
* `vM (p^k) = A_k(p) log p` (coefficients of `−L'/L`; the von Mangoldt function of `Δ`).
-/
import RamanujanTau.EdgeNonvanishing.Main

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- The normalized L-function `L(s) = L(Δ, s + 11/2)`. -/
noncomputable def Lnorm (s : ℂ) : ℂ := tauL (s + 11 / 2)

lemma Lnorm_differentiable : Differentiable ℂ Lnorm :=
  tauLSeries_entire.comp (differentiable_id.add_const _)

lemma Lnorm_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : Lnorm s ≠ 0 :=
  tauL_ne_zero_of_ge (by simp; linarith)

/-- Satake parameter `α_p`. -/
noncomputable def sa (p : ℕ) : ℂ := Classical.choose (satake (lam p))

/-- Satake parameter `β_p`. -/
noncomputable def sb (p : ℕ) : ℂ := Classical.choose (Classical.choose_spec (satake (lam p)))

lemma sab (p : ℕ) :
    sa p * sb p = 1 ∧ sa p + sb p = lam p ∧ 1 ≤ ‖sa p‖ ∧ ‖sb p‖ ≤ 1 :=
  Classical.choose_spec (Classical.choose_spec (satake (lam p)))

lemma norm_sa_sq_le {p : ℕ} (hp : p.Prime) : ‖sa p‖ ^ 2 ≤ p :=
  alpha_sq_le hp (sab p).1 (sab p).2.1 (sab p).2.2.2

/-- `A_k(p) = α_p^k + β_p^k`, as a real number. -/
noncomputable def AA (p k : ℕ) : ℝ := pseq (lam p) k

lemma AA_eq (p k : ℕ) : (AA p k : ℂ) = sa p ^ k + sb p ^ k :=
  (pow_add_pow_eq_pseq (sab p).2.1 (sab p).1 k).symm

lemma AA_one (p : ℕ) : AA p 1 = lam p := rfl

lemma AA_two (p : ℕ) : AA p 2 = lam p ^ 2 - 2 := by
  simp only [AA, pseq]; ring

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

end RamanujanTau.TauPNT
