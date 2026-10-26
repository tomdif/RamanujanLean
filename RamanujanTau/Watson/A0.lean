/-
# Watson's (A₀): the two series for χ₀ agree

  `Σ_n qⁿ/(q^{n+1};q)_n = 1 + Σ_m q^{2m+1}/(q^{m+1};q)_{m+1}`.

Watson sums the double series `Σ_{n,k} q^{n+1+(n+2)k} (q;q)_{n+k}/((q;q)_n (q;q)_k)` in two ways with
the finite q-binomial (E3).
-/
import RamanujanTau.Watson.Binom

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-- `χ₀ = Σ_n qⁿ/(q^{n+1};q)_n`. -/
noncomputable def chiA : PowerSeries ℤ := osum fun n => X ^ n * Ring.inverse (FP 1 (n + 1) 1 n)

/-- the second series `1 + Σ_m q^{2m+1}/(q^{m+1};q)_{m+1}`. -/
noncomputable def chiB : PowerSeries ℤ := 1 + osum fun m => X ^ (2 * m + 1) * Ring.inverse (FP 1 (m + 1) 1 (m + 1))

lemma LF_Xpow_mul {g : ℕ → PowerSeries ℤ} {e : ℕ → ℕ} (he : ∀ n, n ≤ e n) :
    LF fun n => X ^ (e n) * g n :=
  LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by have := he n; omega)]

/-- symmetric form of the q-binomial coefficient: `(q^{n+1};q)_k/(q;q)_k = (q^{k+1};q)_n/(q;q)_n`. -/
lemma qbinom_symm (n k : ℕ) : FP 1 (n + 1) 1 k * QI 1 k = FP 1 (k + 1) 1 n * QI 1 n := by
  have un := isUnit_FP 1 (le_refl 1) 1 n
  have uk := isUnit_FP 1 (le_refl 1) 1 k
  have e1 : QF 1 n * FP 1 (n + 1) 1 k = QF 1 (n + k) := by
    rw [QF, QF, FP_add]; ring_nf
  have e2 : QF 1 k * FP 1 (k + 1) 1 n = QF 1 (n + k) := by
    rw [QF, QF, add_comm n k, FP_add]; ring_nf
  apply (un.mul uk).mul_left_cancel
  calc QF 1 n * QF 1 k * (FP 1 (n + 1) 1 k * QI 1 k)
      = (QF 1 n * FP 1 (n + 1) 1 k) * (QF 1 k * QI 1 k) := by ring
    _ = QF 1 (n + k) := by rw [e1, QF_mul_QI 1 k le_rfl, mul_one]
    _ = (QF 1 k * FP 1 (k + 1) 1 n) * (QF 1 n * QI 1 n) := by rw [e2, QF_mul_QI 1 n le_rfl, mul_one]
    _ = QF 1 n * QF 1 k * (FP 1 (k + 1) 1 n * QI 1 n) := by ring

lemma inv_FP_eq_osum (a M : ℕ) (ha : 1 ≤ a) :
    Ring.inverse (FP 1 a 1 M) = osum fun k => X ^ (a * k) * (FP 1 M 1 k * QI 1 k) := by
  rw [← KB_eq 1 ha le_rfl M, KB]
  refine osum_ext fun k => ?_
  simp [kB]; ring

/-- **(A₀)**. -/
theorem chiA_eq_chiB : chiA = chiB := by
  -- the double family, indexed `(n, k)`, of exponent `n + 1 + (n+2)k = 2k + 1 + (k+1)n`
  set f : ℕ × ℕ → PowerSeries ℤ := fun p =>
    X ^ (p.1 + 1 + (p.1 + 2) * p.2) * (FP 1 (p.1 + 1) 1 p.2 * QI 1 p.2) with hf_def
  have hf : LF f := LF.of_order (fun p => p.1 + p.2)
    (fun p k hk => by
      simp only [hf_def]
      rw [coeff_X_pow_mul', if_neg (by nlinarith)])
    (fun k => ((Set.finite_Iic k).prod (Set.finite_Iic k)).subset fun p hp => by
      simp only [Set.mem_setOf_eq] at hp
      exact ⟨by simp; omega, by simp; omega⟩)
  -- LHS: peel the `n = 0` term of χ₀ and expand each `1/(q^{n+2};q)_{n+1}` with (E3)
  have hL : chiA = 1 + osum fun n => osum fun k => f (n, k) := by
    rw [chiA, osum_succ (LF_Xpow_mul (fun n => le_refl n))]
    simp only [pow_zero, one_mul, FP_zero, Ring.inverse_one]
    congr 1
    refine osum_ext fun n => ?_
    rw [inv_FP_eq_osum (n + 1 + 1) (n + 1) (by omega),
      mul_osum (LF_Xpow_mul (fun k => by nlinarith)) ]
    refine osum_ext fun k => ?_
    simp only [hf_def]
    rw [← mul_assoc, ← pow_add]
  -- RHS: expand each `1/(q^{m+1};q)_{m+1}` with (E3)
  have hR : chiB = 1 + osum fun k => osum fun n => f (n, k) := by
    rw [chiB]
    congr 1
    refine osum_ext fun k => ?_
    rw [inv_FP_eq_osum (k + 1) (k + 1) (by omega), mul_osum (LF_Xpow_mul (fun n => by nlinarith))]
    refine osum_ext fun n => ?_
    simp only [hf_def]
    rw [qbinom_symm n k, ← mul_assoc, ← pow_add]
    ring_nf
  rw [hL, hR, osum_prod_swap hf]

end Watson
