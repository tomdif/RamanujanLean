/-
# The local LDLᵀ for the actual `ρ_p` of `HafnerBridge/QF.lean` (unconditional)

`μ_p(k) = λ(p^{k−1})` (`μ_p(0) = 0`) satisfies the hypotheses of `chol_loc`, and
`rr (1/p) μ_p k = ρ_p(k)` (`rhoP`).  Hence (**`chol_rhoP`**), for every prime `p`, `a, n ≥ 0`,

  `p^{−(a+n)} ρ_p(n) = p^{−(2a+n)} ρ_p(a) ρ_p(a+n) + Σ_{i<a} W_p(a−i) p^{−(n+2i)} λ(p^i) λ(p^{i+n})`.
-/
import RamanujanTau.QFProof.Local
import RamanujanTau.QFProof.Chol

set_option autoImplicit false

namespace RamanujanTau.QFProof

open Finset RamanujanTau.HafnerBridge

/-- `μ_p(k) = λ(p^{k−1})`, `μ_p(0) = 0`. -/
noncomputable def muP (p k : ℕ) : ℝ := if k = 0 then 0 else lam (p ^ (k - 1))

lemma muP_succ (p k : ℕ) : muP p (k + 1) = lam (p ^ k) := by simp [muP]

lemma muP_rec {p : ℕ} (hp : p.Prime) (k : ℕ) :
    muP p (k + 2) = lam p * muP p (k + 1) - muP p k := by
  rcases k with _ | k
  · simp only [muP, show (0 + 2 : ℕ) = 1 + 1 by rfl]
    simp [lam_one]
  · rw [show k + 1 + 2 = (k + 2) + 1 by ring, muP_succ, show k + 1 + 1 = k + 2 by ring, muP_succ,
      muP_succ, lamp_rec hp k, pow_one]

lemma rhoP_zero {p : ℕ} (hp : p.Prime) : rhoP p 0 = 1 := by
  have hD := one_le_Dp hp
  unfold rhoP Np Dp
  simp only [Nat.add_zero, ← sq]
  exact div_self (by unfold Dp at hD; linarith)

lemma rr_muP {p : ℕ} (hp : p.Prime) (k : ℕ) : rr ((p : ℝ)⁻¹) (muP p) k = rhoP p k := by
  rcases k with _ | k
  · rw [rr_zero, rhoP_zero hp]
  rcases k with _ | k
  · rw [rhoP_one hp, rr_succ, muP_succ]
    simp [muP, pow_one]
  · rw [rhoP_add_two hp, rr_succ, show k + 1 + 2 = (k + 2) + 1 by ring, muP_succ,
      show k + 1 = k + 1 by rfl, muP_succ]

/-- **The local LDLᵀ identity for the actual `ρ_p`.** -/
theorem chol_rhoP {p : ℕ} (hp : p.Prime) (n a : ℕ) :
    ((p : ℝ)⁻¹) ^ (a + n) * rhoP p n =
      ((p : ℝ)⁻¹) ^ (2 * a + n) * rhoP p a * rhoP p (a + n) +
      ∑ i ∈ range a, Wc (lam p) ((p : ℝ)⁻¹) (a - i) * ((p : ℝ)⁻¹) ^ (n + 2 * i) *
        lam (p ^ i) * lam (p ^ (i + n)) := by
  have h := chol_loc (lam p) ((p : ℝ)⁻¹) (muP p) (by simp [muP]) (by simp [muP, lam_one])
    (muP_rec hp) (one_add_X_pos p).ne' n a
  rw [rr_muP hp, rr_muP hp, rr_muP hp] at h
  rw [h]
  congr 1

end RamanujanTau.QFProof
