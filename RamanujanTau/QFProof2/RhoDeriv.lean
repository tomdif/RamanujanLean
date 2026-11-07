/-
# Closed form of `ρ'_p(a)` (unconditional)

With `X = 1/p`:

* `Np'_succ`: `N'_p(a+1) = λ_{a+1} D'_p − λ_a X (N'_p(1) − log p · N_p(1))`;
* **`rhoP'_zero`**: `ρ'_p(0) = 0`;
* **`rhoP'_succ`**: `ρ'_p(a+1) = X log p · λ(p) λ(p^a) / (1+X)²`
  (equivalently `X log p (λ_{a+1} + λ_{a−1})/(1+X)²`).
-/
import RamanujanTau.QFProof.Local

set_option autoImplicit false

namespace RamanujanTau.QFProof2

open RamanujanTau.HafnerBridge RamanujanTau.QFProof

lemma Np'_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Np' p (a + 1) = lam (p ^ (a + 1)) * Dp' p -
      lam (p ^ a) * (p : ℝ)⁻¹ * (Np' p 1 - Real.log p * Np p 1) := by
  set X : ℝ := (p : ℝ)⁻¹ with hX
  have sT := summable_Np' hp (a + 1)
  have sD := summable_Dp' hp
  have sT1 := summable_Np' hp 1
  have sN1 := summable_Np hp 1
  unfold Np' Dp' Np
  rw [sT.tsum_eq_zero_add, sD.tsum_eq_zero_add]
  have sD' := (summable_nat_add_iff 1).2 sD
  have sM : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) * lam (p ^ j) *
      (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
    refine ((sT1.add (sN1.mul_left (Real.log p))).mul_left X).congr fun j => ?_
    rw [rpow_neg_nat, rpow_neg_nat, pow_succ]; push_cast; ring
  have e : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1 + (a + 1))) * lam (p ^ (j + 1)) *
      (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      lam (p ^ (a + 1)) * (((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) ^ 2 * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ))) -
      lam (p ^ a) * (((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) * lam (p ^ j) *
        (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ))) := by
    intro j
    rw [show j + 1 + (a + 1) = a + j + 2 by ring, lamp_mul hp]; ring
  have hsplit : ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1 + (a + 1))) * lam (p ^ (j + 1)) *
      (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      lam (p ^ (a + 1)) * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) ^ 2 *
        (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) -
      lam (p ^ a) * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) * lam (p ^ j) *
        (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
    rw [tsum_congr e, Summable.tsum_sub (sD'.mul_left _) (sM.mul_left _), tsum_mul_left, tsum_mul_left]
  have hshift : ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * Real.log p * lam (p ^ (j + 1)) * lam (p ^ j) *
      (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      X * (∑' j : ℕ, (j : ℝ) * Real.log p * lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) +
        Real.log p * ∑' j : ℕ, lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ))) := by
    rw [← tsum_mul_left, ← Summable.tsum_add sT1 (sN1.mul_left (Real.log p)), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [rpow_neg_nat, rpow_neg_nat, pow_succ]; push_cast; ring
  rw [hsplit, hshift]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  ring

lemma rhoP'_zero {p : ℕ} (_hp : p.Prime) : rhoP' p 0 = 0 := by
  unfold rhoP' Np' Np Dp' Dp
  simp only [Nat.add_zero]
  have : ∀ j : ℕ, (j : ℝ) * Real.log p * lam (p ^ j) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) =
      (j : ℝ) * Real.log p * lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ)) := fun j => by ring
  simp only [this, ← sq]
  ring

/-- **`ρ'_p(a+1) = X log p · λ(p) λ(p^a)/(1+X)²`.** -/
theorem rhoP'_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    rhoP' p (a + 1) = (p : ℝ)⁻¹ * Real.log p * lam p * lam (p ^ a) / (1 + (p : ℝ)⁻¹) ^ 2 := by
  have hD := one_le_Dp hp
  have hX := one_add_X_pos p
  have h1 := Np_succ hp a
  have h2 := Np_one_eq hp
  have h3 := Np'_succ hp a
  have h4 := Np'_succ hp 0
  rw [lamp_zero, zero_add, pow_one] at h4
  have hN1 : Np p 1 = lam p * Dp p / (1 + (p : ℝ)⁻¹) := by rw [eq_div_iff hX.ne', h2]
  have hN1' : Np' p 1 = (lam p * Dp' p + (p : ℝ)⁻¹ * Real.log p * Np p 1) / (1 + (p : ℝ)⁻¹) := by
    rw [eq_div_iff hX.ne']; linarith
  unfold rhoP'
  rw [h1, h3, hN1', hN1]
  have hD0 : Dp p ≠ 0 := by linarith
  field_simp
  ring

end RamanujanTau.QFProof2
