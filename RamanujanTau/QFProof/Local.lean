/-
# Closed form of the local Rankin–Selberg twist `ρ_p(a)` (unconditional)

With `X = 1/p`, `λ_j = λ(p^j)` (`HafnerBridge.lam`):

* `lamp_rec` (Hecke): `λ_{k+2} = λ_1 λ_{k+1} − λ_k`;
* `lamp_mul`: `λ_{a+j+2} = λ_{a+1}λ_{j+1} − λ_a λ_j`;
* `Np_succ`: `N_p(a+1) = λ_{a+1} D_p − λ_a X N_p(1)`;
* **`rhoP_one`**: `ρ_p(1) = λ(p)/(1+X)`; **`rhoP_add_two`**: `ρ_p(a+2) = (λ_{a+2} − Xλ_a)/(1+X)`.
-/
import RamanujanTau.HafnerBridge.Local
import RamanujanTau.EdgeNonvanishing.PrimeLocal

set_option autoImplicit false

namespace RamanujanTau.QFProof

open RamanujanTau.HafnerBridge

lemma lam_pp {p : ℕ} (hp : p.Prime) (j : ℕ) : lam (p ^ j) = RamanujanTau.EdgeNonvanishing.uu p j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [lam, RamanujanTau.SubconvexityCond.lam, RamanujanTau.EdgeNonvanishing.uu,
    RamanujanTau.EdgeNonvanishing.rr]
  push_cast
  congr 1
  rw [← Real.rpow_natCast (p : ℝ) j, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast _ j,
    ← Real.rpow_mul hp0.le]
  ring_nf

/-- Hecke: `λ_{k+2} = λ_1 λ_{k+1} − λ_k`. -/
lemma lamp_rec {p : ℕ} (hp : p.Prime) (k : ℕ) :
    lam (p ^ (k + 2)) = lam (p ^ 1) * lam (p ^ (k + 1)) - lam (p ^ k) := by
  rw [lam_pp hp, lam_pp hp, lam_pp hp, lam_pp hp, RamanujanTau.EdgeNonvanishing.uu_rec hp k]
  rfl

lemma lamp_zero (p : ℕ) : lam (p ^ 0) = 1 := by rw [pow_zero]; exact lam_one

/-- `λ_{a+j+2} = λ_{a+1}λ_{j+1} − λ_a λ_j`. -/
lemma lamp_mul {p : ℕ} (hp : p.Prime) (a j : ℕ) :
    lam (p ^ (a + j + 2)) = lam (p ^ (a + 1)) * lam (p ^ (j + 1)) - lam (p ^ a) * lam (p ^ j) := by
  induction j using Nat.twoStepInduction with
  | zero => rw [lamp_rec hp, lamp_zero]; ring_nf
  | one =>
    rw [show a + 1 + 2 = (a + 1) + 2 by ring, lamp_rec hp (a + 1), show a + 1 + 1 = a + 2 by ring,
      lamp_rec hp a, show (1 + 1 : ℕ) = 0 + 2 by rfl, lamp_rec hp 0, lamp_zero]
    ring_nf
  | more j h0 h1 =>
    rw [show a + (j + 2) + 2 = (a + j + 2) + 2 by ring, lamp_rec hp,
      show a + j + 2 + 1 = a + (j + 1) + 2 by ring, h1, h0,
      show j + 2 + 1 = (j + 1) + 2 by ring, lamp_rec hp (j + 1), lamp_rec hp j]
    ring

lemma rpow_neg_nat {p : ℕ} (j : ℕ) : (p : ℝ) ^ (-(j : ℝ)) = ((p : ℝ)⁻¹) ^ j := by
  rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast, inv_pow]

/-- `N_p(a+1) = λ_{a+1} D_p − λ_a X N_p(1)`. -/
lemma Np_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Np p (a + 1) = lam (p ^ (a + 1)) * Dp p - lam (p ^ a) * (p : ℝ)⁻¹ * Np p 1 := by
  set X : ℝ := (p : ℝ)⁻¹ with hX
  have sN := summable_Np hp (a + 1)
  have sD := summable_Dp hp
  have sN1 := summable_Np hp 1
  unfold Np Dp
  rw [sN.tsum_eq_zero_add, sD.tsum_eq_zero_add]
  have sD' := (summable_nat_add_iff 1).2 sD
  have sN1' : Summable fun j : ℕ => lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
    refine (sN1.mul_left X).congr fun j => ?_
    rw [rpow_neg_nat, rpow_neg_nat, pow_succ]; ring
  have e : ∀ j : ℕ, lam (p ^ (j + 1 + (a + 1))) * lam (p ^ (j + 1)) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      lam (p ^ (a + 1)) * (lam (p ^ (j + 1)) ^ 2 * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ))) -
      lam (p ^ a) * (lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ))) := by
    intro j
    rw [show j + 1 + (a + 1) = a + j + 2 by ring, lamp_mul hp]; ring
  have hsplit : ∑' j : ℕ, lam (p ^ (j + 1 + (a + 1))) * lam (p ^ (j + 1)) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      lam (p ^ (a + 1)) * ∑' j : ℕ, lam (p ^ (j + 1)) ^ 2 * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) -
      lam (p ^ a) * ∑' j : ℕ, lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
    rw [tsum_congr e, Summable.tsum_sub (sD'.mul_left _) (sN1'.mul_left _), tsum_mul_left, tsum_mul_left]
  have hshift : ∑' j : ℕ, lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
      X * ∑' j : ℕ, lam (p ^ (j + 1)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [rpow_neg_nat, rpow_neg_nat, pow_succ]; ring
  rw [hsplit, hshift]
  simp only [Nat.zero_add, Nat.cast_zero, neg_zero, Real.rpow_zero, pow_zero, lam_one]
  ring

lemma one_add_X_pos (p : ℕ) : 0 < 1 + (p : ℝ)⁻¹ := by positivity

lemma Np_one_eq {p : ℕ} (hp : p.Prime) : Np p 1 * (1 + (p : ℝ)⁻¹) = lam p * Dp p := by
  have h := Np_succ hp 0
  rw [lamp_zero, zero_add, pow_one] at h
  linarith

/-- **`ρ_p(1) = λ(p)/(1 + 1/p)`.** -/
theorem rhoP_one {p : ℕ} (hp : p.Prime) : rhoP p 1 = lam p / (1 + (p : ℝ)⁻¹) := by
  have hD := one_le_Dp hp
  have hX := one_add_X_pos p
  unfold rhoP
  rw [div_eq_div_iff (by linarith) hX.ne', Np_one_eq hp]

/-- **`ρ_p(a+2) = (λ_{a+2} − λ_a/p)/(1 + 1/p)`.** -/
theorem rhoP_add_two {p : ℕ} (hp : p.Prime) (a : ℕ) :
    rhoP p (a + 2) = (lam (p ^ (a + 2)) - (p : ℝ)⁻¹ * lam (p ^ a)) / (1 + (p : ℝ)⁻¹) := by
  have hD := one_le_Dp hp
  have hX := one_add_X_pos p
  have h := Np_succ hp (a + 1)
  have h1 := Np_one_eq hp
  have hr := lamp_rec hp a
  rw [pow_one] at hr
  unfold rhoP
  rw [div_eq_div_iff (by linarith) hX.ne', h]
  have hN1 : Np p 1 = lam p * Dp p / (1 + (p : ℝ)⁻¹) := by
    rw [eq_div_iff hX.ne', h1]
  rw [hN1]
  field_simp
  rw [hr]
  ring

end RamanujanTau.QFProof
