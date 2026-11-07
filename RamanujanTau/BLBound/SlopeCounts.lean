import Mathlib.Tactic

/-!
# Dimension identities behind the slope chain

The floor-function identities D1, D2 and D4 of `docs/BL_SHARPNESS_PROOF.md` §4.10, for
`dimM`, the dimension of level-one modular forms of even weight. `n` stands for `ℓ - 1`, with `ℓ ≥ 5`
prime, so `n % 12` is one of `0, 4, 6, 10`.

* `dimM_step`: the identity that makes the Katz blocks independent of the step along a chain.
* `gr_succ_eq`: `dim gr^{t+2}(a+2) = dim gr^{t+1}(a)` (D1).
* `gr_chain`: `dim gr^{t+1}(k+2+2t) = dim gr^1(k+2)`.
* `gr_one`, `gr_law`: that block has dimension `dim S_k + dim M_{n+2-k}` (D2 and D4).

D3, which involves the dimension of `S_w^new(Γ₀(ℓ))`, is not here.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound

/-- Dimension of `M_k(SL₂(ℤ))` for even `k`. -/
def dimM (k : ℕ) : ℕ := k / 12 + if k % 12 = 2 then 0 else 1

/-- Dimension of `gr^{t+1}` in class `a`. Integer valued since `dimM` is not monotone. -/
def grDim (n a t : ℕ) : ℤ := (dimM (a + (t + 1) * n) : ℤ) - dimM (a + t * n)

/-- The residue condition satisfied by `ℓ - 1` for every prime `ℓ ≥ 5`. -/
def GoodStep (n : ℕ) : Prop := n % 12 = 0 ∨ n % 12 = 4 ∨ n % 12 = 6 ∨ n % 12 = 10

theorem goodStep_of_prime (ℓ : ℕ) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) : GoodStep (ℓ - 1) := by
  have h2 : ¬ 2 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h
    omega
  have h3 : ¬ 3 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 h
    omega
  unfold GoodStep
  omega

theorem dimM_step (n X : ℕ) (hn : GoodStep n) (hX : X % 2 = 0) (hnX : n ≤ X) :
    dimM X + dimM (X + 2) = dimM (X - n) + dimM (X + n + 2) := by
  unfold GoodStep at hn
  unfold dimM
  split_ifs <;> omega

/-- D1: `dim gr^{t+2}(a+2) = dim gr^{t+1}(a)`. -/
theorem gr_succ_eq (n a t : ℕ) (hn : GoodStep n) (ha : a % 2 = 0) :
    grDim n (a + 2) (t + 1) = grDim n a t := by
  have hn2 : n % 2 = 0 := by unfold GoodStep at hn; omega
  have hX : (a + (t + 1) * n) % 2 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod, hn2, ha]; simp
  have hle : n ≤ a + (t + 1) * n := by
    nlinarith
  have h := dimM_step n (a + (t + 1) * n) hn hX hle
  have e1 : a + (t + 1) * n - n = a + t * n := by
    have : (t + 1) * n = t * n + n := by ring
    omega
  have e2 : a + (t + 1) * n + n + 2 = a + 2 + (t + 1 + 1) * n := by ring
  have e3 : a + (t + 1) * n + 2 = a + 2 + (t + 1) * n := by ring
  rw [e1, e2, e3] at h
  unfold grDim
  have hz : ((dimM (a + (t + 1) * n) : ℤ) + dimM (a + 2 + (t + 1) * n)) =
      (dimM (a + t * n) : ℤ) + dimM (a + 2 + (t + 1 + 1) * n) := by exact_mod_cast h
  linarith

/-- Along a chain the Katz block does not depend on the step. -/
theorem gr_chain (n k t : ℕ) (hn : GoodStep n) (hk : k % 2 = 0) :
    grDim n (k + 2 + 2 * t) t = grDim n (k + 2) 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e : k + 2 + 2 * (t + 1) = (k + 2 + 2 * t) + 2 := by ring
    rw [e, gr_succ_eq n _ t hn (by omega), ih]

/-- D2 and D4 at the bottom of a chain: `dim gr^1(k+2) = dim S_k + dim M_{n+2-k}`. -/
theorem gr_one (n k : ℕ) (hn : GoodStep n) (hk : k % 2 = 0) (hle : k ≤ n + 2) :
    grDim n (k + 2) 0 = ((dimM k : ℤ) - 1) + dimM (n + 2 - k) := by
  unfold GoodStep at hn
  unfold grDim dimM
  simp only [zero_add, one_mul, zero_mul, add_zero]
  push_cast
  split_ifs <;> omega

/-- D2 and D4: the block `gr^{t+1}` in class `k+2+2t` has the dimension the law predicts. -/
theorem gr_law (n k t : ℕ) (hn : GoodStep n) (hk : k % 2 = 0) (hle : k ≤ n + 2) :
    grDim n (k + 2 + 2 * t) t = ((dimM k : ℤ) - 1) + dimM (n + 2 - k) := by
  rw [gr_chain n k t hn hk, gr_one n k hn hk hle]

end RamanujanTau.BLBound
