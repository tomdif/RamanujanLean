/-
# The quintuple product identity in theta form, over `ℂ((t))`

With `q = t^N`, `z = c·tᵉ`, `θ(z) = Σ_k (−1)^k q^{C(k,2)} zᵏ` and `E(q) = Σ_k (−1)^k q^{k(3k−1)/2}`:

  `(Σ_n (−1)ⁿ q^{n(3n−1)/2} z^{3n} (1 + z qⁿ)) · θ(z) = E(q) · θ(z²)`.

Proof: both sides are sums over `ℤ²`. Split the two left families by the parity of `n + m`. One parity
class of each maps bijectively onto half of the right family. The other two classes cancel in pairs.
All three maps are affine, and each term identity is a polynomial identity.
-/
import RamanujanTau.ALChangeZ

set_option autoImplicit false

namespace ALz
open HahnSeries

/-! ## Parity splittings of `ℤ²` -/

/-- `(b, n, j) ↦ (n, n + 2j + b)`. -/
def parEquiv : Bool × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := if x.1 then (x.2.1, x.2.1 + 2 * x.2.2 + 1) else (x.2.1, x.2.1 + 2 * x.2.2)
  invFun p := if (p.2 - p.1) % 2 = 1 then (true, (p.1, (p.2 - p.1 - 1) / 2)) else (false, (p.1, (p.2 - p.1) / 2))
  left_inv := by
    rintro ⟨b, n, j⟩
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs with h <;>
      first | (exfalso; omega) | (simp only [Prod.mk.injEq, true_and, and_true]; omega)
  right_inv := by
    rintro ⟨n, m⟩
    by_cases h : (m - n) % 2 = 1
    · simp only [h, ↓reduceIte, Prod.mk.injEq, true_and]; omega
    · simp only [h, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq, true_and]; omega

/-- `(false, n, j) ↦ (j, 2n + j)`, `(true, n, j) ↦ (−j, 2n + j + 1)`. -/
def parEquivG : Bool × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := if x.1 then (-x.2.2, 2 * x.2.1 + x.2.2 + 1) else (x.2.2, 2 * x.2.1 + x.2.2)
  invFun p := if (p.2 - p.1) % 2 = 1 then (true, ((p.2 + p.1 - 1) / 2, -p.1)) else (false, ((p.2 - p.1) / 2, p.1))
  left_inv := by
    rintro ⟨b, n, j⟩
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs with h <;>
      first | (exfalso; omega) | (simp only [Prod.mk.injEq, true_and, and_true]; omega)
  right_inv := by
    rintro ⟨k, l⟩
    by_cases h : (l - k) % 2 = 1
    · simp only [h, ↓reduceIte, Prod.mk.injEq, true_and, and_true]; omega
    · simp only [h, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq, true_and, and_true]; omega

lemma mono_congr {a a' : ℤ} {b b' : ℂ} (h1 : a = a') (h2 : b = b') : mono a b = mono a' b' := by rw [h1, h2]

lemma hs_fin {ι : Type*} [Fintype ι] (S : SummableFamily ℤ ℂ ι) : hs S = ∑ i, S i := by
  ext k
  rw [hs, SummableFamily.coeff_hsum, finsum_eq_sum_of_fintype, HahnSeries.coeff_sum]

/-- splitting a `ℤ²` family along a `Bool × ℤ² ≃ ℤ²`. -/
lemma hs_split (σ : Bool × (ℤ × ℤ) ≃ ℤ × ℤ) (s : SummableFamily ℤ ℂ (ℤ × ℤ)) :
    hs s = hs (row (SummableFamily.Equiv σ.symm s) false) + hs (row (SummableFamily.Equiv σ.symm s) true) := by
  have h1 : hs s = hs (SummableFamily.Equiv σ.symm s) := by
    rw [hs_eq, hs_eq, SummableFamily.hsum_equiv]
  rw [h1, ← hs_rowFam, hs_fin, Fintype.sum_bool, rowFam_apply, rowFam_apply, add_comm]

@[simp] lemma row_equiv_apply (σ : Bool × (ℤ × ℤ) ≃ ℤ × ℤ) (s : SummableFamily ℤ ℂ (ℤ × ℤ)) (b : Bool)
    (i : ℤ × ℤ) : row (SummableFamily.Equiv σ.symm s) b i = s (σ (b, i)) := by
  simp [row_apply, SummableFamily.Equiv_toFun]

/-! ## Coefficient bookkeeping -/

lemma coef_eq {a b a' b' : ℤ} (c : ℂ) (h1 : Even (a - a')) (h2 : b = b') :
    (-1 : ℂ) ^ a * c ^ b = (-1) ^ a' * c ^ b' := by
  subst h2
  congr 1
  rw [show a = (a - a') + a' by ring, zpow_add₀ (by norm_num), h1.neg_one_zpow, one_mul]

lemma prod_form {c : ℂ} (hc : c ≠ 0) (a b a' b' : ℤ) :
    ((-1 : ℂ) ^ a * c ^ b) * ((-1) ^ a' * c ^ b') = (-1) ^ (a + a') * c ^ (b + b') := by
  rw [zpow_add₀ (by norm_num), zpow_add₀ hc]; ring

lemma thC_pow (c : ℂ) (p : ℕ) (k : ℤ) : thC (c ^ p) k = (-1) ^ k * c ^ ((p : ℤ) * k) := by
  unfold thC; rw [zpow_mul, zpow_natCast]

lemma thC_one' (c : ℂ) (k : ℤ) : thC 1 k = (-1) ^ k * c ^ ((0 : ℤ) * k) := by
  unfold thC; simp

lemma thC_self (c : ℂ) (k : ℤ) : thC c k = (-1) ^ k * c ^ ((1 : ℤ) * k) := by
  unfold thC; rw [one_mul]

lemma shape1 {c : ℂ} (hc : c ≠ 0) (a1 b1 a2 b2 a3 b3 a4 b4 : ℤ) (h1 : Even ((a1 + a2) - (a3 + a4)))
    (h2 : b1 + b2 = b3 + b4) :
    ((-1 : ℂ) ^ a1 * c ^ b1) * ((-1) ^ a2 * c ^ b2) = ((-1) ^ a3 * c ^ b3) * ((-1) ^ a4 * c ^ b4) := by
  rw [prod_form hc, prod_form hc]; exact coef_eq c h1 h2

lemma shape2 {c : ℂ} (hc : c ≠ 0) (a1 b1 a2 b2 a3 b3 a4 b4 : ℤ) (h1 : Even ((a1 + a2) - (a3 + a4)))
    (h2 : b1 + b2 = 1 + (b3 + b4)) :
    ((-1 : ℂ) ^ a1 * c ^ b1) * ((-1) ^ a2 * c ^ b2) = c * (((-1) ^ a3 * c ^ b3) * ((-1) ^ a4 * c ^ b4)) := by
  rw [prod_form hc, prod_form hc, coef_eq c h1 h2, zpow_add₀ hc, zpow_one]; ring

lemma shape3 {c : ℂ} (hc : c ≠ 0) (a1 b1 a2 b2 a3 b3 a4 b4 : ℤ) (h1 : Even ((a1 + a2) - (1 + (a3 + a4))))
    (h2 : b1 + b2 = 1 + (b3 + b4)) :
    ((-1 : ℂ) ^ a1 * c ^ b1) * ((-1) ^ a2 * c ^ b2) = -c * (((-1) ^ a3 * c ^ b3) * ((-1) ^ a4 * c ^ b4)) := by
  rw [prod_form hc, prod_form hc, coef_eq c h1 h2, zpow_add₀ hc, zpow_add₀ (by norm_num), zpow_one, zpow_one]
  ring

/-! ## The identity -/

section Quint
variable {N : ℕ} (hN : 1 ≤ N) (h3 : 1 ≤ 3 * N)

lemma thF_apply' {M : ℕ} (h : 1 ≤ M) (e : ℤ) (c : ℂ) (k : ℤ) : thF h e c k = mono (thE M e k) (thC c k) := rfl

/-- **Quintuple product identity (theta form).** -/
theorem quint_theta (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    (θ h3 (N + 3 * e) (c ^ 3) + mono e c * θ h3 (2 * N + 3 * e) (c ^ 3)) * θ hN e c
      = θ h3 N 1 * θ hN (2 * e) (c ^ 2) := by
  have e1 : θ h3 (N + 3 * e) (c ^ 3) * θ hN e c = hs (SummableFamily.mul (thF h3 (N + 3 * e) (c ^ 3)) (thF hN e c)) := by
    rw [θ, θ, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_mul]
  have e2 : θ h3 (2 * N + 3 * e) (c ^ 3) * θ hN e c
      = hs (SummableFamily.mul (thF h3 (2 * N + 3 * e) (c ^ 3)) (thF hN e c)) := by
    rw [θ, θ, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_mul]
  have eG : θ h3 N 1 * θ hN (2 * e) (c ^ 2) = hs (SummableFamily.mul (thF h3 N 1) (thF hN (2 * e) (c ^ 2))) := by
    rw [θ, θ, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_mul]
  rw [add_mul, mul_assoc, e1, e2, eG, hs_split parEquiv (SummableFamily.mul (thF h3 (N + 3 * e) (c ^ 3)) _),
    hs_split parEquiv (SummableFamily.mul (thF h3 (2 * N + 3 * e) (c ^ 3)) _), hs_split parEquivG (SummableFamily.mul (thF h3 N 1) _)]
  have hA : hs (row (SummableFamily.Equiv parEquiv.symm
        (SummableFamily.mul (thF h3 (N + 3 * e) (c ^ 3)) (thF hN e c))) false)
      = hs (row (SummableFamily.Equiv parEquivG.symm
        (SummableFamily.mul (thF h3 N 1) (thF hN (2 * e) (c ^ 2)))) false) := by
    refine hsum_congr _ _ fun ⟨n, j⟩ => ?_
    simp only [row_equiv_apply, SummableFamily.mul_toFun, parEquiv, parEquivG, Equiv.coe_fn_mk,
      Bool.false_eq_true, ↓reduceIte, thF_apply', mono_mul]
    refine mono_congr ?_ ?_
    · have h1 := two_c2 n; have h2 := two_c2 (n + 2 * j); have h3 := two_c2 j
      have h4 := two_c2 (2 * n + j)
      unfold thE; push_cast
      refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
      linear_combination (3 * (N : ℤ)) * h1 + (N : ℤ) * h2 - (3 * (N : ℤ)) * h3 - (N : ℤ) * h4
    · simp only [thC_pow]; rw [thC_one' c]; simp only [thC_self]
      exact shape1 hc _ _ _ _ _ _ _ _ ⟨0, by ring⟩ (by push_cast; ring)
  have hB : mono e c * hs (row (SummableFamily.Equiv parEquiv.symm
        (SummableFamily.mul (thF h3 (2 * N + 3 * e) (c ^ 3)) (thF hN e c))) true)
      = hs (row (SummableFamily.Equiv parEquivG.symm
        (SummableFamily.mul (thF h3 N 1) (thF hN (2 * e) (c ^ 2)))) true) := by
    refine (hsum_reindex _ _ (Equiv.refl _) _ fun ⟨n, j⟩ => ?_).symm
    simp only [Equiv.refl_apply, row_equiv_apply, SummableFamily.mul_toFun, parEquiv, parEquivG,
      Equiv.coe_fn_mk, ↓reduceIte, thF_apply', mono_mul]
    refine mono_congr ?_ ?_
    · have h1 := two_c2 n; have h2 := two_c2 (n + 2 * j + 1); have h3 := two_c2 (-j)
      have h4 := two_c2 (2 * n + j + 1)
      unfold thE; push_cast
      refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
      linear_combination (3 * (N : ℤ)) * h3 + (N : ℤ) * h4 - (3 * (N : ℤ)) * h1 - (N : ℤ) * h2
    · simp only [thC_pow]; rw [thC_one' c]; simp only [thC_self]
      exact shape2 hc _ _ _ _ _ _ _ _ ⟨-j, by ring⟩ (by push_cast; ring)
  have hC : hs (row (SummableFamily.Equiv parEquiv.symm
        (SummableFamily.mul (thF h3 (N + 3 * e) (c ^ 3)) (thF hN e c))) true)
      = -mono e c * hs (row (SummableFamily.Equiv parEquiv.symm
        (SummableFamily.mul (thF h3 (2 * N + 3 * e) (c ^ 3)) (thF hN e c))) false) := by
    refine hsum_reindex _ _ ⟨fun p => (p.1 + p.2, -p.2), fun p => (p.1 + p.2, -p.2),
      fun p => by simp, fun p => by simp⟩ _ fun ⟨n, j⟩ => ?_
    simp only [Equiv.coe_fn_mk, row_equiv_apply, SummableFamily.mul_toFun, parEquiv,
      Bool.false_eq_true, ↓reduceIte, thF_apply', mono_mul]
    rw [← single_neg, mono_mul]
    refine mono_congr ?_ ?_
    · have h1 := two_c2 (n + j); have h2 := two_c2 (n + j + 2 * -j + 1); have h3 := two_c2 n
      have h4 := two_c2 (n + 2 * j)
      unfold thE; push_cast
      refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
      linear_combination (3 * (N : ℤ)) * h1 + (N : ℤ) * h2 - (3 * (N : ℤ)) * h3 - (N : ℤ) * h4
    · simp only [thC_pow]; simp only [thC_self]
      exact shape3 hc _ _ _ _ _ _ _ _ ⟨-j, by ring⟩ (by push_cast; ring)
  rw [hC, ← hA, ← hB]; ring

end Quint

end ALz
