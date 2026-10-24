/-
# Products of two theta functions (HM (1.4b))

`j(x; q) j(y; q) = j(−xy; q²) j(−q x⁻¹ y; q²) − x j(−q x y; q²) j(−x⁻¹ y; q²)`, here in the form
`θ_N(e₁,c₁) θ_N(e₂,c₂) = θ_{2N}(e₁+e₂, −c₁c₂) θ_{2N}(N+e₁−e₂, −c₁/c₂)
   − c₁t^{e₁} θ_{2N}(N+e₁+e₂, −c₁c₂) θ_{2N}(2N+e₁−e₂, −c₁/c₂)`
(`θ_mul`): split the product family by the parity of `m + n`, `(m, n) = (u + v, u − v)` or `(u + v + 1, u − v)`.
Adding and subtracting the instances at `(−c₁, c₂)` and `(c₁, −c₂)` gives HM (1.4c), (1.4d) (`θ_mul_plus`,
`θ_mul_minus`).
-/
import RamanujanTau.ALTheta
import RamanujanTau.MTC.F373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-- the even-sum embedding `(u, v) ↦ (u + v, u − v)`. -/
def psE : ℤ × ℤ ↪ ℤ × ℤ := ⟨fun p => (p.1 + p.2, p.1 - p.2), fun p q h => by
  simp only [Prod.mk.injEq] at h; ext <;> omega⟩

/-- the odd-sum embedding `(u, v) ↦ (u + v + 1, u − v)`. -/
def psO : ℤ × ℤ ↪ ℤ × ℤ := ⟨fun p => (p.1 + p.2 + 1, p.1 - p.2), fun p q h => by
  simp only [Prod.mk.injEq] at h; ext <;> omega⟩

section Mul
variable {N : ℕ} (hN : 1 ≤ N)

lemma h2N (hN : 1 ≤ N) : 1 ≤ 2 * N := by omega

lemma neg_mono_t (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

lemma coeffE {c1 c2 : ℂ} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (u v : ℤ) :
    (-1) ^ (u + v) * c1 ^ (u + v) * ((-1) ^ (u - v) * c2 ^ (u - v)) =
      (-1) ^ u * (-(c1 * c2)) ^ u * ((-1) ^ v * (-(c1 / c2)) ^ v) := by
  have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
  rw [neg_eq_neg_one_mul (c1 * c2), neg_eq_neg_one_mul (c1 / c2), mul_zpow, mul_zpow, mul_zpow, div_zpow,
    zpow_add₀ hm, zpow_add₀ hc1, zpow_sub₀ hm, zpow_sub₀ hc2]
  simp only [div_eq_mul_inv]
  rw [← eq_inv_of_mul_eq_one_left (neg_one_zpow_sq v)]
  ring

lemma coeffO {c1 c2 : ℂ} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (u v : ℤ) :
    (-1) ^ (u + v + 1) * c1 ^ (u + v + 1) * ((-1) ^ (u - v) * c2 ^ (u - v)) =
      -(c1 * ((-1) ^ u * (-(c1 * c2)) ^ u * ((-1) ^ v * (-(c1 / c2)) ^ v))) := by
  have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
  have := coeffE hc1 hc2 u v
  rw [zpow_add_one₀ hm, zpow_add_one₀ hc1]
  linear_combination (-c1) * this

theorem θ_mul (e1 e2 : ℤ) {c1 c2 : ℂ} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) :
    θ hN e1 c1 * θ hN e2 c2 =
      θ (h2N hN) (e1 + e2) (-(c1 * c2)) * θ (h2N hN) (N + e1 - e2) (-(c1 / c2)) -
        mono e1 c1 * (θ (h2N hN) (N + e1 + e2) (-(c1 * c2)) * θ (h2N hN) (2 * N + e1 - e2) (-(c1 / c2))) := by
  set P := (thF hN e1 c1).mul (thF hN e2 c2)
  set E := (thF (h2N hN) (e1 + e2) (-(c1 * c2))).mul (thF (h2N hN) (N + e1 - e2) (-(c1 / c2)))
  set O := (thF (h2N hN) (N + e1 + e2) (-(c1 * c2))).mul (thF (h2N hN) (2 * N + e1 - e2) (-(c1 / c2)))
  have hP : θ hN e1 c1 * θ hN e2 c2 = hs P := by
    unfold θ; rw [hs, hs, hs, SummableFamily.hsum_mul]
  have hE : θ (h2N hN) (e1 + e2) (-(c1 * c2)) * θ (h2N hN) (N + e1 - e2) (-(c1 / c2)) = hs E := by
    unfold θ; rw [hs, hs, hs, SummableFamily.hsum_mul]
  have hO : θ (h2N hN) (N + e1 + e2) (-(c1 * c2)) * θ (h2N hN) (2 * N + e1 - e2) (-(c1 / c2)) = hs O := by
    unfold θ; rw [hs, hs, hs, SummableFamily.hsum_mul]
  have hsplit : P = E.embDomain psE + (-mono e1 c1) • O.embDomain psO := by
    ext ⟨m, n⟩ : 1
    simp only [SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul]
    by_cases hpar : (m - n) % 2 = 0
    · have hq : psE (((m + n) / 2), ((m - n) / 2)) = (m, n) := by
        show (((m + n) / 2) + ((m - n) / 2), ((m + n) / 2) - ((m - n) / 2)) = (m, n)
        rw [Prod.mk.injEq]; omega
      rw [← hq, SummableFamily.embDomain_image,
        SummableFamily.embDomain_notin_range (s := O) (f := psO) (b := psE ((m + n) / 2, (m - n) / 2)) (by
          rintro ⟨p, hp⟩
          have h1 : psO p = psE ((m + n) / 2, (m - n) / 2) := hp
          change (p.1 + p.2 + 1, p.1 - p.2) = (((m + n) / 2) + ((m - n) / 2), ((m + n) / 2) - ((m - n) / 2)) at h1
          rw [Prod.mk.injEq] at h1; omega),
        mul_zero, add_zero]
      set u := (m + n) / 2
      set v := (m - n) / 2
      show thF hN e1 c1 (u + v) * thF hN e2 c2 (u - v) =
        thF (h2N hN) (e1 + e2) (-(c1 * c2)) u * thF (h2N hN) (N + e1 - e2) (-(c1 / c2)) v
      simp only [thF, monoFam_apply, mono_mul, thE, thC]
      refine mono_ext ?_ (coeffE hc1 hc2 u v)
      have h1 := two_c2 (u + v); have h2 := two_c2 (u - v); have h3 := two_c2 u; have h4 := two_c2 v
      push_cast
      apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
      linear_combination (N : ℤ) * h1 + (N : ℤ) * h2 - 2 * (N : ℤ) * h3 - 2 * (N : ℤ) * h4
    · have hq : psO (((m + n - 1) / 2), ((m - n - 1) / 2)) = (m, n) := by
        show (((m + n - 1) / 2) + ((m - n - 1) / 2) + 1, ((m + n - 1) / 2) - ((m - n - 1) / 2)) = (m, n)
        rw [Prod.mk.injEq]; omega
      rw [← hq, SummableFamily.embDomain_image,
        SummableFamily.embDomain_notin_range (s := E) (f := psE) (b := psO ((m + n - 1) / 2, (m - n - 1) / 2)) (by
          rintro ⟨p, hp⟩
          have h1 : psE p = psO ((m + n - 1) / 2, (m - n - 1) / 2) := hp
          change (p.1 + p.2, p.1 - p.2) =
            (((m + n - 1) / 2) + ((m - n - 1) / 2) + 1, ((m + n - 1) / 2) - ((m - n - 1) / 2)) at h1
          rw [Prod.mk.injEq] at h1; omega),
        zero_add]
      set u := (m + n - 1) / 2
      set v := (m - n - 1) / 2
      show thF hN e1 c1 (u + v + 1) * thF hN e2 c2 (u - v) =
        -mono e1 c1 * (thF (h2N hN) (N + e1 + e2) (-(c1 * c2)) u * thF (h2N hN) (2 * N + e1 - e2) (-(c1 / c2)) v)
      simp only [thF, monoFam_apply, mono_mul, thE, thC, neg_mul, neg_mono_t]
      refine mono_ext ?_ (coeffO hc1 hc2 u v)
      have h1 := two_c2 (u + v + 1); have h2 := two_c2 (u - v); have h3 := two_c2 u; have h4 := two_c2 v
      push_cast
      apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
      linear_combination (N : ℤ) * h1 + (N : ℤ) * h2 - 2 * (N : ℤ) * h3 - 2 * (N : ℤ) * h4
  rw [hP, hE, hO, hsplit, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_smul, SummableFamily.hsum_embDomain,
    SummableFamily.hsum_embDomain, hs_eq, hs_eq]
  ring

end Mul

end MTC
