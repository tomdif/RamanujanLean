/-
# The product identities of the MTC₀ endgame (`Q = t^{168}`, atoms `PA₁₆₈ r M = ιN (Q^r;Q^M)_∞`)

* `PI1`: `J₁ J³ j₁₀ J̄_{1,5} = J_{5,10} J_{2,5} j₂ j₁₂ j₈ J̄_{5,20}`;
* `PI2`: `J₁ J³ j₁₀ J_{2,20} j̄₄j̄₆j̄₁₄j̄₁₆ j_{20} = κ₄₀ J_{5,20} J_{1,20} J_{9,20} J_{2,5} j₂ j₁₂ j₈ J̄_{5,20}`
  (bars on `j̄` here are base `Q⁴⁰`; `J = (Q³⁰;Q³⁰)_∞`, `κ₄₀ = (Q⁴⁰;Q⁴⁰)³_∞`, `J₁ = (Q;Q)_∞ = j(Q²;Q³)`).
-/
import RamanujanTau.MTC.ProdId
import RamanujanTau.MTC.Endgame2

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

lemma ιN_N {N N' : ℕ} (h : N = N') (hN : 1 ≤ N) (hN' : 1 ≤ N') (f : PowerSeries ℤ) : ιN hN f = ιN hN' f := by
  subst h; rfl

/-- `X ↦ t^{dk}` is `X ↦ X^k` followed by `X ↦ t^d`. -/
lemma ιN_Ea {d k : ℕ} (hd : 1 ≤ d) (hk : k ≠ 0) (h : 1 ≤ d * k) (f : PowerSeries ℤ) :
    ιN h f = ιN hd (Ea k hk f) := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [ιN_coeff_neg h _ hn, ιN_coeff_neg hd _ hn]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    rw [ιN_coeff_nat, ιN_coeff_nat, coeff_Ea]
    have hd0 : 0 < d := by omega
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    by_cases h1 : d * k ∣ m
    · obtain ⟨t, rfl⟩ := h1
      rw [if_pos ⟨t, rfl⟩, if_pos ⟨k * t, by ring⟩, show d * k * t / d = k * t by
          rw [mul_assoc, Nat.mul_div_cancel_left _ hd0],
        if_pos (dvd_mul_right k t), Nat.mul_div_cancel_left _ (Nat.mul_pos hd0 hk0), Nat.mul_div_cancel_left _ hk0]
    · rw [if_neg h1]
      by_cases h2 : d ∣ m
      · obtain ⟨s, rfl⟩ := h2
        rw [if_pos ⟨s, rfl⟩, Nat.mul_div_cancel_left _ hd0]
        have h3 : ¬ k ∣ s := fun ⟨t, ht⟩ => h1 ⟨t, by rw [ht]; ring⟩
        rw [if_neg h3]; simp
      · rw [if_neg h2]

lemma J30_PA (k : ℕ) (hk : 1 ≤ k) :
    ιN (h120 hqT) MockTheta5.JTP.qfacInf = ∏ j ∈ range k, PA h168 (30 + 30 * j) (k * 30) := by
  rw [ιN_N (show 120 * 42 = 168 * 30 by norm_num) _ (show 1 ≤ 168 * 30 by norm_num),
    ιN_Ea h168 (by norm_num : (30 : ℕ) ≠ 0), ← Pinf_one_one, Ea_Pinf 30 1 1 _ le_rfl le_rfl,
    ιN_Pinf_split h168 _ _ k (by norm_num) (by norm_num) hk]

lemma J40_PA (k : ℕ) (hk : 1 ≤ k) :
    ιN (h160 hqT) MockTheta5.JTP.qfacInf = ∏ j ∈ range k, PA h168 (40 + 40 * j) (k * 40) := by
  rw [ιN_N (show 160 * 42 = 168 * 40 by norm_num) _ (show 1 ≤ 168 * 40 by norm_num),
    ιN_Ea h168 (by norm_num : (40 : ℕ) ≠ 0), ← Pinf_one_one, Ea_Pinf 40 1 1 _ le_rfl le_rfl,
    ιN_Pinf_split h168 _ _ k (by norm_num) (by norm_num) hk]

lemma Jp_PA (b a k : ℕ) (hb : 1 ≤ b) (hab : b < a) (hk : 1 ≤ k) : ιN h168 (Jp b a) = PJ h168 b a k := by
  rw [Jp, map_mul, map_mul, ιN_Pinf_split h168 b a k hb (by omega) hk,
    ιN_Pinf_split h168 (a - b) a k (by omega) (by omega) hk, ιN_Pinf_split h168 a a k (by omega) (by omega) hk]
  rfl

/-- **PI1**. -/
theorem PI1 :
    θ h504 336 1 * (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 10 * θ h840 168 (-1) =
      ιN h168 (Jp 5 10 * Jp 2 5) * j30 2 * j30 12 * j30 8 * B20 5 := by
  unfold j30 B20
  rw [map_mul, Jp_PA 5 10 12 (by norm_num) (by norm_num) (by norm_num), Jp_PA 2 5 24 (by norm_num) (by norm_num) (by norm_num),
    J30_PA 4 (by norm_num),
    θu h168 h504 3 2 40 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h840 5 1 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 10 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 2 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 12 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 8 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h3360 20 5 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 120 ≠ 0 := fun r hr => PA_ne h168 r 120 hr (by norm_num)
  field_simp [hP]

/-- **PI2**. -/
theorem PI2 :
    θ h504 336 1 * (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 10 * J20 2 * jB 4 * jB 6 * jB 14 * jB 16 *
        jA 20 =
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * J20 5 * J20 1 * J20 9 * J5 2 * j30 2 * j30 12 * j30 8 *
        B20 5 := by
  unfold j30 B20 J20 J5 jA jB
  rw [J30_PA 8 (by norm_num), J40_PA 6 (by norm_num),
    θu h168 h504 3 2 80 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 10 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 2 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 12 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 8 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 2 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 5 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 1 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 9 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h840 5 2 48 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h160 hqT) 40 20 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 4 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 6 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 14 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 16 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h3360 20 5 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 240 ≠ 0 := fun r hr => PA_ne h168 r 240 hr (by norm_num)
  field_simp [hP]

end MTC
