/-
# Weierstrass' three-term relation with two points of valuation zero

Same engine as `ALTheta.weierstrass`, for `u = c_u`, `v = c_v` (valuation `0`), `c_u ≠ c_v`, `c_u c_v ≠ 1`:
the determinant's `t⁰`-coefficient is `(1 + c₁²) c₂ − (1 + c₂²) c₁ = (c₂ − c₁)(1 − c₁ c₂)`.
-/
import RamanujanTau.ALTheta

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section Engine0
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma e0M_zero0 (c : ℂ) :
    (hs (e0M hN 0 1 0 c)).coeff 0 = 1 + c ^ 2 ∧ ∀ n < 0, (hs (e0M hN 0 1 0 c)).coeff n = 0 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hE : ∀ m : ℤ, thE (2 * N) (2 * 0 + 0) m = N * (m * (m - 1)) := by
    intro m; unfold thE c2; have := Int.ediv_mul_cancel (show (2 : ℤ) ∣ m * (m - 1) from by
      rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (k + k - 1), by ring⟩
      · exact ⟨(2 * k + 1) * k, by ring⟩); push_cast; nlinarith
  have hnn : ∀ m : ℤ, 0 ≤ (N : ℤ) * (m * (m - 1)) := fun m => by
    have : 0 ≤ m * (m - 1) := by nlinarith [sq_nonneg (2 * m - 1)]
    positivity
  refine ⟨?_, fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun m => ?_⟩
  · unfold e0M
    rw [monoFam_coeff, finsum_eq_sum_of_support_subset (s := {0, 1})]
    · rw [Finset.sum_pair (by norm_num)]
      simp only [hE]
      norm_num
      exact zpow_ofNat c 2
    · intro m hm
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hm
      obtain ⟨h1, -⟩ := hm
      rw [hE] at h1
      have : m * (m - 1) = 0 := by
        rcases (mul_eq_zero.mp h1) with h | h
        · omega
        · exact h
      rcases mul_eq_zero.mp this with h | h
      · simp [h]
      · simp [show m = 1 by omega]
  · rw [hE]; have := hnn m; omega

lemma e1M_zero0 (c : ℂ) :
    (hs (e1M hN 0 1 0 c)).coeff 0 = c ∧ ∀ n < 0, (hs (e1M hN 0 1 0 c)).coeff n = 0 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hE : ∀ m : ℤ, thE (2 * N) (N + 2 * 0 + 0) m + 0 = N * (m * m) := by
    intro m; unfold thE c2; have := Int.ediv_mul_cancel (show (2 : ℤ) ∣ m * (m - 1) from by
      rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (k + k - 1), by ring⟩
      · exact ⟨(2 * k + 1) * k, by ring⟩); push_cast; nlinarith
  refine ⟨?_, fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun m => ?_⟩
  · unfold e1M
    rw [monoFam_coeff_at _ _ _ _ _ 0 0 (by rw [hE]; ring) fun m hm => by
      rw [hE]; intro h; rcases mul_eq_zero.mp h with h | h
      · omega
      · exact hm (by nlinarith [sq_nonneg m])]
    simp
  · rw [hE]; have : 0 ≤ (N : ℤ) * (m * m) := mul_nonneg (by positivity) (mul_self_nonneg m)
    omega

theorem det_x0 {c₁ c₂ : ℂ} (h12 : c₁ ≠ c₂) (h1 : c₁ * c₂ ≠ 1) :
    hs (e0M hN 0 1 0 c₁) * hs (e1M hN 0 1 0 c₂) - hs (e0M hN 0 1 0 c₂) * hs (e1M hN 0 1 0 c₁) ≠ 0 := by
  obtain ⟨P0, Pb⟩ := e0M_zero0 hN c₁
  obtain ⟨R0, Rb⟩ := e0M_zero0 hN c₂
  obtain ⟨S0, Sb⟩ := e1M_zero0 hN c₂
  obtain ⟨Q0, Qb⟩ := e1M_zero0 hN c₁
  intro hΔ
  have := congrArg (fun f : L => f.coeff 0) hΔ
  simp only [coeff_sub, coeff_zero] at this
  have e1 := coeff_mul_lowest _ _ 0 0 Pb Sb
  have e2 := coeff_mul_lowest _ _ 0 0 Rb Qb
  rw [zero_add] at e1 e2
  rw [e1, e2, P0, S0, R0, Q0] at this
  have h : (c₂ - c₁) * (1 - c₁ * c₂) = 0 := by linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact h12 (by linear_combination -h)
  · exact h1 (by linear_combination -h)

theorem sol_vanish_x0 {c₁ c₂ : ℂ} (hc1 : c₁ ≠ 0) (hc2 : c₂ ≠ 0) (h12 : c₁ ≠ c₂) (h1 : c₁ * c₂ ≠ 1)
    (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N 0 1 k * F k)
    (S₁ S₂ : SummableFamily ℤ ℂ ℤ) (hS₁ : ∀ k, S₁ k = (mono 0 c₁) ^ k * F k)
    (hS₂ : ∀ k, S₂ k = (mono 0 c₂) ^ k * F k) (e₁ : hs S₁ = 0) (e₂ : hs S₂ = 0) : ∀ k, F k = 0 := by
  have d₁ := ev_decomp hN 0 one_ne_zero F hF 0 hc1 S₁ hS₁
  have d₂ := ev_decomp hN 0 one_ne_zero F hF 0 hc2 S₂ hS₂
  rw [e₁, hs_e0Fam, hs_e1Fam] at d₁
  rw [e₂, hs_e0Fam, hs_e1Fam] at d₂
  have hΔ := det_x0 hN h12 h1
  set P := hs (e0M hN 0 1 0 c₁); set Q := hs (e1M hN 0 1 0 c₁)
  set R := hs (e0M hN 0 1 0 c₂); set S := hs (e1M hN 0 1 0 c₂)
  have f0 : F 0 * (P * S - R * Q) = 0 := by linear_combination (-S) * d₁ + Q * d₂
  have f1 : F 1 * (P * S - R * Q) = 0 := by linear_combination R * d₁ - P * d₂
  have z0 := (mul_eq_zero.mp f0).resolve_right hΔ
  have z1 := (mul_eq_zero.mp f1).resolve_right hΔ
  intro k
  rw [sol_basis one_ne_zero F hF k, z0, z1]; ring

/-- Weierstrass from a vanishing principle at the two points `u, v`. -/
theorem weierstrass_of {by' bu bv bx : ℤ} {cy cu cv cx : ℂ} (hcy : cy ≠ 0) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hcx : cx ≠ 0)
    (hvan : ∀ (F : ℤ → L), (∀ k, F (k + 2) = mult N 0 1 k * F k) → ∀ (S₁ S₂ : SummableFamily ℤ ℂ ℤ),
      (∀ k, S₁ k = (mono bu cu) ^ k * F k) → (∀ k, S₂ k = (mono bv cv) ^ k * F k) → hs S₁ = 0 → hs S₂ = 0 →
      ∀ k, F k = 0) :
    θ hN (bx + by') (cx * cy) * θ hN (bx - by') (cx * cy⁻¹) * θ hN (bu + bv) (cu * cv) * θ hN (bu - bv) (cu * cv⁻¹)
      - θ hN (bx + bv) (cx * cv) * θ hN (bx - bv) (cx * cv⁻¹) * θ hN (bu + by') (cu * cy) * θ hN (bu - by') (cu * cy⁻¹)
      = mono (bu - by') (cu * cy⁻¹) * θ hN (by' + bv) (cy * cv) * θ hN (by' - bv) (cy * cv⁻¹) *
          θ hN (bx + bu) (cx * cu) * θ hN (bx - bu) (cx * cu⁻¹) := by
  set c1 := θ hN (bu + bv) (cu * cv) * θ hN (bu - bv) (cu * cv⁻¹)
  set c2 := θ hN (bu + by') (cu * cy) * θ hN (bu - by') (cu * cy⁻¹)
  set c3 := mono (bu - by') (cu * cy⁻¹) * θ hN (by' + bv) (cy * cv) * θ hN (by' - bv) (cy * cv⁻¹)
  set F : ℤ → L := fun k => c1 * TT hN by' cy (-by') cy⁻¹ k - c2 * TT hN bv cv (-bv) cv⁻¹ k
    - c3 * TT hN bu cu (-bu) cu⁻¹ k
  have hmul : ∀ (b : ℤ) (c : ℂ), c ≠ 0 → ∀ k : ℤ, mono (N * k + (b + -b)) (c * c⁻¹) = mult N 0 1 k := by
    intro b c hc k; unfold mult; rw [mul_inv_cancel₀ hc]; congr 1; ring
  have hF : ∀ k, F (k + 2) = mult N 0 1 k * F k := by
    intro k; simp only [F]
    rw [TT_rec hN by' hcy (-by') (inv_ne_zero hcy), TT_rec hN bv hcv (-bv) (inv_ne_zero hcv),
      TT_rec hN bu hcu (-bu) (inv_ne_zero hcu), hmul by' cy hcy, hmul bv cv hcv, hmul bu cu hcu]
    ring
  -- the evaluation family at `c_p t^β`
  let Fv : ℤ → ℂ → SummableFamily ℤ ℂ ℤ := fun β cp =>
    c1 • wFam hN by' cy β cp - c2 • wFam hN bv cv β cp - c3 • wFam hN bu cu β cp
  have hFv : ∀ β cp, cp ≠ 0 → ∀ k, Fv β cp k = (mono β cp) ^ k * F k := by
    intro β cp hp k
    simp only [Fv, wFam, F, SummableFamily.sub_apply, SummableFamily.smul_apply,
      HahnSeries.of_symm_smul_of_eq_mul]
    rw [ttEv_apply hN _ _ _ _ _ hp, ttEv_apply hN _ _ _ _ _ hp, ttEv_apply hN _ _ _ _ _ hp]
    ring
  have hsum : ∀ β cp, hs (Fv β cp) =
      c1 * (θ hN (by' + β) (cy * cp) * θ hN (-by' + β) (cy⁻¹ * cp))
      - c2 * (θ hN (bv + β) (cv * cp) * θ hN (-bv + β) (cv⁻¹ * cp))
      - c3 * (θ hN (bu + β) (cu * cp) * θ hN (-bu + β) (cu⁻¹ * cp)) := by
    intro β cp
    simp only [Fv, wFam]
    rw [hs_eq, SummableFamily.hsum_sub, SummableFamily.hsum_sub, SummableFamily.hsum_smul,
      SummableFamily.hsum_smul, SummableFamily.hsum_smul, ← hs_eq, ← hs_eq, ← hs_eq, ttEv_sum, ttEv_sum,
      ttEv_sum]
  have hθ0 := θ_one hN
  -- zero at `x = u`
  have zu : hs (Fv bu cu) = 0 := by
    rw [hsum, show -bu + bu = 0 by ring, inv_mul_cancel₀ hcu, hθ0, mul_zero, mul_zero, sub_zero]
    simp only [c1, c2]
    rw [show by' + bu = bu + by' by ring, show cy * cu = cu * cy by ring, show -by' + bu = bu - by' by ring,
      show cy⁻¹ * cu = cu * cy⁻¹ by ring, show bv + bu = bu + bv by ring, show cv * cu = cu * cv by ring,
      show -bv + bu = bu - bv by ring, show cv⁻¹ * cu = cu * cv⁻¹ by ring]
    ring
  -- zero at `x = v`
  have zv : hs (Fv bv cv) = 0 := by
    rw [hsum, show -bv + bv = 0 by ring, inv_mul_cancel₀ hcv, hθ0, mul_zero, mul_zero, sub_zero]
    simp only [c1, c3]
    have i1 : θ hN (-by' + bv) (cy⁻¹ * cv) = -mono (-(by' - bv)) (cy * cv⁻¹)⁻¹ * θ hN (by' - bv) (cy * cv⁻¹) := by
      rw [← θ_inv hN _ (mul_ne_zero hcy (inv_ne_zero hcv))]; congr 1 <;> [ring; field_simp]
    have i2 : θ hN (-bu + bv) (cu⁻¹ * cv) = -mono (-(bu - bv)) (cu * cv⁻¹)⁻¹ * θ hN (bu - bv) (cu * cv⁻¹) := by
      rw [← θ_inv hN _ (mul_ne_zero hcu (inv_ne_zero hcv))]; congr 1 <;> [ring; field_simp]
    have mm : mono (bu - by') (cu * cy⁻¹) * mono (-(bu - bv)) (cu * cv⁻¹)⁻¹ = mono (-(by' - bv)) (cy * cv⁻¹)⁻¹ := by
      rw [mono_mul]; congr 1 <;> [ring; field_simp]
    rw [i1, i2, show bu + bv = bv + bu by ring, show cu * cv = cv * cu by ring,
      show by' + bv = bv + by' by ring, show cy * cv = cv * cy by ring] at *
    rw [← mm]
    ring
  have hall := hvan F hF (Fv bu cu) (Fv bv cv) (hFv bu cu hcu) (hFv bv cv hcv) zu zv
  have zx := ev_decomp hN 0 one_ne_zero F hF bx hcx (Fv bx cx) (hFv bx cx hcx)
  rw [hall 0, hall 1, zero_mul, zero_mul, add_zero, hsum] at zx
  simp only [c1, c2, c3] at zx
  rw [show by' + bx = bx + by' by ring, show cy * cx = cx * cy by ring, show -by' + bx = bx - by' by ring,
    show cy⁻¹ * cx = cx * cy⁻¹ by ring, show bv + bx = bx + bv by ring, show cv * cx = cx * cv by ring,
    show -bv + bx = bx - bv by ring, show cv⁻¹ * cx = cx * cv⁻¹ by ring, show bu + bx = bx + bu by ring,
    show cu * cx = cx * cu by ring, show -bu + bx = bx - bu by ring, show cu⁻¹ * cx = cx * cu⁻¹ by ring] at zx
  linear_combination zx

/-- **Weierstrass' three-term relation, valuation-zero `u, v`** (`c_u ≠ c_v`, `c_u c_v ≠ 1`). -/
theorem weierstrass0 {by' bx : ℤ} {cy cu cv cx : ℂ} (hcy : cy ≠ 0) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hcx : cx ≠ 0) (h12 : cu ≠ cv) (h1 : cu * cv ≠ 1) :
    θ hN (bx + by') (cx * cy) * θ hN (bx - by') (cx * cy⁻¹) * θ hN (0 + 0) (cu * cv) * θ hN (0 - 0) (cu * cv⁻¹)
      - θ hN (bx + 0) (cx * cv) * θ hN (bx - 0) (cx * cv⁻¹) * θ hN (0 + by') (cu * cy) * θ hN (0 - by') (cu * cy⁻¹)
      = mono (0 - by') (cu * cy⁻¹) * θ hN (by' + 0) (cy * cv) * θ hN (by' - 0) (cy * cv⁻¹) *
          θ hN (bx + 0) (cx * cu) * θ hN (bx - 0) (cx * cu⁻¹) :=
  weierstrass_of hN hcy hcu hcv hcx fun F hF S₁ S₂ h₁ h₂ e₁ e₂ =>
    sol_vanish_x0 hN hcu hcv h12 h1 F hF S₁ S₂ h₁ h₂ e₁ e₂

end Engine0
end ALz
