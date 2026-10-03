/-
# A theta-identity engine: the Weierstrass three-term relation

For theta values `θ(w) = Σ_k (−1)^k q^{C(k,2)} wᵏ` at monomial points of `ℂ((t))`, `q = t^N`:
`θ(xy)θ(x/y)θ(uv)θ(u/v) − θ(xv)θ(x/v)θ(uy)θ(u/y) = (u/y) θ(yv)θ(y/v)θ(xu)θ(x/u)`.
Proof: as a series in a free `x` both sides lie in the 2-dimensional space of
`F_{k+2} = q^k F_k`; their difference vanishes at `x = u` and `x = v`; a determinant
with an explicit leading term (`0 < val u < val v < N/2`) forces it to vanish.
Test: Atkin–Swinnerton-Dyer's identity `J₂³J₃ = J₁J₃³ + q J₁³J₂` (base `q⁷`).
-/
import RamanujanTau.ALRank7

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section Engine
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `θ(q/y) = θ(y)`. -/
theorem θ_reflect (e : ℤ) {c : ℂ} (hc : c ≠ 0) : θ hN (N - e) c⁻¹ = θ hN e c := by
  refine (hsum_reindex' (thF hN e c) (thF hN (N - e) c⁻¹) (Equiv.neg ℤ) 1 fun k => ?_).trans (one_mul _)
  simp only [sv, thF_apply, thT, Equiv.neg_apply, one_mul, thE, thC]
  congr 1
  · have h1 := two_c2 (-k); have h2 := two_c2 k; nlinarith
  · rw [inv_zpow', neg_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]

/-- the determinant for the multiplier `q^k` (i.e. `x = 1`) at two points of valuations
`0 < β₁ < β₂ < N/2`. -/
theorem det_x1 {β₁ β₂ : ℤ} (h1 : 0 < β₁) (h12 : β₁ < β₂) (h2 : 2 * β₂ < N) {c₁ c₂ : ℂ} (hc1 : c₁ ≠ 0) :
    hs (e0M hN 0 1 β₁ c₁) * hs (e1M hN 0 1 β₂ c₂) - hs (e0M hN 0 1 β₂ c₂) * hs (e1M hN 0 1 β₁ c₁) ≠ 0 := by
  obtain ⟨P0, Pb⟩ := e0M_low hN (β := β₁) (a := 0) 1 c₁ (by omega) (by omega)
  obtain ⟨R0, Rb⟩ := e0M_low hN (β := β₂) (a := 0) 1 c₂ (by omega) (by omega)
  obtain ⟨S0, Sb⟩ := e1M_low hN (β := β₂) (a := 0) 1 c₂ (by omega) (by omega)
  obtain ⟨Q0, Qb⟩ := e1M_low hN (β := β₁) (a := 0) 1 c₁ (by omega) (by omega)
  intro hΔ
  have := congrArg (fun f : L => f.coeff β₁) hΔ
  simp only [coeff_sub, coeff_zero] at this
  have e2 := coeff_mul_lowest _ _ 0 β₁ Rb Qb
  rw [zero_add] at e2
  have hS' : ∀ n < β₂, (hs (e1M hN 0 1 β₂ c₂)).coeff n = 0 := Sb
  rw [coeff_mul_below _ _ 0 β₂ Pb hS' _ (by omega), e2, R0, Q0] at this
  exact hc1 (by linear_combination -this)

/-- a solution of `F_{k+2} = q^k F_k` vanishing (after evaluation) at two points with
`0 < β₁ < β₂ < N/2` is zero. -/
theorem sol_vanish_x1 {β₁ β₂ : ℤ} (h1 : 0 < β₁) (h12 : β₁ < β₂) (h2 : 2 * β₂ < N) {c₁ c₂ : ℂ}
    (hc1 : c₁ ≠ 0) (hc2 : c₂ ≠ 0) (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N 0 1 k * F k)
    (S₁ S₂ : SummableFamily ℤ ℂ ℤ) (hS₁ : ∀ k, S₁ k = (mono β₁ c₁) ^ k * F k)
    (hS₂ : ∀ k, S₂ k = (mono β₂ c₂) ^ k * F k) (e₁ : hs S₁ = 0) (e₂ : hs S₂ = 0) : ∀ k, F k = 0 := by
  have d₁ := ev_decomp hN 0 one_ne_zero F hF β₁ hc1 S₁ hS₁
  have d₂ := ev_decomp hN 0 one_ne_zero F hF β₂ hc2 S₂ hS₂
  rw [e₁, hs_e0Fam, hs_e1Fam] at d₁
  rw [e₂, hs_e0Fam, hs_e1Fam] at d₂
  have hΔ := det_x1 hN h1 h12 h2 (c₂ := c₂) hc1
  set P := hs (e0M hN 0 1 β₁ c₁); set Q := hs (e1M hN 0 1 β₁ c₁)
  set R := hs (e0M hN 0 1 β₂ c₂); set S := hs (e1M hN 0 1 β₂ c₂)
  have f0 : F 0 * (P * S - R * Q) = 0 := by linear_combination (-S) * d₁ + Q * d₂
  have f1 : F 1 * (P * S - R * Q) = 0 := by linear_combination R * d₁ - P * d₂
  have z0 := (mul_eq_zero.mp f0).resolve_right hΔ
  have z1 := (mul_eq_zero.mp f1).resolve_right hΔ
  intro k
  rw [sol_basis one_ne_zero F hF k, z0, z1]; ring


/-- `θ(w X) θ(X/w)` evaluated at `p`. -/
noncomputable def wFam (bw : ℤ) (cw : ℂ) (β : ℤ) (cp : ℂ) : SummableFamily ℤ ℂ ℤ := ttEv hN bw cw (-bw) cw⁻¹ β cp

/-- **Weierstrass' three-term relation** (points `y, u, v, x` monomials; `0 < val u < val v < N/2`). -/
theorem weierstrass {by' bu bv bx : ℤ} {cy cu cv cx : ℂ} (hcy : cy ≠ 0) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hcx : cx ≠ 0) (h1 : 0 < bu) (h12 : bu < bv) (h2 : 2 * bv < N) :
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
  have hall := sol_vanish_x1 hN h1 h12 h2 hcu hcv F hF (Fv bu cu) (Fv bv cv) (hFv bu cu hcu) (hFv bv cv hcv) zu zv
  have zx := ev_decomp hN 0 one_ne_zero F hF bx hcx (Fv bx cx) (hFv bx cx hcx)
  rw [hall 0, hall 1, zero_mul, zero_mul, add_zero, hsum] at zx
  simp only [c1, c2, c3] at zx
  rw [show by' + bx = bx + by' by ring, show cy * cx = cx * cy by ring, show -by' + bx = bx - by' by ring,
    show cy⁻¹ * cx = cx * cy⁻¹ by ring, show bv + bx = bx + bv by ring, show cv * cx = cx * cv by ring,
    show -bv + bx = bx - bv by ring, show cv⁻¹ * cx = cx * cv⁻¹ by ring, show bu + bx = bx + bu by ring,
    show cu * cx = cx * cu by ring, show -bu + bx = bx - bu by ring, show cu⁻¹ * cx = cx * cu⁻¹ by ring] at zx
  linear_combination zx

end Engine


section IdT

lemma h7 : (1 : ℕ) ≤ 7 := by norm_num

/-- `θ_k := θ(q^k; q⁷) = J_{7,k}`. -/
noncomputable abbrev th7 (k : ℤ) : L := θ h7 k 1

lemma th7_neg (k : ℤ) : th7 (-k) = -mono (-k) 1 * th7 k := by
  have := θ_inv h7 k (one_ne_zero (α := ℂ)); rwa [inv_one] at this

lemma th7_refl (k : ℤ) : th7 (7 - k) = th7 k := by
  have := θ_reflect h7 k (one_ne_zero (α := ℂ)); rwa [inv_one] at this

/-- **Identity T** (Atkin–Swinnerton-Dyer), from the Weierstrass relation:
`J_{7,2}³ J_{7,3} = J_{7,1} J_{7,3}³ + q J_{7,1}³ J_{7,2}`. -/
theorem identity_T_theta : th7 2 ^ 3 * th7 3 = th7 1 * th7 3 ^ 3 + mono 1 1 * th7 1 ^ 3 * th7 2 := by
  have W := weierstrass h7 (by' := -4) (bu := 1) (bv := 2) (bx := 0) (cy := 1) (cu := 1) (cv := 1) (cx := 1)
    one_ne_zero one_ne_zero one_ne_zero one_ne_zero (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one, inv_one] at W
  norm_num at W
  have a4 : th7 4 = th7 3 := by rw [show (4 : ℤ) = 7 - 3 by norm_num, th7_refl]
  have a5 : th7 5 = th7 2 := by rw [show (5 : ℤ) = 7 - 2 by norm_num, th7_refl]
  have a6 : th7 6 = th7 1 := by rw [show (6 : ℤ) = 7 - 1 by norm_num, th7_refl]
  have n1 := th7_neg 1; have n2 := th7_neg 2; have n3 := th7_neg 3; have n4 := th7_neg 4; have n6 := th7_neg 6
  simp only [th7] at n1 n2 n3 n4 n6 a4 a5 a6 ⊢
  rw [n1, n2, n3, n4, n6, a4, a5, a6] at W
  have m1 : mono (-4) (1 : ℂ) * mono (-1) 1 = mono (-5) 1 := by rw [mono_mul]; norm_num
  have m2 : mono (-2) (1 : ℂ) * mono (-3) 1 = mono (-5) 1 := by rw [mono_mul]; norm_num
  have m3 : mono 5 (1 : ℂ) * mono (-2) 1 * mono (-6) 1 * mono (-1) 1 = mono (-4) 1 := by
    rw [mono_mul, mono_mul, mono_mul]; norm_num
  have m4 : mono (-5) (1 : ℂ) * mono 1 1 = mono (-4) 1 := by rw [mono_mul]; norm_num
  have hu : mono (-5) (1 : ℂ) ≠ 0 := by simp [mono]
  have key : mono (-5) (1 : ℂ) * (θ h7 2 1 ^ 3 * θ h7 3 1 - (θ h7 1 1 * θ h7 3 1 ^ 3 + mono 1 1 * θ h7 1 1 ^ 3 * θ h7 2 1)) = 0 := by
    linear_combination (-1 : L) * W + (θ h7 1 1 * θ h7 3 1 ^ 3) * m1 - (θ h7 2 1 ^ 3 * θ h7 3 1) * m2
      + (θ h7 1 1 ^ 3 * θ h7 2 1) * (m3 - m4)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu)

end IdT

end ALz
