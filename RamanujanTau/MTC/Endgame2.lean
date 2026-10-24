/-
# The MTC₀ endgame, part 2: the unknown Appell–Lerch values cancel

`endgame_reduce`: with `X = ιN((q;q)_∞ f₀)` at `q = Q`, `Φ' = ιN(1 + φ)` at `q = Q²`, `J₁ = j(Q²;Q³)`,

  `J̄₀ (X + 2 J₁ (Φ' − 1)) = 2 J₁ J³ Q⁻² j̄₆ j₁₀/(j₂ j₁₂ j₈) + κ₄₀ (2 j(Q³;Q¹²) S)`.
-/
import RamanujanTau.MTC.Endgame1
import RamanujanTau.MTC.ProdCalc

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-- the bracket `S` of `thV_xstar`. -/
noncomputable def Sx : L :=
  mono (-168) 1 * jA 18 / (jB 6 * jB 16) + jA 2 / (jB 4 * jB 6) -
    mono 840 1 * jA 2 / (jB 14 * jB 16) - mono (-336) 1 * jA 18 / (jB 14 * jB 4)

/-- **HM Theorem 0.3 at the MTC₀ point, assembled** (E1, E2, E3, `κ = (q;q)³`). -/
theorem main_x : jb30 0 * ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0) =
    2 * θ h504 336 1 * (Av (h120 hqT) 2352 1 0 (-1) + mono (-336) 1 * Av (h120 hqT) 672 1 0 (-1)) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * Sx) := by
  have h := hm03_xstar
  rw [fS_xstar, gNum_xstar, thV_xstar, kap_eq] at h
  unfold Jb at h
  unfold jb30 Sx
  rw [show (168 : ℤ) * 0 = 0 by norm_num]
  exact h

/-- `(Q¹⁰;Q¹⁰)_∞ = j(Q¹⁰;Q³⁰)`. -/
theorem P0 : ιN h336 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) = j30 10 := by
  have h := θ_eq_ιN_prod (d := 336) (a := 15) (b := 5) h336 (by norm_num) (by norm_num) (by norm_num)
  have e : RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf =
      RankProof.Pinf 5 15 * RankProof.Pinf (15 - 5) 15 * RankProof.Pinf 15 15 := by
    rw [← RankProof.Pinf_one_one, RankProof.Ea_Pinf 5 1 1 _ le_rfl le_rfl, Pinf_splitk 5 5 3 (by norm_num)
      (by norm_num) (by norm_num)]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    first | done | norm_num
  rw [e, ← h]
  unfold j30
  rw [θ_N' (by norm_num) _ (h120 hqT)]
  first | done | norm_num

lemma hS1 :
    Av (h120 hqT) 2352 1 0 (-1) + (Qm ^ 2)⁻¹ * Av (h120 hqT) 672 1 0 (-1) =
      jb30 0 / j30 4 * (Av (h120 hqT) 2352 1 672 1 + (Qm ^ 2)⁻¹ * Av (h120 hqT) 672 1 672 1) +
        (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * ((Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8)) := by
  have h1 := I1
  have h3 := I3
  rw [mQ 4 672 (by norm_num)] at h1 h3
  have hA := LemA
  have h4 := j30_ne 4 (by norm_num); have h8 := j30_ne 8 (by norm_num); have h18 := j30_ne 18 (by norm_num)
  have hb4 := jb30_ne 4; have hb14 := jb30_ne 14
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set A1 := Av (h120 hqT) 2352 1 0 (-1)
  set A2 := Av (h120 hqT) 672 1 0 (-1)
  set A3 := Av (h120 hqT) 2352 1 672 1
  set A4 := Av (h120 hqT) 672 1 672 1
  have e1 : A1 = jb30 0 * A3 / j30 4 + Qm ^ 4 * J ^ 3 * jb30 (-4) * jb30 18 / (j30 4 * j30 18 * jb30 14) := by
    have key : A1 - (jb30 0 * A3 / j30 4 + Qm ^ 4 * J ^ 3 * jb30 (-4) * jb30 18 / (j30 4 * j30 18 * jb30 14)) =
        (j30 4 * j30 18 * jb30 14 * A1 - A3 * j30 18 * jb30 0 * jb30 14 +
          Qm ^ 4 * -J ^ 3 * jb30 (-4) * jb30 18) / (j30 4 * j30 18 * jb30 14) := by
      field_simp; ring
    rw [h1, zero_div] at key
    exact sub_eq_zero.mp key
  have e3 : A2 = jb30 0 * A4 / j30 4 + Qm ^ 4 * J ^ 3 * jb30 (-4) * jb30 8 / (j30 4 * j30 8 * jb30 4) := by
    have key : A2 - (jb30 0 * A4 / j30 4 + Qm ^ 4 * J ^ 3 * jb30 (-4) * jb30 8 / (j30 4 * j30 8 * jb30 4)) =
        (j30 4 * j30 8 * jb30 4 * A2 - A4 * j30 8 * jb30 0 * jb30 4 +
          Qm ^ 4 * -J ^ 3 * jb30 (-4) * jb30 8) / (j30 4 * j30 8 * jb30 4) := by
      field_simp; ring
    rw [h3, zero_div] at key
    exact sub_eq_zero.mp key
  rw [e1, e3]
  linear_combination J ^ 3 * hA

lemma hS2 :
    ιN h336 (RankProof.Phi 1) - 1 +
      (Av (h120 hqT) 2352 1 672 1 + (Qm ^ 2)⁻¹ * Av (h120 hqT) 672 1 672 1) / j30 4 = 0 := by
  have hP := hΦ
  rw [P0, j30_refl 20 10 (by norm_num), mQ 20 3360 (by norm_num), m336, mQ 4 672 (by norm_num)] at hP
  have h2 := I2
  have h4' := I4
  rw [mQ 4 672 (by norm_num)] at h2 h4'
  have hB := LemB
  have h4 := j30_ne 4 (by norm_num); have h6 := j30_ne 6 (by norm_num); have h8 := j30_ne 8 (by norm_num)
  have h10 := j30_ne 10 (by norm_num); have h18 := j30_ne 18 (by norm_num)
  have hm6 : j30 (-6) ≠ 0 := j30_ne (-6) (by norm_num)
  have hQ := Qm_ne
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set Φ' := ιN h336 (RankProof.Phi 1)
  set A3 := Av (h120 hqT) 2352 1 672 1
  set A4 := Av (h120 hqT) 672 1 672 1
  set A5 := Av (h120 hqT) 2352 1 (-3360) 1
  set A6 := Av (h120 hqT) 672 1 (-1680) 1
  have key : j30 10 * (Φ' - 1 + (A3 + (Qm ^ 2)⁻¹ * A4) / j30 4) =
      (Φ' * j30 10 - (j30 10 + Qm ^ 20 * A5 + Qm ^ 2 * J ^ 3 / j30 6 + (Qm ^ 2) ^ 2 * (Qm ^ 4 * A6))) +
      Qm ^ 20 * (j30 4 * j30 18 * j30 (-6) * A5 - A3 * j30 18 * j30 (-20) * j30 (-6) +
        Qm ^ 4 * -J ^ 3 * j30 (-24) * j30 (-2)) / (j30 4 * j30 18 * j30 (-6)) +
      Qm ^ 8 * (j30 4 * j30 8 * j30 (-6) * A6 - A4 * j30 8 * j30 (-10) * j30 (-6) +
        Qm ^ 4 * -J ^ 3 * j30 (-14) * j30 (-2)) / (j30 4 * j30 8 * j30 (-6)) +
      J ^ 3 * (Qm ^ 24 * j30 (-24) * j30 (-2) / (j30 4 * j30 18 * j30 (-6)) + Qm ^ 2 / j30 6 +
        Qm ^ 12 * j30 (-14) * j30 (-2) / (j30 4 * j30 8 * j30 (-6))) := by
    rw [show (-20 : ℤ) = -((20 : ℕ) : ℤ) by norm_num, j30_neg, show (((20 : ℕ) : ℤ)) = 20 by norm_num,
      j30_refl 20 10 (by norm_num), show (-10 : ℤ) = -((10 : ℕ) : ℤ) by norm_num, j30_neg,
      show (((10 : ℕ) : ℤ)) = 10 by norm_num]
    field_simp
    ring
  rw [sub_eq_zero.mpr hP, h2, h4', hB] at key
  simp only [add_zero, mul_zero, zero_div] at key
  exact (mul_eq_zero.mp key).resolve_left h10

/-- **the reduction**: `A(Q¹⁴,Q⁴)`, `A(Q⁴,Q⁴)` cancel. -/
theorem endgame_reduce :
    jb30 0 * (ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0) +
        2 * θ h504 336 1 * (ιN h336 (RankProof.Phi 1) - 1)) =
      2 * θ h504 336 1 * ((ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 *
        ((Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8))) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * Sx) := by
  have hM := main_x
  rw [mneg336] at hM
  have h1 := hS1
  have h2 := hS2
  linear_combination hM + 2 * θ h504 336 1 * h1 + 2 * θ h504 336 1 * jb30 0 * h2

end MTC
