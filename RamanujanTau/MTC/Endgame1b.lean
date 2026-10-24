/-
# The MTC₁ endgame: reduction to a single theta identity

As for MTC₀ (`Endgame1`, `Endgame2`), now at `x₁ = Z²¹t^{189}` and with `z₀ = Q²`:

* `main_x1`: `J̄₀ (Q;Q)_∞ f₁ = 2J₁(Q⁻³A(Q²,−1) + Q⁻⁹A(Q⁻⁸,−1)) + κ₄₀ (2 j(Q³;Q¹²) S₁)`;
* `hΨ`: `(1 + ψ(Q²))(Q¹⁰;Q¹⁰)_∞ = −Q¹⁰ A(Q²²,Q⁻¹⁰) + Q⁴ J³/j₁₂ − Q⁻² A(Q², Q¹⁰)`;
* four changes of `z` to `z₀ = Q²` (`K1`–`K4`), `LemA1`, `LemB1`;

and the unknown values `A(Q²²,Q²)`, `A(Q²,Q²)` cancel:

  `J̄₀ ((Q;Q)_∞ f₁ + 2J₁ Q⁻¹ ψ(Q²)) = 2J₁ J³ Q⁻³ j̄₁₂ j₁₀/(j₄j₆j₁₄) + κ₄₀ (2 j(Q³;Q¹²) S₁)`  (`endgame_reduce₁`).
-/
import RamanujanTau.MTC.Endgame2
import RamanujanTau.MTC.ThetaLem1
import RamanujanTau.MTC.ThetaY1
import RamanujanTau.MTC.GX1
import RamanujanTau.MTC.Hecke1
import RamanujanTau.MTC.Zeros1
import RamanujanTau.MTC.L5b

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-- the bracket `S₁` of `thV_x1`. -/
noncomputable def S1x : L :=
  jA 14 / (jB 18 * jB 8) + mono (-336) 1 * jA 6 / (jB 2 * jB 8) -
    mono 504 1 * jA 6 / (jB 12 * jB 18) - mono (-504) 1 * jA 14 / (jB 12 * jB 2)

theorem main_x1 : jb30 0 * ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f1) =
    2 * θ h504 336 1 * (mono (-504) 1 * Av (h120 hqT) 336 1 0 (-1) + mono (-1512) 1 * Av (h120 hqT) (-1344) 1 0 (-1)) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * S1x) := by
  have h := hm03_x1
  rw [fS_xstar₁, gNum_x1, thV_x1, kap_eq] at h
  unfold Jb at h
  unfold jb30 S1x
  rw [show (168 : ℤ) * 0 = 0 by norm_num]
  exact h

/-! ## The four changes of `z` (`z₀ = Q²`) -/

lemma K1 : j30 2 * j30 24 * jb30 22 * Av (h120 hqT) 3696 1 0 (-1) -
    Av (h120 hqT) 3696 1 336 1 * j30 24 * jb30 0 * jb30 22 +
    mono 336 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * jb30 (-2) * jb30 24 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 3696) (b₀ := 336) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := -1)
    one_ne_zero one_ne_zero (by norm_num) (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero (by norm_num) (lamOK_cm 3696 0),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 3696 336 (by intro m; omega))] at h
  unfold j30 jb30
  norm_num at h ⊢
  linear_combination h

lemma K2 : j30 2 * j30 24 * j30 12 * Av (h120 hqT) 3696 1 (-1680) 1 -
    Av (h120 hqT) 3696 1 336 1 * j30 24 * j30 (-10) * j30 12 +
    mono 336 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 (-12) * j30 14 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 3696) (b₀ := 336) (b₁ := -1680) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := 1)
    one_ne_zero one_ne_zero one_ne_zero (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 3696 (-1680) (by intro m; omega)),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 3696 336 (by intro m; omega))] at h
  unfold j30
  norm_num at h ⊢
  linear_combination h

lemma K3 : j30 2 * j30 4 * jb30 2 * Av (h120 hqT) 336 1 0 (-1) -
    Av (h120 hqT) 336 1 336 1 * j30 4 * jb30 0 * jb30 2 +
    mono 336 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * jb30 (-2) * jb30 4 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 336) (b₀ := 336) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := -1)
    one_ne_zero one_ne_zero (by norm_num) (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero (by norm_num) (lamOK_cm 336 0),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 336 336 (by intro m; omega))] at h
  unfold j30 jb30
  norm_num at h ⊢
  linear_combination h

lemma K4 : j30 2 * j30 4 * j30 12 * Av (h120 hqT) 336 1 1680 1 -
    Av (h120 hqT) 336 1 336 1 * j30 4 * j30 10 * j30 12 +
    mono 336 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 8 * j30 14 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 336) (b₀ := 336) (b₁ := 1680) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := 1)
    one_ne_zero one_ne_zero one_ne_zero (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 336 1680 (by intro m; omega)),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 336 336 (by intro m; omega))] at h
  unfold j30
  norm_num at h ⊢
  linear_combination h

/-! ## `ψ` at `q = Q²` -/

lemma hs_LF₂ (b : ℤ) : hs (LF₂ h336 b) = Av (h120 hqT) ((21 - b) * ((336 : ℕ) : ℤ)) 1 (b * ((336 : ℕ) : ℤ)) 1 := by
  rw [← Av_N (h15 h336) (by norm_num) (h120 hqT), Av_eq_Alam (h15 h336) one_ne_zero one_ne_zero (lamOK21 h336 b)]
  rfl

lemma hB10 : Av (h120 hqT) 3696 1 3360 1 = -(mono 1680 1 * Av (h120 hqT) 3696 1 (-1680) 1) := by
  have z := Av_zshift' (h120 hqT) (ex := 3696) (ez := -1680) one_ne_zero one_ne_zero
    (lamOK_c1 3696 (-1680) (by intro m; omega))
  rw [show (-1680 : ℤ) + ((120 * 42 : ℕ) : ℤ) = 3360 by norm_num] at z
  have e : (mono 1680 1 : L) * mono (-1680) 1 = 1 := by
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]; exact mono_ext (by norm_num) (by norm_num)
  linear_combination (mono 1680 1 : L) * z - Av (h120 hqT) 3696 1 3360 1 * e

lemma hB15 : j30 12 * Av (h120 hqT) 2016 1 5040 1 = (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 := by
  have z := Av_zshift' (h120 hqT) (ex := 2016) (ez := 0) one_ne_zero one_ne_zero (lamOK_c1 2016 0 (by intro m; omega))
  have k := kappa_eq_jacobi (h120 hqT) (a := 2016) (by norm_num) (by norm_num) (cx := 1) one_ne_zero
    (mono_ne_one (by norm_num))
  rw [← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 2016 0 (by intro m; omega))] at k
  rw [show (mono 0 1 : L) = 1 from rfl] at z
  norm_num at z
  unfold j30
  norm_num
  linear_combination -k + θ (h120 hqT) 2016 1 * z

lemma hB20 : Av (h120 hqT) 336 1 6720 1 = -(mono (-1680) 1 * Av (h120 hqT) 336 1 1680 1) := by
  have z := Av_zshift' (h120 hqT) (ex := 336) (ez := 1680) one_ne_zero one_ne_zero
    (lamOK_c1 336 1680 (by intro m; omega))
  rw [show (1680 : ℤ) + ((120 * 42 : ℕ) : ℤ) = 6720 by norm_num] at z
  have e : (mono (-1680) 1 : L) * mono 1680 1 = 1 := by
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]; exact mono_ext (by norm_num) (by norm_num)
  linear_combination (mono (-1680) 1 : L) * z - Av (h120 hqT) 336 1 6720 1 * e

theorem hΨ : ιN h336 (RankProof.Phi 2) * ιN h336 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) =
    -(mono 1680 1 * Av (h120 hqT) 3696 1 (-1680) 1) +
      mono 336 1 ^ 2 * ((ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 / j30 12) +
      mono 336 1 ^ 4 * -(mono (-1680) 1 * Av (h120 hqT) 336 1 1680 1) := by
  have h := L5_lam₂ h336
  rw [hs_LF₂, hs_LF₂, hs_LF₂] at h
  simp only [Nat.cast_ofNat] at h
  rw [show ((21 : ℤ) - 10) * 336 = 3696 by norm_num, show (10 : ℤ) * 336 = 3360 by norm_num,
    show ((21 : ℤ) - 15) * 336 = 2016 by norm_num, show (15 : ℤ) * 336 = 5040 by norm_num,
    show ((21 : ℤ) - 20) * 336 = 336 by norm_num, show (20 : ℤ) * 336 = 6720 by norm_num] at h
  have h12 := j30_ne 12 (by norm_num)
  have hv : Av (h120 hqT) 2016 1 5040 1 = (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 / j30 12 := by
    rw [eq_div_iff h12, mul_comm]; exact hB15
  rw [h, hB10, hB20, hv]

/-! ## The cancellation -/

lemma hT1 :
    mono (-504) 1 * Av (h120 hqT) 336 1 0 (-1) + mono (-1512) 1 * Av (h120 hqT) (-1344) 1 0 (-1) =
      jb30 0 / j30 2 * ((Qm ^ 3)⁻¹ * Av (h120 hqT) 336 1 336 1 - Qm⁻¹ * Av (h120 hqT) 3696 1 336 1) + Qm⁻¹ * jb30 0 +
        (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * ((Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14)) := by
  have q := Av_qshift (h120 hqT) (ex := -1344) (cx := 1) (ez := 0) (cz := -1) one_ne_zero (by norm_num)
    (lamOK_cm _ _)
  rw [show (-1344 : ℤ) + ((120 * 42 : ℕ) : ℤ) = 3696 by norm_num] at q
  have k1 := K1
  have k3 := K3
  rw [mQ 2 336 (by norm_num)] at k1 k3
  have hA := LemA1
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h24 := j30_ne 24 (by norm_num)
  have hb2 := jb30_ne 2; have hb22 := jb30_ne 22
  have hQ := Qm_ne
  rw [mQn 3 (-504) (by norm_num), mQn 9 (-1512) (by norm_num)]
  rw [mQn 8 (-1344) (by norm_num)] at q
  have hJb : θ (h120 hqT) 0 (-1) = jb30 0 := by unfold jb30; norm_num
  rw [hJb] at q
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set A1 := Av (h120 hqT) 336 1 0 (-1)
  set A2 := Av (h120 hqT) (-1344) 1 0 (-1)
  set A3 := Av (h120 hqT) 3696 1 0 (-1)
  set A4 := Av (h120 hqT) 336 1 336 1
  set A5 := Av (h120 hqT) 3696 1 336 1
  have e3 : A3 = jb30 0 * A5 / j30 2 + Qm ^ 2 * J ^ 3 * jb30 (-2) * jb30 24 / (j30 2 * j30 24 * jb30 22) := by
    have key : A3 - (jb30 0 * A5 / j30 2 + Qm ^ 2 * J ^ 3 * jb30 (-2) * jb30 24 / (j30 2 * j30 24 * jb30 22)) =
        (j30 2 * j30 24 * jb30 22 * A3 - A5 * j30 24 * jb30 0 * jb30 22 + Qm ^ 2 * -J ^ 3 * jb30 (-2) * jb30 24) /
          (j30 2 * j30 24 * jb30 22) := by
      field_simp; ring
    rw [k1, zero_div] at key
    exact sub_eq_zero.mp key
  have e1 : A1 = jb30 0 * A4 / j30 2 + Qm ^ 2 * J ^ 3 * jb30 (-2) * jb30 4 / (j30 2 * j30 4 * jb30 2) := by
    have key : A1 - (jb30 0 * A4 / j30 2 + Qm ^ 2 * J ^ 3 * jb30 (-2) * jb30 4 / (j30 2 * j30 4 * jb30 2)) =
        (j30 2 * j30 4 * jb30 2 * A1 - A4 * j30 4 * jb30 0 * jb30 2 + Qm ^ 2 * -J ^ 3 * jb30 (-2) * jb30 4) /
          (j30 2 * j30 4 * jb30 2) := by
      field_simp; ring
    rw [k3, zero_div] at key
    exact sub_eq_zero.mp key
  have e2 : A2 = Qm ^ 8 * (jb30 0 - A3) := by
    have hq8 : (Qm ^ 8)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 8 hQ)
    field_simp at q ⊢
    linear_combination q
  rw [e2, e3, e1, ← hA]
  field_simp
  ring

lemma hT2 :
    ιN h336 (RankProof.Phi 2) - (Av (h120 hqT) 3696 1 336 1 - (Qm ^ 2)⁻¹ * Av (h120 hqT) 336 1 336 1) / j30 2 = 0 := by
  have hP := hΨ
  rw [P0, mQ 10 1680 (by norm_num), mQn 10 (-1680) (by norm_num), m336] at hP
  have k2 := K2
  have k4 := K4
  rw [mQ 2 336 (by norm_num)] at k2 k4
  have hB := LemB1
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h10 := j30_ne 10 (by norm_num)
  have h12 := j30_ne 12 (by norm_num); have h24 := j30_ne 24 (by norm_num)
  have hQ := Qm_ne
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set Ψ' := ιN h336 (RankProof.Phi 2)
  set A4 := Av (h120 hqT) 336 1 336 1
  set A5 := Av (h120 hqT) 3696 1 336 1
  set A6 := Av (h120 hqT) 3696 1 (-1680) 1
  set A7 := Av (h120 hqT) 336 1 1680 1
  have key : j30 10 * (Ψ' - (A5 - (Qm ^ 2)⁻¹ * A4) / j30 2) =
      (Ψ' * j30 10 - (-(Qm ^ 10 * A6) + (Qm ^ 2) ^ 2 * (J ^ 3 / j30 12) + (Qm ^ 2) ^ 4 * -((Qm ^ 10)⁻¹ * A7))) -
      Qm ^ 10 * (j30 2 * j30 24 * j30 12 * A6 - A5 * j30 24 * j30 (-10) * j30 12 +
        Qm ^ 2 * -J ^ 3 * j30 (-12) * j30 14) / (j30 2 * j30 24 * j30 12) -
      (Qm ^ 2) ^ 4 * (Qm ^ 10)⁻¹ * (j30 2 * j30 4 * j30 12 * A7 - A4 * j30 4 * j30 10 * j30 12 +
        Qm ^ 2 * -J ^ 3 * j30 8 * j30 14) / (j30 2 * j30 4 * j30 12) +
      J ^ 3 * (-(Qm ^ 12 * j30 (-12) * j30 14 / (j30 2 * j30 24 * j30 12)) + Qm ^ 4 / j30 12 -
        j30 8 * j30 14 / (j30 2 * j30 4 * j30 12)) := by
    rw [show (-10 : ℤ) = -((10 : ℕ) : ℤ) by norm_num, j30_neg, show (((10 : ℕ) : ℤ)) = 10 by norm_num]
    field_simp
    ring
  rw [sub_eq_zero.mpr hP, k2, k4, hB] at key
  simp only [sub_zero, zero_div, mul_zero, add_zero] at key
  exact (mul_eq_zero.mp key).resolve_left h10

/-- **the reduction for MTC₁**. -/
theorem endgame_reduce₁ :
    jb30 0 * (ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f1) +
        2 * θ h504 336 1 * Qm⁻¹ * (ιN h336 (RankProof.Phi 2) - 1)) =
      2 * θ h504 336 1 * ((ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 *
        ((Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14))) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * S1x) := by
  have hM := main_x1
  have h1 := hT1
  have h2 := hT2
  rw [h1] at hM
  have hQ := Qm_ne
  have hj2 := j30_ne 2 (by norm_num)
  set A4 := Av (h120 hqT) 336 1 336 1
  set A5 := Av (h120 hqT) 3696 1 336 1
  have hs : ιN h336 (RankProof.Phi 2) = (A5 - (Qm ^ 2)⁻¹ * A4) / j30 2 := sub_eq_zero.mp h2
  rw [hs]
  linear_combination hM

end MTC
