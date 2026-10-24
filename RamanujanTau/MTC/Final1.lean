/-
# The second Mock Theta Conjecture (MTC₁)

`f₁(q) = Σ_{n≥0} q^{n²+n}/(−q;q)ₙ` satisfies `f₁(q) = θ₄(0,q⁵)/((q²;q⁵)_∞(q³;q⁵)_∞) − 2q⁻¹Ψ(q²)`
(`mock_theta_conjecture_f1`, multiplied by `q`), where `Ψ(q) = −1 + Σ q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n)` is
`RankProof.Phi 2 − 1`.

The remaining theta identity is HM (8.17) for `f₁`,
`J̄_{5,20} J̄_{12,30} − Q³ J̄_{2,5} J̄_{30,120} = J_{6,20} J_{3,12}`, which is HM (1.9) (`F19_zero`) at `x = Q⁶`,
together with three product identities.
-/
import RamanujanTau.MTC.Endgame1b
import RamanujanTau.MTC.H19b

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

/-- HM (8.17) for `f₁`. -/
def E817₁ : Prop :=
  B20 5 * jb30 12 - mono 504 1 * θ h840 336 (-1) * θ h20160 5040 (-1) = J20 6 * j12 3

/-- `J_{3,15} J_{24,60} = J_{3,12} J̄_{9,30}`. -/
theorem PX₁ : θ h2520 504 1 * θ h10080 4032 1 = j12 3 * θ h5040 1512 (-1) := by
  unfold j12
  rw [θu h168 h2520 15 3 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h10080 60 24 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h48 hqT) 12 3 5 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h5040 30 9 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 60 ≠ 0 := fun r hr => PA_ne h168 r 60 hr (by norm_num)
  field_simp [hP]

theorem E817₁_holds : E817₁ := by
  have h0 : ev F19 1008 1 = 0 := by rw [F19_zero]; exact ev_zero 1008 1
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero] at h0
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (1008 : ℤ) + 1008 = 2016 by norm_num,
    show (3 : ℤ) * 1008 + 504 = ((5040 : ℕ) : ℤ) - 1512 by norm_num, refl_m h5040,
    θ_red h840 (1008 + 168) 336 1 n1 (-336) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h5040 (2 * 1008 + 4536) 1512 1 n1 (-1512) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    show (2 : ℤ) * 1008 + 336 = ((3360 : ℕ) : ℤ) - 1008 by norm_num,
    show (2 : ℤ) * 1008 + 2016 = 4032 by norm_num] at h0
  have r1 : θ h3360 (((3360 : ℕ) : ℤ) - 1008) 1 = θ h3360 1008 1 := by
    have := θ_reflect h3360 1008 one_ne_zero; rwa [inv_one] at this
  have r2 : θ h2520 2016 1 = θ h2520 504 1 := by
    have := θ_reflect h2520 504 one_ne_zero; rw [inv_one] at this
    rw [← this]; norm_num
  rw [r1, r2] at h0
  have hW : θ h5040 1512 (-1) ≠ 0 := θ_ne_zero h5040 (by norm_num) fun _ _ => by norm_num
  unfold E817₁
  have e12 : jb30 12 = θ h5040 2016 (-1) := by unfold jb30; rw [θ_N' (by norm_num) _ h5040]; norm_num
  have e6 : J20 6 = θ h3360 1008 1 := by unfold J20; norm_num
  have em : (mono 336 1 : L) * mono (2 * 1008) 1 * mono (-336) 1 * mono (-1512) 1 = mono 504 1 := by
    simp only [mono_mul]; exact mono_ext_x (by norm_num) (by norm_num)
  rw [e12, e6]
  have hP := PX₁
  apply mul_right_cancel₀ hW
  linear_combination h0 + θ h3360 1008 1 * hP + θ h840 336 (-1) * θ h20160 5040 (-1) * θ h5040 1512 (-1) * em

/-- **PI1₁**: `J₁ J³ j₁₀ J̄_{2,5} = J_{5,10}J_{1,5} j₄j₆j₁₄ J̄_{5,20}`. -/
theorem PI1₁ :
    θ h504 336 1 * (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 10 * θ h840 336 (-1) =
      ιN h168 (Jp 5 10 * Jp 1 5) * j30 4 * j30 6 * j30 14 * B20 5 := by
  unfold j30 B20
  rw [map_mul, Jp_PA 5 10 12 (by norm_num) (by norm_num) (by norm_num), Jp_PA 1 5 24 (by norm_num) (by norm_num) (by norm_num),
    J30_PA 4 (by norm_num),
    θu h168 h504 3 2 40 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h840 5 2 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 10 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 4 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 6 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 14 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h3360 20 5 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 120 ≠ 0 := fun r hr => PA_ne h168 r 120 hr (by norm_num)
  field_simp [hP]

set_option maxHeartbeats 2000000 in
/-- **PI2₁**. -/
theorem PI2₁ :
    θ h504 336 1 * (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 10 * J20 6 * jB 2 * jB 8 * jB 12 * jB 18 *
        jA 20 =
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * J20 3 * J20 5 * J20 7 * J5 1 * j30 4 * j30 6 * j30 14 *
        B20 5 := by
  unfold j30 B20 J20 J5 jA jB
  rw [J30_PA 8 (by norm_num), J40_PA 6 (by norm_num),
    θu h168 h504 3 2 80 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 10 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 4 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 6 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h120 hqT) 30 14 8 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 6 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 3 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 5 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 7 12 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h840 5 1 48 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h160 hqT) 40 20 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 2 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 8 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 12 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 (h160 hqT) 40 18 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h3360 20 5 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 240 ≠ 0 := fun r hr => PA_ne h168 r 240 hr (by norm_num)
  field_simp [hP]

set_option maxHeartbeats 2000000 in
theorem LemC1 :
    2 * θ h504 336 1 * ((ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 *
        ((Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14))) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * S1x) =
      jb30 0 * ιN h168 (Jp 5 10 * Jp 1 5) := by
  have h817 := E817₁_holds
  have hS := S1_prod
  have p1 := PI1₁
  have p2 := PI2₁
  unfold E817₁ at h817
  have hj0 : jb30 0 = 2 * θ h20160 5040 (-1) := by
    unfold jb30
    rw [show (168 : ℤ) * 0 = 0 by norm_num, θbar0, θ_N' (by norm_num) _ h20160]
    norm_num
  have hB : B20 5 ≠ 0 := by
    unfold B20; exact θ_ne_zero h3360 (by norm_num) fun _ _ => by norm_num
  have hb : ∀ a : ℤ, jB a ≠ 0 := fun a => by
    unfold jB; exact θ_ne_zero (h160 hqT) (by norm_num) fun _ _ => by norm_num
  have hb2 := hb 2; have hb8 := hb 8; have hb12 := hb 12; have hb18 := hb 18
  have hA20 : jA 20 ≠ 0 := by
    unfold jA
    refine θ_ne_zero (h160 hqT) one_ne_zero fun m hm => ?_
    exfalso
    have : (168 : ℤ) * 20 = 160 * 42 * m := by rw [hm]; push_cast; ring
    omega
  have h4 := j30_ne 4 (by norm_num); have h6 := j30_ne 6 (by norm_num); have h14 := j30_ne 14 (by norm_num)
  have hQ := Qm_ne
  rw [mQ 3 504 (by norm_num)] at h817
  have e1 : jb30 12 = (J20 6 * j12 3 + Qm ^ 3 * θ h840 336 (-1) * θ h20160 5040 (-1)) / B20 5 := by
    rw [eq_div_iff hB]; linear_combination h817
  have eS : S1x = -((Qm ^ 3)⁻¹ * (J20 3 * J20 5 * J20 7 * J5 1)) / ((jB 2 * jB 8 * jB 12 * jB 18) * jA 20) := by
    have hden : (jB 2 * jB 8 * jB 12 * jB 18) * jA 20 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb2 hb8) hb12) hb18) hA20
    rw [eq_div_iff hden]; unfold S1x; rw [mQn 3 (-504) (by norm_num)] at hS ⊢; exact hS
  set J1 := θ h504 336 1
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set κ := ιN (h160 hqT) MockTheta5.JTP.qfacInf
  set Jt := ιN h168 (Jp 5 10 * Jp 1 5)
  set X1 := θ h840 336 (-1)
  set X2 := θ h20160 5040 (-1)
  have key : 2 * J1 * (J ^ 3 * ((Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14))) +
      κ ^ 3 * (2 * j12 3 * S1x) - jb30 0 * Jt =
      2 * X2 / (j30 4 * j30 6 * j30 14 * B20 5) * (J1 * J ^ 3 * j30 10 * X1 - Jt * j30 4 * j30 6 * j30 14 * B20 5) +
      2 * (Qm ^ 3)⁻¹ * j12 3 / (j30 4 * j30 6 * j30 14 * B20 5 * (jB 2 * jB 8 * jB 12 * jB 18) * jA 20) *
        (J1 * J ^ 3 * j30 10 * J20 6 * jB 2 * jB 8 * jB 12 * jB 18 * jA 20 -
          κ ^ 3 * J20 3 * J20 5 * J20 7 * J5 1 * j30 4 * j30 6 * j30 14 * B20 5) := by
    rw [e1, eS, hj0]
    field_simp
    ring
  rw [sub_eq_zero.mpr p1, sub_eq_zero.mpr p2, mul_zero, mul_zero, add_zero] at key
  exact sub_eq_zero.mp key

/-- **the second mock theta conjecture, multiplied out**:
`q (q;q)_∞ f₁(q) + 2 (q;q)_∞ Ψ(q²) = q J_{5,10} J_{1,5}`. -/
theorem mtc1 :
    PowerSeries.X * MockTheta5.JTP.qfacInf * MockTheta5.JTP.f1 +
        2 * MockTheta5.JTP.qfacInf * (Ea 2 two_ne_zero (Phi 2) - 1) = PowerSeries.X * (Jp 5 10 * Jp 1 5) := by
  have hR := endgame_reduce₁
  rw [LemC1] at hR
  have h0 : jb30 0 ≠ 0 := jb30_ne 0
  have hL := mul_left_cancel₀ h0 hR
  have hQ := Qm_ne
  have hX : ιN h168 PowerSeries.X = Qm := ιN_X h168
  apply ιN_injective h168
  rw [map_mul, ← hL, J1_eq, ιN_Ea h168 two_ne_zero h336 (Phi 2)]
  simp only [map_add, map_mul, map_sub, map_one, map_ofNat, hX]
  field_simp
  first | done | ring

/-- `(q;q)_∞ = J_{1,5} (q²;q⁵)_∞ (q³;q⁵)_∞`. -/
lemma qfacInf_split₁ : MockTheta5.JTP.qfacInf = Jp 1 5 * (Pinf 2 5 * Pinf 3 5) := by
  rw [← Pinf_one_one, Pinf_splitk 1 1 5 le_rfl le_rfl (by norm_num), Jp]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  ring

/-- **The second Mock Theta Conjecture** (Hickerson 1988; Andrews–Garvan form), multiplied by `q`:
`q f₁(q) = q θ₄(0,q⁵)/((q²;q⁵)_∞(q³;q⁵)_∞) − 2 Ψ(q²)`. -/
theorem mock_theta_conjecture_f1 :
    PowerSeries.X * MockTheta5.JTP.f1 =
      PowerSeries.X * (Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 2 5 * Pinf 3 5)) -
        2 * (Ea 2 two_ne_zero (Phi 2) - 1) := by
  have h := mtc1
  have hu : IsUnit (Pinf 2 5 * Pinf 3 5) := (isUnit_Pinf 2 5 (by norm_num) (by norm_num)).mul
    (isUnit_Pinf 3 5 (by norm_num) (by norm_num))
  have hJ : Jp 1 5 ≠ 0 := by
    unfold Jp
    exact ((isUnit_Pinf 1 5 le_rfl (by norm_num)).mul (isUnit_Pinf (5 - 1) 5 (by norm_num) (by norm_num))).mul
      (isUnit_Pinf 5 5 (by norm_num) (by norm_num)) |>.ne_zero
  rw [qfacInf_split₁] at h
  have h2 : (Pinf 2 5 * Pinf 3 5) * (PowerSeries.X * MockTheta5.JTP.f1 + 2 * (Ea 2 two_ne_zero (Phi 2) - 1)) =
      PowerSeries.X * Jp 5 10 := by
    apply mul_left_cancel₀ hJ
    linear_combination h
  have h3 : PowerSeries.X * MockTheta5.JTP.f1 + 2 * (Ea 2 two_ne_zero (Phi 2) - 1) =
      Ring.inverse (Pinf 2 5 * Pinf 3 5) * (PowerSeries.X * Jp 5 10) := by
    rw [← h2, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rw [show Pinf 5 10 * Pinf 5 10 * Pinf 10 10 = Jp 5 10 by unfold Jp; norm_num]
  linear_combination h3

end MTC
