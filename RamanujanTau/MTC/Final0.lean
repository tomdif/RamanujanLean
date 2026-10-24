/-
# MTC₀ from HM (8.17)

`LemC_of`: given (8.17) `J̄_{5,20} J̄_{6,30} − Q² J̄_{1,5} J̄_{30,120} = J_{2,20} J_{3,12}`, the theta side of
`endgame_reduce` equals `J̄₀ J_{5,10} J_{2,5}`; with `endgame_reduce` and `ιN` injectivity this is the first mock
theta conjecture in `ℤ⟦q⟧` (`mtc0_of`):

  `(q;q)_∞ f₀(q) + 2 (q;q)_∞ φ(q²) = J_{5,10} J_{2,5}`.
-/
import RamanujanTau.MTC.LemC

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

lemma h20160 : 1 ≤ 20160 := by norm_num

/-- `j(−1; q) = 2 j(−q; q⁴)`. -/
lemma θbar0 {N : ℕ} (h : 1 ≤ N) : θ h 0 (-1) = 2 * θ (hN' h 2 two_pos) N (-1) := by
  have hdis := dissect2 h 0 (by norm_num : (-1 : ℂ) ≠ 0)
  simp only [mul_zero, add_zero, zero_sub, sub_zero, show ((-1 : ℂ)) ^ 2 = 1 by norm_num,
    show -((-1 : ℂ))⁻¹ = 1 by norm_num] at hdis
  rw [inv_m'] at hdis
  have hmm : (mono N 1 : L) * -mono (-(N : ℤ)) (-1) = 1 := by
    rw [show -(mono (-(N : ℤ)) (-1) : L) = mono (-(N : ℤ)) 1 by simp [mono], mono_mul,
      show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  rw [show (mono 0 1 : L) = 1 from rfl, one_mul] at hdis
  rw [hdis]
  linear_combination θ (hN' h 2 two_pos) N (-1) * hmm

/-- HM (8.17), as a proposition. -/
def E817 : Prop :=
  B20 5 * jb30 6 - mono 336 1 * θ h840 168 (-1) * θ h20160 5040 (-1) = J20 2 * j12 3

theorem LemC_of (h817 : E817) :
    2 * θ h504 336 1 * ((ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 *
        ((Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8))) +
      (ιN (h160 hqT) MockTheta5.JTP.qfacInf) ^ 3 * (2 * j12 3 * Sx) =
      jb30 0 * ιN h168 (Jp 5 10 * Jp 2 5) := by
  have hS := S_prod
  have p1 := PI1
  have p2 := PI2
  unfold E817 at h817
  have hj0 : jb30 0 = 2 * θ h20160 5040 (-1) := by
    unfold jb30
    rw [show (168 : ℤ) * 0 = 0 by norm_num, θbar0, θ_N' (by norm_num) _ h20160]
    norm_num
  have hB : B20 5 ≠ 0 := by
    unfold B20; exact θ_ne_zero h3360 (by norm_num) fun _ _ => by norm_num
  have hb : ∀ a : ℤ, jB a ≠ 0 := fun a => by
    unfold jB; exact θ_ne_zero (h160 hqT) (by norm_num) fun _ _ => by norm_num
  have hA20 : jA 20 ≠ 0 := by
    unfold jA
    refine θ_ne_zero (h160 hqT) one_ne_zero fun m hm => ?_
    exfalso
    have : (168 : ℤ) * 20 = 160 * 42 * m := by rw [hm]; push_cast; ring
    omega
  have h2 := j30_ne 2 (by norm_num); have h8 := j30_ne 8 (by norm_num); have h12 := j30_ne 12 (by norm_num)
  have hQ := Qm_ne
  have hb4 := hb 4; have hb6 := hb 6; have hb14 := hb 14; have hb16 := hb 16
  rw [m336] at hS h817
  have e1 : jb30 6 = (J20 2 * j12 3 + Qm ^ 2 * θ h840 168 (-1) * θ h20160 5040 (-1)) / B20 5 := by
    rw [eq_div_iff hB]; linear_combination h817
  have eS : Sx = -(J20 5 * J20 1 * J20 9 * J5 2) / (Qm ^ 2 * (jB 4 * jB 6 * jB 14 * jB 16) * jA 20) := by
    have hden : Qm ^ 2 * (jB 4 * jB 6 * jB 14 * jB 16) * jA 20 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hQ) (mul_ne_zero (mul_ne_zero (mul_ne_zero (hb 4) (hb 6)) (hb 14))
        (hb 16))) hA20
    rw [eq_div_iff hden]; unfold Sx; exact hS
  set J1 := θ h504 336 1
  set J := ιN (h120 hqT) MockTheta5.JTP.qfacInf
  set κ := ιN (h160 hqT) MockTheta5.JTP.qfacInf
  set Jt := ιN h168 (Jp 5 10 * Jp 2 5)
  set X1 := θ h840 168 (-1)
  set X2 := θ h20160 5040 (-1)
  have key : 2 * J1 * (J ^ 3 * ((Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8))) +
      κ ^ 3 * (2 * j12 3 * Sx) - jb30 0 * Jt =
      2 * X2 / (j30 2 * j30 12 * j30 8 * B20 5) * (J1 * J ^ 3 * j30 10 * X1 - Jt * j30 2 * j30 12 * j30 8 * B20 5) +
      2 * (Qm ^ 2)⁻¹ * j12 3 / (j30 2 * j30 12 * j30 8 * B20 5 * (jB 4 * jB 6 * jB 14 * jB 16) * jA 20) *
        (J1 * J ^ 3 * j30 10 * J20 2 * jB 4 * jB 6 * jB 14 * jB 16 * jA 20 -
          κ ^ 3 * J20 5 * J20 1 * J20 9 * J5 2 * j30 2 * j30 12 * j30 8 * B20 5) := by
    rw [e1, eS, hj0]
    field_simp
    ring
  rw [sub_eq_zero.mpr p1, sub_eq_zero.mpr p2, mul_zero, mul_zero, add_zero] at key
  exact sub_eq_zero.mp key

lemma ιN_injective {N : ℕ} (hN : 1 ≤ N) : Function.Injective (ιN hN) := fun f g h => by
  ext k
  have := congrArg (fun F : L => F.coeff ((N * k : ℕ) : ℤ)) h
  simp only [ιN_coeff_nat, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (show 0 < N by omega)] at this
  exact_mod_cast this

lemma J1_eq : θ h504 336 1 = ιN h168 MockTheta5.JTP.qfacInf := by
  rw [θu h168 h504 3 2 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) le_rfl, ← Pinf_one_one,
    ιN_Pinf_split h168 1 1 3 le_rfl le_rfl (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul, mul_zero, add_zero, mul_one, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul]
  ring

/-- **the first mock theta conjecture, multiplied out**, given (8.17). -/
theorem mtc0_of (h817 : E817) :
    MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0 +
        2 * MockTheta5.JTP.qfacInf * (Ea 2 two_ne_zero (Phi 1) - 1) = Jp 5 10 * Jp 2 5 := by
  have hR := endgame_reduce
  rw [LemC_of h817] at hR
  have h0 : jb30 0 ≠ 0 := jb30_ne 0
  have hL := mul_left_cancel₀ h0 hR
  apply ιN_injective h168
  rw [← hL, J1_eq, ιN_Ea h168 two_ne_zero h336 (Phi 1)]
  simp only [map_add, map_mul, map_sub, map_one, map_ofNat]

end MTC
