/-
# `CVHyp` proved: `u ↦ −Φ'(u)/(uΦ(u))` is nondecreasing on `(0,∞)` — and the unconditional
# Turán inequalities / degree-2 GORZ hyperbolicity for `Ξ`

`R = −Φ'/(uΦ)` has `R' = G/(uΦ)²` with `G = Φ(Φ' − uΦ'') + uΦ'²` (**`hasDerivAt_ratio`**), and `G > 0` on
`(0,∞)` (**`Gfun_pos`**), from three pieces:

* `0 < u ≤ 737/2^12`: even Taylor model at `0` (`CVRegionB`, cover `CVDataB`, `|Φ^{(10)}| ≤ 8·10⁹` from
  `CVDataM`);
* `737/2^12 ≤ u ≤ 12`: `k = 1` exponential polynomial plus enclosed tails (`CVRegionA`, cover `CVDataA`);
* `u ≥ 12`: an explicit estimate (`QR_pos_large`): the `k = 1` part is `≥ x⁵`, the rest `≤ 5·10¹² x³`.

Hence **`cvHyp_holds : CVHyp`**, and with `turan_gamma`/`jensen2_gamma` (`Main.lean`):
**`turan_gamma_unconditional`** and **`jensen2_gamma_unconditional`**.
-/
import RamanujanTau.GORZXiEff.CVDataA
import RamanujanTau.GORZXiEff.CVDataB
import RamanujanTau.GORZXiEff.CVDataM

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Finset GORZXiEff GORZXi JensenThreshold JensenThreshold.Tail JensenThreshold.Tail.Iv

/-! ## the three regions -/

theorem Phi10_bound : ∀ t, 0 ≤ t → t ≤ (u0B : ℝ) / 2 ^ 12 → -(Mb : ℝ) ≤ Phi 10 t ∧ Phi 10 t ≤ Mb := by
  intro t h0 h1
  have hc := coverM_ok
  rw [ptsM] at hc
  refine cover_sound cellM (fun p q h u h1 h2 => cellM_sound h u h1 h2) _ _ _ hc t (by simpa using h0) ?_
  have : lastZ 11 [17, 23, 34, 40, 46, 57, 63, 69, 80, 92, 103, 115, 126, 138, 149, 161, 172, 184, 195, 207,
    218, 230, 241, 253, 264, 276, 287, 299, 310, 322, 333, 345, 356, 368, 379, 391, 402, 414, 425, 437, 448,
    460, 471, 483, 494, 506, 517, 529, 540, 552, 563, 575, 586, 598, 609, 621, 632, 644, 655, 667, 678, 690,
    701, 713, 725, 737] = u0B := by decide
  rw [this]; exact h1

theorem Gfun_pos_small {u : ℝ} (hu : 0 < u) (hu2 : u ≤ (u0B : ℝ) / 2 ^ 12) : 0 < Gfun u := by
  have hc := coverB_ok
  rw [ptsB] at hc
  refine cover_sound (P := fun u => 0 < u → 0 < Gfun u) cellB
    (fun p q h u h1 h2 hu => cellB_sound Phi10_bound h u h1 h2 hu) _ _ _ hc u (by simpa using hu.le) ?_ hu
  have : lastZ 368 [460, 552, 598, 644, 690, 713, 737] = u0B := by decide
  rw [this]; exact hu2

theorem QR_pos_mid {u : ℝ} (hu1 : (u0B : ℝ) / 2 ^ 12 ≤ u) (hu2 : u ≤ 12) :
    0 < QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) := by
  have hc := coverA_ok
  rw [ptsA] at hc
  refine cover_sound cellA (fun p q h u h1 h2 => cellA_sound h h1 h2) _ _ _ hc u (by simpa [u0B] using hu1) ?_
  have : lastZ 742 [748, 754, 760, 766, 772, 778, 784, 795, 807, 819, 831, 842, 854, 866, 878, 890, 902, 914,
    926, 937, 949, 961, 973, 996, 1020, 1043, 1067, 1091, 1115, 1138, 1162, 1209, 1256, 1304, 1351, 1398, 1493,
    1587, 1682, 1871, 2249, 3005, 3762, 5275, 6788, 9814, 12840, 18892, 24944, 37048, 49152] = 49152 := by decide
  rw [this]; norm_num; linarith

/-! ## the region `u ≥ 12` -/

lemma abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

lemma abs_crossR_le {u x P0 P1 P2 t0 t1 t2 A B : ℝ} (hu0 : 0 ≤ u) (hux : u ≤ x) (hx : 2 ≤ x)
    (hB : B ≤ A) (hB0 : 0 ≤ B) (h0 : |P0| ≤ A) (h1 : |P1| ≤ A) (h2 : |P2| ≤ A)
    (g0 : |t0| ≤ B) (g1 : |t1| ≤ B) (g2 : |t2| ≤ B) :
    |crossR u P0 P1 P2 t0 t1 t2| ≤ 9 * x * A * B := by
  have hA0 : 0 ≤ A := le_trans hB0 hB
  have hu : |u| ≤ x := by rw [abs_of_nonneg hu0]; exact hux
  have s : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    have := abs_add_le a (-b); rwa [abs_neg, ← sub_eq_add_neg] at this
  have two : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have a1 : |2 * t1 - u * t2| ≤ 2 * x * B := by
    refine (s _ _).trans ?_
    rw [abs_mul, abs_mul, two]
    nlinarith [abs_nonneg t2, abs_nonneg u, mul_le_mul hu g2 (abs_nonneg _) (by linarith)]
  have a2 : |2 * P1 - u * P2| ≤ 2 * x * A := by
    refine (s _ _).trans ?_
    rw [abs_mul, abs_mul, two]
    nlinarith [abs_nonneg P2, abs_nonneg u, mul_le_mul hu h2 (abs_nonneg _) (by linarith)]
  have a3 : |2 * P1 * t1 + t1 ^ 2| ≤ 3 * A * B := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, two, abs_pow]
    have := mul_le_mul h1 g1 (abs_nonneg _) hA0
    have : |t1| ^ 2 ≤ A * B := by
      rw [sq]; exact mul_le_mul (le_trans g1 hB) g1 (abs_nonneg _) hA0
    nlinarith
  have T1 := abs_mul_le_of h0 a1
  have T2 := abs_mul_le_of g0 a2
  have T3 := abs_mul_le_of g0 a1
  have T4 := abs_mul_le_of hu a3
  unfold crossR
  have e := abs_add_le (P0 * (2 * t1 - u * t2) + t0 * (2 * P1 - u * P2) + t0 * (2 * t1 - u * t2))
    (u * (2 * P1 * t1 + t1 ^ 2))
  have e2 := abs_add_le (P0 * (2 * t1 - u * t2) + t0 * (2 * P1 - u * P2)) (t0 * (2 * t1 - u * t2))
  have e3 := abs_add_le (P0 * (2 * t1 - u * t2)) (t0 * (2 * P1 - u * P2))
  have h2xB : 0 ≤ 2 * x * B := mul_nonneg (by linarith) hB0
  have : B * (2 * x * B) ≤ 2 * x * A * B := by nlinarith [mul_le_mul_of_nonneg_left hB h2xB]
  nlinarith

lemma aS_Zs_le {i : ℕ} (hi : i ≤ 2) : aS (Zs i) ≤ 661 ∧ (Zs i).length ≤ 5 := by
  interval_cases i
  · simp [Zs, aS]; norm_num
  · rw [Zs_one]; simp [aS]; norm_num
  · rw [Zs_two]; simp [aS]; norm_num

lemma tail_large {i : ℕ} (hi : i ≤ 2) {x : ℝ} (hx : 100 ≤ x) :
    |sig (Zs i) x - pe (Zs i) x| ≤ 1322 * (5 * x) ^ 5 * rexp (-(3 * x)) := by
  have hpos : 0 < x := by linarith
  obtain ⟨hA, hn⟩ := aS_Zs_le hi
  have hcond : 2 * ((((1 : ℕ) : ℝ) + 2) / (((1 : ℕ) : ℝ) + 1)) ^ (2 * (Zs i).length) ≤
      rexp ((2 * ((1 : ℕ) : ℝ) + 3) * 100) := by
    have e1 : (((1 : ℕ) : ℝ) + 2) / (((1 : ℕ) : ℝ) + 1) = 3 / 2 := by norm_num
    have e2 : (2 * ((1 : ℕ) : ℝ) + 3) * 100 = 500 := by norm_num
    rw [e1, e2]
    have h1 : ((3 : ℝ) / 2) ^ (2 * (Zs i).length) ≤ (3 / 2) ^ 10 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 := add_one_le_exp (500 : ℝ)
    have h3 : ((3 : ℝ) / 2) ^ 10 ≤ 58 := by norm_num
    linarith
  have ht := tail_le (Zs i) 1 (by norm_num) hx hcond
  rw [sig_eq_main (Zs i) hpos 1 le_rfl]
  simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, zero_add]
  refine ht.trans ?_
  unfold gT
  have hK : Kk 1 = 4 := by unfold Kk; norm_num
  rw [hK, show -((4 : ℝ) - 1) * x = -(3 * x) by ring]
  have hA0 := aS_nonneg (Zs i)
  have hp : (1 + 4 * x) ^ (Zs i).length ≤ (5 * x) ^ 5 := by
    calc (1 + 4 * x) ^ (Zs i).length ≤ (5 * x) ^ (Zs i).length :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (5 * x) ^ 5 := pow_le_pow_right₀ (by linarith) hn
  have hE := (exp_pos (-(3 * x))).le
  calc 2 * (aS (Zs i) * (1 + 4 * x) ^ (Zs i).length * rexp (-(3 * x)))
      ≤ 2 * (661 * (5 * x) ^ 5 * rexp (-(3 * x))) := by gcongr
    _ = _ := by ring

lemma pe_large {i : ℕ} (hi : i ≤ 2) {x : ℝ} (hx : 1 ≤ x) : |pe (Zs i) x| ≤ 661 * (2 * x) ^ 5 := by
  obtain ⟨hA, hn⟩ := aS_Zs_le hi
  refine (abs_pe_le _ _).trans ?_
  rw [abs_of_pos (by linarith : (0 : ℝ) < x)]
  have hp : (1 + x) ^ (Zs i).length ≤ (2 * x) ^ 5 := by
    calc (1 + x) ^ (Zs i).length ≤ (2 * x) ^ (Zs i).length := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (2 * x) ^ 5 := pow_le_pow_right₀ (by linarith) hn
  have := aS_nonneg (Zs i)
  calc aS (Zs i) * (1 + x) ^ (Zs i).length ≤ 661 * (2 * x) ^ 5 := by gcongr

theorem QR_pos_large {u : ℝ} (hu : 12 ≤ u) :
    0 < QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) := by
  set x := xOf u with hxdef
  have hx : 8000000 ≤ x := by
    have h1 := Real.pow_div_factorial_le_exp (24 : ℝ) (by norm_num) 8
    have h2 : rexp 24 ≤ rexp (2 * u) := exp_le_exp.2 (by linarith)
    norm_num [Nat.factorial] at h1
    rw [hxdef]; unfold xOf
    nlinarith [pi_gt_three, exp_pos (2 * u)]
  have hux : u ≤ x := by
    have h1 := add_one_le_exp (2 * u)
    rw [hxdef]; unfold xOf
    nlinarith [pi_gt_three, exp_pos (2 * u)]
  set E := rexp (-(3 * x)) with hEdef
  have hE0 : 0 < E := exp_pos _
  have hE : E * (6561 * x ^ 8) ≤ 40320 := by
    have h1 := Real.pow_div_factorial_le_exp (3 * x) (by positivity) 8
    have h2 : E * rexp (3 * x) = 1 := by rw [hEdef, ← exp_add]; simp
    norm_num [Nat.factorial] at h1
    have : E * ((3 * x) ^ 8 / 40320) ≤ E * rexp (3 * x) := mul_le_mul_of_nonneg_left h1 hE0.le
    rw [h2] at this
    nlinarith
  set A := 661 * (2 * x) ^ 5
  set B := 1322 * (5 * x) ^ 5 * E
  have hB0 : 0 ≤ B := by positivity
  have hBA : B ≤ A := by
    have hx8 : (10000 : ℝ) ≤ x ^ 8 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) (show (10 : ℝ) ≤ x by linarith) 8
      norm_num at this; linarith
    have hE1 : E * 65610000 ≤ 40320 := by nlinarith
    simp only [A, B]
    have h5 : 0 < x ^ 5 := pow_pos (show (0 : ℝ) < x by linarith) 5
    have : 1322 * (5 * x) ^ 5 * E = x ^ 5 * (4131250 * E) := by ring
    have : 661 * (2 * x) ^ 5 = x ^ 5 * 21152 := by ring
    nlinarith
  have hsplit : QR u (sig (Zs 0) x) (sig (Zs 1) x) (sig (Zs 2) x) =
      Q0R u x + crossR u (pe (Zs 0) x) (pe (Zs 1) x) (pe (Zs 2) x) (sig (Zs 0) x - pe (Zs 0) x)
        (sig (Zs 1) x - pe (Zs 1) x) (sig (Zs 2) x - pe (Zs 2) x) := by
    rw [← QR_split]; simp
  have hc := abs_crossR_le (by linarith) hux (by linarith) hBA hB0
    (pe_large (i := 0) (by norm_num) (by linarith)) (pe_large (i := 1) (by norm_num) (by linarith))
    (pe_large (i := 2) (by norm_num) (by linarith)) (tail_large (i := 0) (by norm_num) (by linarith))
    (tail_large (i := 1) (by norm_num) (by linarith)) (tail_large (i := 2) (by norm_num) (by linarith))
  have hQ0 : x ^ 5 ≤ Q0R u x := by
    unfold Q0R
    have hx0 : 0 ≤ x := by linarith
    have h1 : 0 ≤ 32 * x ^ 3 * (2 * u - 1) + 4 * x ^ 2 * (42 - 48 * u) - x ^ 3 := by
      have : 4 * x ^ 2 * (42 - 48 * u) ≥ -(192 * u * x ^ 2) := by nlinarith [sq_nonneg x]
      have : 32 * x ^ 3 * (2 * u - 1) - x ^ 3 - 192 * u * x ^ 2 =
          x ^ 2 * (u * (64 * x - 192) - 33 * x) := by ring
      have : 0 ≤ u * (64 * x - 192) - 33 * x := by nlinarith
      nlinarith [sq_nonneg x]
    have h2 : 0 ≤ 240 * x * (u - 1) := by nlinarith
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) h1, mul_nonneg (sq_nonneg x) h2]
  have hcross : 9 * x * A * B ≤ 4900000000000 * x ^ 3 := by
    simp only [A, B]
    have : 9 * x * (661 * (2 * x) ^ 5) * (1322 * (5 * x) ^ 5 * E) =
        786457800000 * x ^ 3 * (E * x ^ 8) := by ring
    rw [this]
    have hx3 : 0 ≤ x ^ 3 := by positivity
    have : E * x ^ 8 ≤ 40320 / 6561 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hfin : 4900000000000 * x ^ 3 < x ^ 5 := by
    have hx3 : 0 < x ^ 3 := by positivity
    have : (4900000000000 : ℝ) < x ^ 2 := by nlinarith
    have : x ^ 5 = x ^ 2 * x ^ 3 := by ring
    nlinarith
  rw [hsplit]
  have := neg_abs_le (crossR u (pe (Zs 0) x) (pe (Zs 1) x) (pe (Zs 2) x) (sig (Zs 0) x - pe (Zs 0) x)
    (sig (Zs 1) x - pe (Zs 1) x) (sig (Zs 2) x - pe (Zs 2) x))
  linarith

/-! ## assembling `G > 0` -/

lemma Gfun_eq_QR (u : ℝ) : Gfun u = (rexp (u / 2) * rexp (-xOf u)) ^ 2 / 4 *
    QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) := by
  unfold Gfun QR
  rw [Phi_eq_sig 0, Phi_eq_sig 1, Phi_eq_sig 2]
  push_cast; ring

/-- **`G = Φ(Φ' − uΦ'') + uΦ'² > 0` on `(0,∞)`.** -/
theorem Gfun_pos {u : ℝ} (hu : 0 < u) : 0 < Gfun u := by
  rcases le_or_gt u ((u0B : ℝ) / 2 ^ 12) with h | h
  · exact Gfun_pos_small hu h
  · rw [Gfun_eq_QR]
    refine mul_pos (by positivity) ?_
    rcases le_or_gt u 12 with h' | h'
    · exact QR_pos_mid h.le h'
    · exact QR_pos_large h'.le

/-! ## monotonicity of `R` -/

lemma Phi0_pos {u : ℝ} (hu : 0 ≤ u) : 0 < Phi 0 u := by rw [← PhiR_eq]; exact PhiR_pos hu

theorem hasDerivAt_ratio {u : ℝ} (hu : 0 < u) :
    HasDerivAt (ratioR PhiR PhiD) (Gfun u / (u * Phi 0 u) ^ 2) u := by
  rw [PhiR_eq, PhiD_eq]
  have hP := Phi0_pos hu.le
  have hne : u * Phi 0 u ≠ 0 := (mul_pos hu hP).ne'
  have h := (hasDerivAt_Phi 1 u).neg.div ((hasDerivAt_id' u).mul (hasDerivAt_Phi 0 u)) hne
  have e : ratioR (Phi 0) (Phi 1) = fun x => -Phi 1 x / (x * Phi 0 x) := by
    funext x; simp [ratioR]
  rw [e]
  simp only [Pi.mul_apply, Pi.neg_apply] at h
  convert h using 1
  congr 1
  unfold Gfun
  simp only [show (1 : ℕ) + 1 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl]
  ring

/-- **`CVHyp` holds** (Csordas–Varga's log-concavity of `Φ(√t)`, here with a kernel-checked proof). -/
theorem cvHyp_holds : CVHyp := by
  unfold CVHyp
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (ratioR PhiR PhiD) (Gfun u / (u * Phi 0 u) ^ 2) u :=
    fun u hu => hasDerivAt_ratio hu
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun u hu => (hd u hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro u hu
    rw [(hd u hu).deriv]
    exact div_nonneg (Gfun_pos hu).le (sq_nonneg _)

end GORZXiEff.CV

namespace GORZXiEff

/-- **Turán inequalities for `Ξ`, unconditional** (Csordas–Norfolk–Varga 1986):
`γ(n) γ(n+2) ≤ γ(n+1)²` for every `n ≥ 0`. -/
theorem turan_gamma_unconditional (n : ℕ) :
    GORZXi.gammaMathlib n * GORZXi.gammaMathlib (n + 2) ≤ GORZXi.gammaMathlib (n + 1) ^ 2 :=
  turan_gamma CV.cvHyp_holds n

/-- **GORZ Theorem 2 for `d = 2`, unconditional**: `J^{2,n}_γ` is hyperbolic for every `n ≥ 0`. -/
theorem jensen2_gamma_unconditional (n : ℕ) :
    JensenThreshold.Hyperbolic (GORZXi.jensenSeq GORZXi.gammaMathlib 2 n) :=
  jensen2_gamma CV.cvHyp_holds n

end GORZXiEff

#print axioms GORZXiEff.CV.cvHyp_holds
#print axioms GORZXiEff.turan_gamma_unconditional
#print axioms GORZXiEff.jensen2_gamma_unconditional
#print axioms GORZXiEff.CV.Gfun_pos
#print axioms GORZXiEff.CV.hasDerivAt_ratio
#print axioms GORZXiEff.CV.Phi_odd_zero
#print axioms GORZXiEff.CV.hasDerivAt_Phi
#print axioms GORZXiEff.CV.PhiR_eq
#print axioms GORZXiEff.CV.PhiD_eq
#print axioms GORZXiEff.CV.Phi10_bound
#print axioms GORZXiEff.CV.Gfun_pos_small
#print axioms GORZXiEff.CV.QR_pos_mid
#print axioms GORZXiEff.CV.QR_pos_large
