import RamanujanTau.TauBridge
import RamanujanTau.RankTheta

/-! Kernel-checked integer coefficient certificates for the weight-six eta quotients. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open PowerSeries RankProof

noncomputable def etaProductSeries (s d k e r : ℕ) : PowerSeries ℤ :=
  X ^ s * Pinf d d ^ k * Pinf e e ^ r

def eulerListAux (d : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => truncList 9 (mulList (eulerListAux d n) (oneMinusXk (d * (n + 1))))

def eulerList (d : ℕ) : List ℤ := eulerListAux d 9

lemma toPS_oneMinusXk_of_pos {n : ℕ} (hn : 0 < n) :
    toPS (oneMinusXk n) = 1 - (X : PowerSeries ℤ) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact toPS_oneMinusXk m

lemma pi_eulerListAux (d : ℕ) (hd : 0 < d) (n : ℕ) :
    FourSquares.π 10 (toPS (eulerListAux d n)) = FourSquares.π 10 (Pfin d d n) := by
  induction n with
  | zero => simp [eulerListAux, Pfin, toPS_cons, toPS_nil]
  | succ n ih =>
    rw [eulerListAux, π_truncList, toPS_mulList, map_mul, ih,
      toPS_oneMinusXk_of_pos (by positivity), Pfin_succ, map_mul]
    congr 2
    congr 1
    ring

lemma pi_eulerList (d : ℕ) (hd : 0 < d) :
    FourSquares.π 10 (toPS (eulerList d)) = FourSquares.π 10 (Pinf d d) := by
  rw [eulerList, pi_eulerListAux d hd]
  apply Eq.symm
  exact FourSquares.π_eq_iff.mpr (X_pow_dvd_Pinf_sub d d hd hd 9)

def etaProductList (s d k e r : ℕ) : List ℤ :=
  truncList 9 (shiftList s
    (mulList (truncPowList 9 (eulerList d) k) (truncPowList 9 (eulerList e) r)))

lemma pi_etaProductList (s d k e r : ℕ) (hd : 0 < d) (he : 0 < e) :
    FourSquares.π 10 (toPS (etaProductList s d k e r)) =
      FourSquares.π 10 (etaProductSeries s d k e r) := by
  rw [etaProductList, π_truncList]
  have hs : toPS (shiftList s
      (mulList (truncPowList 9 (eulerList d) k) (truncPowList 9 (eulerList e) r))) =
      X ^ s * toPS (mulList (truncPowList 9 (eulerList d) k) (truncPowList 9 (eulerList e) r)) := by
    induction s with
    | zero => simp [shiftList]
    | succ s ih => rw [shiftList, toPS_cons, ih, map_zero, zero_add]; ring
  rw [hs, toPS_mulList, map_mul, map_mul, π_truncPow, π_truncPow,
    pi_eulerList d hd, pi_eulerList e he]
  simp [etaProductSeries, map_mul, map_pow, mul_assoc]

theorem etaProductSeries_coeff (s d k e r : ℕ) (hd : 0 < d) (he : 0 < e)
    {n : ℕ} (hn : n < 10) :
    (etaProductSeries s d k e r).coeff n = coeffList (etaProductList s d k e r) n := by
  simpa only [toPS, coeff_mk] using (FourSquares.coeff_eq_of_dvd
    (FourSquares.π_eq_iff.mp (pi_etaProductList s d k e r hd he)) hn).symm

def gCoefficients : List ℤ := [0, 1, -6, 9, 4, 6, -54, -40, 168, 81]
def vCoefficients : List ℤ := [0, 0, 1, 0, -6, 0, 9, 0, 4, 0]
def wCoefficients : List ℤ := [0, 0, 0, 1, -4, 4, 4, -12, 8, 0]

theorem g_list_certificate : etaProductList 1 1 6 3 6 = gCoefficients := by decide +kernel
theorem v_list_certificate : etaProductList 2 2 6 6 6 = vCoefficients := by decide +kernel

theorem w_list_certificate :
    truncList 9 (mulList wCoefficients (etaProductList 0 2 2 3 4)) =
      etaProductList 3 1 4 6 14 := by decide +kernel

noncomputable def wDenominator : PowerSeries ℤ := etaProductSeries 0 2 2 3 4
noncomputable def wNumerator : PowerSeries ℤ := etaProductSeries 3 1 4 6 14
noncomputable def wSeries : PowerSeries ℤ := wNumerator * Ring.inverse wDenominator

theorem wDenominator_isUnit : IsUnit wDenominator := by
  simpa [wDenominator, etaProductSeries] using
    ((isUnit_Pinf 2 2 (by decide) (by decide)).pow 2).mul
      ((isUnit_Pinf 3 3 (by decide) (by decide)).pow 4)

theorem wSeries_mul : wSeries * wDenominator = wNumerator := by
  rw [wSeries, mul_assoc, Ring.inverse_mul_cancel _ wDenominator_isUnit, mul_one]

theorem pi_wSeries : FourSquares.π 10 wSeries = FourSquares.π 10 (toPS wCoefficients) := by
  have hc := congrArg (fun L => FourSquares.π 10 (toPS L)) w_list_certificate
  dsimp only at hc
  rw [π_truncList, toPS_mulList, map_mul,
    pi_etaProductList 0 2 2 3 4 (by decide) (by decide),
    pi_etaProductList 3 1 4 6 14 (by decide) (by decide)] at hc
  apply (wDenominator_isUnit.map (FourSquares.π 10)).mul_right_cancel
  rw [← map_mul, wSeries_mul]
  exact hc.symm

theorem wSeries_coeff {n : ℕ} (hn : n < 10) : wSeries.coeff n = coeffList wCoefficients n := by
  simpa only [toPS, coeff_mk] using
    FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp pi_wSeries) hn

end RamanujanTau.TheoremA.EtaSquared
