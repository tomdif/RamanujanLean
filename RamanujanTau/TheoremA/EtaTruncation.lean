import RamanujanTau.TheoremA.EtaFormalProducts

/-! Euler-product coefficient certificates at an arbitrary truncation bound. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open PowerSeries RankProof

def eulerListToAux (D d : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => truncList D (mulList (eulerListToAux D d n) (oneMinusXk (d * (n + 1))))

def eulerListTo (D d : ℕ) : List ℤ := eulerListToAux D d D

lemma pi_eulerListToAux (D d : ℕ) (hd : 0 < d) (n : ℕ) :
    FourSquares.π (D + 1) (toPS (eulerListToAux D d n)) = FourSquares.π (D + 1) (Pfin d d n) := by
  induction n with
  | zero => simp [eulerListToAux, Pfin, toPS_cons, toPS_nil]
  | succ n ih =>
    rw [eulerListToAux, π_truncList, toPS_mulList, map_mul, ih,
      toPS_oneMinusXk_of_pos (by positivity), Pfin_succ, map_mul]
    congr 2
    congr 1
    ring

lemma pi_eulerListTo (D d : ℕ) (hd : 0 < d) :
    FourSquares.π (D + 1) (toPS (eulerListTo D d)) = FourSquares.π (D + 1) (Pinf d d) := by
  rw [eulerListTo, pi_eulerListToAux D d hd]
  apply Eq.symm
  exact FourSquares.π_eq_iff.mpr (X_pow_dvd_Pinf_sub d d hd hd D)

def etaProductListTo (D s d k e r : ℕ) : List ℤ :=
  truncList D (shiftList s
    (mulList (truncPowList D (eulerListTo D d) k) (truncPowList D (eulerListTo D e) r)))

lemma pi_etaProductListTo (D s d k e r : ℕ) (hd : 0 < d) (he : 0 < e) :
    FourSquares.π (D + 1) (toPS (etaProductListTo D s d k e r)) =
      FourSquares.π (D + 1) (etaProductSeries s d k e r) := by
  rw [etaProductListTo, π_truncList]
  have hs : toPS (shiftList s
      (mulList (truncPowList D (eulerListTo D d) k) (truncPowList D (eulerListTo D e) r))) =
      X ^ s * toPS (mulList (truncPowList D (eulerListTo D d) k) (truncPowList D (eulerListTo D e) r)) := by
    induction s with
    | zero => simp [shiftList]
    | succ s ih => rw [shiftList, toPS_cons, ih, map_zero, zero_add]; ring
  rw [hs, toPS_mulList, map_mul, map_mul, π_truncPow, π_truncPow,
    pi_eulerListTo D d hd, pi_eulerListTo D e he]
  simp [etaProductSeries, map_mul, map_pow, mul_assoc]

theorem etaProductSeries_coeff_to (D s d k e r : ℕ) (hd : 0 < d) (he : 0 < e)
    {n : ℕ} (hn : n < D + 1) :
    (etaProductSeries s d k e r).coeff n = coeffList (etaProductListTo D s d k e r) n := by
  simpa only [toPS, coeff_mk] using (FourSquares.coeff_eq_of_dvd
    (FourSquares.π_eq_iff.mp (pi_etaProductListTo D s d k e r hd he)) hn).symm


end RamanujanTau.TheoremA.EtaSquared
