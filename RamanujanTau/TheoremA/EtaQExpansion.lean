import RamanujanTau.TheoremA.EtaQProducts
import RamanujanTau.TheoremA.EtaFormalProducts

/-! The actual eta cusp forms have the certified integer Fourier coefficients. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm Realize PowerSeries RankProof
open UpperHalfPlane hiding I

noncomputable def etaProductFunction (s d k e r : ℕ) (q : ℂ) : ℂ :=
  q ^ s * Pfun d d q ^ k * Pfun e e q ^ r

lemma etaProduct_realizes (s d k e r : ℕ) (hd : 0 < d) (he : 0 < e) :
    Realizes (etaProductFunction s d k e r) (etaProductSeries s d k e r) :=
  ((realizes_X.pow s).mul ((realizes_Pinf d d hd hd).pow k)).mul
    ((realizes_Pinf e e he he).pow r)

theorem qExpansion_g : qExpansion 1 (basisCuspForm 0) =
    PowerSeries.map (Int.castRingHom ℂ) (etaProductSeries 1 1 6 3 6) := by
  have hf : (basisCuspForm 0 : ℍ → ℂ) = qLift (etaProductFunction 1 1 6 3 6) := by
    funext z
    simpa [qLift, etaProductFunction] using basis_zero_qProduct z
  rw [hf]
  exact qExpansion_qLift (etaProduct_realizes 1 1 6 3 6 (by decide) (by decide))

theorem qExpansion_v : qExpansion 1 (basisCuspForm 1) =
    PowerSeries.map (Int.castRingHom ℂ) (etaProductSeries 2 2 6 6 6) := by
  have hf : (basisCuspForm 1 : ℍ → ℂ) = qLift (etaProductFunction 2 2 6 6 6) := by
    funext z
    exact basis_one_qProduct z
  rw [hf]
  exact qExpansion_qLift (etaProduct_realizes 2 2 6 6 6 (by decide) (by decide))

theorem qExpansion_w_relation :
    qExpansion 1 (basisCuspForm 2) * PowerSeries.map (Int.castRingHom ℂ) wDenominator =
      PowerSeries.map (Int.castRingHom ℂ) wNumerator := by
  have hf : (basisCuspForm 2 : ℍ → ℂ) * qLift (etaProductFunction 0 2 2 3 4) =
      qLift (etaProductFunction 3 1 4 6 14) := by
    funext z
    simpa [qLift, etaProductFunction] using basis_two_qProduct z
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (basisCuspForm 2)
    (one_pos : (0 : ℝ) < 1) (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
  have hd := etaProduct_realizes 0 2 2 3 4 (by decide) (by decide)
  have hn := etaProduct_realizes 3 1 4 6 14 (by decide) (by decide)
  have hq := congrArg (qExpansion 1) hf
  rw [qExpansion_mul ha (qLift_analytic hd), qExpansion_qLift hd, qExpansion_qLift hn] at hq
  exact hq

theorem qExpansion_w : qExpansion 1 (basisCuspForm 2) =
    PowerSeries.map (Int.castRingHom ℂ) wSeries := by
  apply (wDenominator_isUnit.map (PowerSeries.map (Int.castRingHom ℂ))).mul_right_cancel
  rw [qExpansion_w_relation, ← map_mul, wSeries_mul]

theorem g_coeff {n : ℕ} (hn : n < 10) :
    (qExpansion 1 (basisCuspForm 0)).coeff n = (coeffList gCoefficients n : ℂ) := by
  rw [qExpansion_g, coeff_map, etaProductSeries_coeff _ _ _ _ _ (by decide) (by decide) hn,
    g_list_certificate]
  rfl

theorem v_coeff {n : ℕ} (hn : n < 10) :
    (qExpansion 1 (basisCuspForm 1)).coeff n = (coeffList vCoefficients n : ℂ) := by
  rw [qExpansion_v, coeff_map, etaProductSeries_coeff _ _ _ _ _ (by decide) (by decide) hn,
    v_list_certificate]
  rfl

theorem w_coeff {n : ℕ} (hn : n < 10) :
    (qExpansion 1 (basisCuspForm 2)).coeff n = (coeffList wCoefficients n : ℂ) := by
  rw [qExpansion_w, coeff_map, wSeries_coeff hn]
  rfl

end RamanujanTau.TheoremA.EtaSquared
