/-
# The χ₀ mock theta conjecture, unconditionally (Watson's route)

  `χ₀(q) − 2 = 3(Φ(q) − 1) − (q⁵;q⁵)²_∞ J_{5,2}/J_{5,1}²`        (`chi0_identity`)

and hence Andrews–Garvan's `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀` (`rank_chi0`). The proof combines:
* Watson's (B₀) = R1 `χ₀ = 2F₀ − φ₀(−q)` (`chi0_R1_watson`), applied at `q²`;
* Watson's (2₀) and (3₀) (`watson_2_0`, `watson_3_0`);
* MTC₀ (`MTC.mock_theta_conjecture_f0`);
* the theta identity `star_L`.

As a corollary the hypothesis `ThetaId` of `MTC/Chi0Final.lean` is now a theorem (`thetaId`).
-/
import RamanujanTau.Watson.Star
import RamanujanTau.Watson.F0Rel
import RamanujanTau.MTC.MTC0
import RamanujanTau.MTC.Chi0Final
import RamanujanTau.MTC.Hecke373
import RamanujanTau.RogersRamanujan
import RamanujanTau.MockTheta5R1

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Watson
open PowerSeries Finset

/-! ### bridges to the repository's definitions -/

lemma osum_eq_mk {f : ℕ → PowerSeries ℤ} (h : ∀ n k, k < n → coeff k (f n) = 0) :
    osum f = mk fun k => coeff k (∑ n ∈ range (k + 1), f n) := by
  ext k
  rw [coeff_osum, coeff_mk, map_sum]
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  simp only [Function.mem_support, coe_range, Set.mem_Iio] at hn ⊢
  by_contra hc; exact hn (h n k (by omega))

lemma FP_one_eq_Pfin (b a M : ℕ) : FP 1 b a M = RankProof.Pfin b a M := by
  simp [FP, RankProof.Pfin]

lemma IP_eq_Pinf (b a : ℕ) : IP 1 b a = RankProof.Pinf b a := by
  ext k; simp only [IP, RankProof.Pinf, coeff_mk, FP_one_eq_Pfin]

lemma chiA_eq : chiA = MockTheta5.Formal.chi0 := by
  rw [chiA, osum_eq_mk (fun n k hk => by rw [coeff_X_pow_mul', if_neg (by omega)]),
    MockTheta5.Formal.chi0]
  congr 1; ext k; congr 1
  refine sum_congr rfl fun n _ => ?_
  simp only [MockTheta5.Formal.chi0term, MockTheta5.Formal.qpochG, FP]
  congr 2
  refine prod_congr rfl fun j _ => ?_
  rw [pow_add]; simp

lemma f0w_eq : f0w = MockTheta5.JTP.f0 := by
  rw [f0w, osum_eq_mk (fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]),
    MockTheta5.JTP.f0, MockTheta5.JTP.tsumQsq]
  congr 1; ext k; congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [sq]
  congr 2
  simp only [FP, MockTheta5.Bailey.mqfac]
  refine prod_congr rfl fun j _ => ?_
  simp; ring_nf

lemma FP111_eq_qfac (n : ℕ) : FP 1 1 1 n = MockTheta5.Bailey.qfac n := by
  simp only [FP, MockTheta5.Bailey.qfac]
  refine prod_congr rfl fun j _ => ?_
  simp [add_comm]

lemma Gw_series : Gw = MockTheta5.JTP.tsumQsq (fun n => Ring.inverse (MockTheta5.Bailey.qfac n)) := by
  have e : Gw = osum fun n => X ^ (n * n) * Ring.inverse (MockTheta5.Bailey.qfac n) :=
    osum_ext fun n => by rw [← FP111_eq_qfac]
  rw [e, osum_eq_mk (fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]), MockTheta5.JTP.tsumQsq]
  simp only [sq]

lemma Hw_series : Hw = MockTheta5.JTP.tsumQsqQ (fun n => Ring.inverse (MockTheta5.Bailey.qfac n)) := by
  have e : Hw = osum fun n => X ^ (n * n + n) * Ring.inverse (MockTheta5.Bailey.qfac n) :=
    osum_ext fun n => by rw [← FP111_eq_qfac]
  rw [e, osum_eq_mk (fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]), MockTheta5.JTP.tsumQsqQ]
  simp only [sq]

lemma Gw_eq : Gw = Ring.inverse (RankProof.Pinf 1 5 * RankProof.Pinf 4 5) := by
  rw [Gw_series]; exact MockTheta5.JTP.RR.rogers_ramanujan_1

lemma Hw_eq : Hw = Ring.inverse (RankProof.Pinf 2 5 * RankProof.Pinf 3 5) := by
  rw [Hw_series]; exact MockTheta5.JTP.RR.rogers_ramanujan_2

/-! ### the assembly -/

open ALz HahnSeries in
lemma ι_inv {f : PowerSeries ℤ} (hf : IsUnit f) : ALz.ιN Watson.Star.h1 (Ring.inverse f) = (ALz.ιN Watson.Star.h1 f)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, Ring.mul_inverse_cancel _ hf, map_one]

lemma uP (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : IsUnit (RankProof.Pinf b a) := RankProof.isUnit_Pinf b a hb ha

lemma expand_Pinf (e : ℕ) (he : e ≠ 0) (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) :
    expand e he (RankProof.Pinf b a) = RankProof.Pinf (e * b) (e * a) := by
  rw [← IP_eq_Pinf, expand_IP e he 1 hb ha, IP_eq_Pinf]

local notation "ιq" => ALz.ιN Watson.Star.h1

open ALz HahnSeries in
/-- **The χ₀ mock theta conjecture** (Andrews–Garvan form), unconditionally:
`χ₀(q) − 2 = 3(Φ(q) − 1) − (q⁵;q⁵)²_∞ J_{5,2}/J_{5,1}²`. -/
theorem chi0_identity :
    MockTheta5.Formal.chi0 - 2 =
      3 * (RankProof.Phi 1 - 1) - MockTheta5.JTP.eQ ^ 2 * CrankProof.Jab 5 2 * Ring.inverse (CrankProof.Jab 5 1) ^ 2 := by
  set E2 := expand (R := ℤ) 2 two_ne_zero
  set E4 := expand (R := ℤ) 4 (by norm_num)
  set P := MockTheta5.JTP.eQ ^ 2 * CrankProof.Jab 5 2 * Ring.inverse (CrankProof.Jab 5 1) ^ 2
  -- the ingredients
  have hR : E2 chiA = 2 * E2 F0w - E2 P0w := by
    rw [chi0_R1_watson, map_sub, map_mul, map_ofNat]
  have h2 := watson_2_0
  have h3 := watson_3_0
  have hM := MTC.mock_theta_conjecture_f0
  rw [← f0w_eq] at hM
  have hS := Watson.Star.star_L
  -- product forms of the theta quotients, in `ℂ((q))`
  have u15 := uP 1 5 le_rfl (by norm_num); have u45 := uP 4 5 (by norm_num) (by norm_num)
  have u25 := uP 2 5 (by norm_num) (by norm_num); have u35 := uP 3 5 (by norm_num) (by norm_num)
  have u24 := uP 2 4 (by norm_num) (by norm_num)
  have u51 : IsUnit (CrankProof.Jab 5 1) := MTC.Chi0L.isUnit_Jab 5 1 le_rfl (by norm_num)
  have eG : ιq Gw = (ιq (RankProof.Pinf 1 5) * ιq (RankProof.Pinf 4 5))⁻¹ := by
    rw [Gw_eq, ι_inv (u15.mul u45), map_mul]
  have eH : ιq (E4 Hw) = (ιq (RankProof.Pinf 8 20) * ιq (RankProof.Pinf 12 20))⁻¹ := by
    rw [Hw_eq, show E4 (Ring.inverse (RankProof.Pinf 2 5 * RankProof.Pinf 3 5)) =
      Ring.inverse (E4 (RankProof.Pinf 2 5 * RankProof.Pinf 3 5)) from expand_inverse 4 _ (u25.mul u35),
      map_mul, expand_Pinf 4 _ 2 5 (by norm_num) (by norm_num), expand_Pinf 4 _ 3 5 (by norm_num) (by norm_num),
      ι_inv ((uP _ _ (by norm_num) (by norm_num)).mul (uP _ _ (by norm_num) (by norm_num))), map_mul]
  have epsi : ιq psi2w = ιq (RankProof.Pinf 4 4) * (ιq (RankProof.Pinf 2 4))⁻¹ := by
    rw [psi2w, map_mul, IP_eq_Pinf, IP_eq_Pinf, ι_inv u24]
  have eth : ιq th4w = ιq (RankProof.Pinf 1 1) * ιq (RankProof.Pinf 1 1) * (ιq (RankProof.Pinf 2 2))⁻¹ := by
    have hsq := IP_sq 1 (a := 1) (b := 1) le_rfl le_rfl
    norm_num at hsq
    rw [IP_eq_Pinf, IP_eq_Pinf] at hsq
    have hne : ιq (RankProof.Pinf 1 1) ≠ 0 := ((uP 1 1 le_rfl le_rfl).map ιq).ne_zero
    have hne2 : ιq (IP (-1) 1 1) ≠ 0 := ((isUnit_IP (-1) le_rfl le_rfl).map ιq).ne_zero
    have hm := congrArg ιq hsq
    rw [map_mul] at hm
    rw [th4w, map_mul, IP_eq_Pinf, ι_inv (isUnit_IP (-1) le_rfl le_rfl), ← hm]
    field_simp
  have eT : ιq (RankProof.Pinf 5 10 * RankProof.Pinf 5 10 * RankProof.Pinf 10 10 *
      Ring.inverse (RankProof.Pinf 1 5 * RankProof.Pinf 4 5)) =
      ιq (RankProof.Pinf 5 10) * ιq (RankProof.Pinf 5 10) * ιq (RankProof.Pinf 10 10) *
        (ιq (RankProof.Pinf 1 5) * ιq (RankProof.Pinf 4 5))⁻¹ := by
    rw [map_mul, map_mul, map_mul, ι_inv (u15.mul u45), map_mul]
  have eP : ιq (E2 P) = ιq (RankProof.Pinf 10 10) ^ 2 *
      (ιq (RankProof.Pinf 4 10) * ιq (RankProof.Pinf 6 10) * ιq (RankProof.Pinf 10 10)) *
      ((ιq (RankProof.Pinf 2 10) * ιq (RankProof.Pinf 8 10) * ιq (RankProof.Pinf 10 10))⁻¹) ^ 2 := by
    have eJ : ∀ b, 1 ≤ b → b < 5 → E2 (CrankProof.Jab 5 b) =
        RankProof.Pinf (2 * b) 10 * RankProof.Pinf (2 * (5 - b)) 10 * RankProof.Pinf 10 10 := fun b hb h5 => by
      simp only [CrankProof.Jab, map_mul]
      rw [expand_Pinf 2 _ b 5 hb (by norm_num), expand_Pinf 2 _ (5 - b) 5 (by omega) (by norm_num),
        expand_Pinf 2 _ 5 5 (by norm_num) (by norm_num)]
    simp only [P, map_mul, map_pow]
    rw [show E2 (Ring.inverse (CrankProof.Jab 5 1)) = Ring.inverse (E2 (CrankProof.Jab 5 1)) from
      expand_inverse 2 _ u51, eJ 1 le_rfl (by norm_num), eJ 2 (by norm_num) (by norm_num),
      CrankProof.eQ_Pinf, expand_Pinf 2 _ 5 5 (by norm_num) (by norm_num)]
    rw [ι_inv (((uP _ _ (by norm_num) (by norm_num)).mul (uP _ _ (by norm_num) (by norm_num))).mul
      (uP _ _ (by norm_num) (by norm_num)))]
    simp only [map_mul]
  -- map the four linear relations to `ℂ((q))`
  have hR' := congrArg ιq hR
  have h2' := congrArg ιq h2
  have h3' := congrArg ιq h3
  have hM' := congrArg ιq hM
  simp only [map_sub, map_add, map_mul, map_ofNat, map_one] at hR' h2' h3' hM'
  rw [eG, eth] at h2' h3'
  rw [epsi, eH, MTC.ιN_X] at h3'
  rw [ι_inv (u15.mul u45), map_mul] at hM'
  -- the doubled target, at `q²`, in `ℂ((q))`
  have key : ιq (E2 (2 * (MockTheta5.Formal.chi0 - 2 - (3 * (RankProof.Phi 1 - 1) - P)))) = 0 := by
    rw [← chiA_eq]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    rw [eP]
    have hEa : (RankProof.Ea 2 two_ne_zero) (RankProof.Phi 1) = E2 (RankProof.Phi 1) := rfl
    rw [hEa] at hM'
    linear_combination 2 * hR' + h2' + 2 * h3' - 3 * hM' + hS
  have h0 : E2 (2 * (MockTheta5.Formal.chi0 - 2 - (3 * (RankProof.Phi 1 - 1) - P))) = E2 0 := by
    rw [map_zero]; exact MTC.ιN_injective Watson.Star.h1 (by rw [key, map_zero])
  have h1 := expand_injective 2 two_ne_zero h0
  have h2ne : (2 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 0) h
    rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 by simp, PowerSeries.coeff_C, if_pos rfl, map_zero] at this
    norm_num at this
  have := (mul_eq_zero.mp h1).resolve_left h2ne
  linear_combination this

end Watson

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

/-- **`ThetaId` holds**: the theta-function identity that `MTC/Chi0Final.lean` took as a hypothesis is a
consequence of the unconditional χ₀ identity (Watson's route). -/
theorem thetaId : ThetaId := by
  have hc := congrArg (ιN h6) Watson.chi0_identity
  have h51 : IsUnit (CrankProof.Jab 5 1) := isUnit_Jab 5 1 le_rfl (by norm_num)
  simp only [map_sub, map_mul, map_pow, ιN_inv h51] at hc
  have he : ιN h6 MockTheta5.JTP.eQ = e6 := rfl
  rw [he, show ((3 : PowerSeries ℤ)) = (3 : ℕ) by norm_num, map_natCast,
    show ((2 : PowerSeries ℤ)) = (2 : ℕ) by norm_num, map_natCast, map_one] at hc
  push_cast at hc
  have k1 := hm_side
  have k2 := phi_side
  rw [map_mul] at k1
  have hJ := Jb6_ne
  have he6 : e6 ≠ 0 := unit_ne ((MockTheta5.JTP.isUnit_qfacInf).map _)
  have h51' : ιN h6 (CrankProof.Jab 5 1) ≠ 0 := unit_ne h51
  unfold ThetaId
  linear_combination (norm := (field_simp; ring)) (Jb6 * e6 * q6) * hc - e6 * k1 + 3 * q6 * k2

/-- **Andrews–Garvan's combinatorial form, unconditionally**: for `n ≥ 1`,
`N(1,5,5n) − N(0,5,5n) = [qⁿ] χ₀`. -/
theorem rank_chi0 (n : ℕ) (hn : 1 ≤ n) :
    (CrankProof.rankCount (5 * n) 1 : ℤ) - CrankProof.rankCount (5 * n) 0 = PowerSeries.coeff n MockTheta5.Formal.chi0 :=
  rank_chi0_of thetaId n hn

end MTC.Chi0L
