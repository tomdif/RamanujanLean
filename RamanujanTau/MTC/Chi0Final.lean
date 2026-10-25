/-
# The χ₀ mock theta identity, reduced to one theta-function identity

Combining the HM side (`hm_side`) and the `Φ` side (`phi_side`), every Appell–Lerch sum cancels, and

  `χ₀(q) − 2 = 3(φ(q) − 0) … ` i.e.  `χ₀ − 2 = 3(Φ − 1) − (q⁵;q⁵)²_∞ J_{5,2}/J_{5,1}²`

follows from the single theta-function identity `ThetaId` (17 theta quotients at `Q = t⁶`, verified numerically to
`Q^{170}`). With `rank_diff_mod5` this gives the Andrews–Garvan combinatorial form
`N(1,5,5n) − N(0,5,5n) = [qⁿ] χ₀` (`rank_chi0_of`).
-/
import RamanujanTau.MTC.Chi0Phi
import RamanujanTau.RankDiff5
import RamanujanTau.MTC.Final0

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

/-- `(Q;Q)_∞`, `(Q⁵;Q⁵)_∞` in `ℂ((t))`. -/
noncomputable abbrev q6 : L := ιN h6 MockTheta5.JTP.qfacInf
noncomputable abbrev e6 : L := ιN h6 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)

/-- **the remaining theta-function identity** (all terms are theta quotients):
`(Q⁵;Q⁵) κ Σ θ_{2,1} = 3(Q;Q) T₁ + 3(Q;Q) t⁶ J̄ A₁₅ − (Q;Q) J̄ (Q⁵;Q⁵)³ J_{5,2}/J_{5,1}²`. -/
def ThetaId : Prop :=
  e6 * (kap (H232.h5 H232.hq36) * TVsum) =
    3 * q6 * T1s + 3 * q6 * (tt ^ (6 : ℤ) * Jb6 * hs (LF h6 15)) -
      q6 * Jb6 * e6 ^ 3 * ιN h6 (CrankProof.Jab 5 2) / ιN h6 (CrankProof.Jab 5 1) ^ 2

lemma unit_ne {f : PowerSeries ℤ} (hf : IsUnit f) : ιN h6 f ≠ 0 := (hf.map (ιN h6)).ne_zero

lemma Jb6_ne : Jb6 ≠ 0 := θ_ne_zero hN360 (by norm_num) fun _ _ => by norm_num

lemma isUnit_Jab (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) : IsUnit (CrankProof.Jab a b) := by
  unfold CrankProof.Jab
  exact ((RankProof.isUnit_Pinf b a hb (by omega)).mul (RankProof.isUnit_Pinf (a - b) a (by omega) (by omega))).mul
    (RankProof.isUnit_Pinf a a (by omega) (by omega))

/-- the identity in `ℂ((t))`. -/
theorem chi0_L (hΘ : ThetaId) :
    ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) - 2 * q6 =
      q6 * (3 * ιN h6 (RankProof.Phi 1) - 3 - e6 ^ 2 * ιN h6 (CrankProof.Jab 5 2) / ιN h6 (CrankProof.Jab 5 1) ^ 2) := by
  have hJ := Jb6_ne
  have he : e6 ≠ 0 := unit_ne ((MockTheta5.JTP.isUnit_qfacInf).map _)
  have h51 : ιN h6 (CrankProof.Jab 5 1) ≠ 0 := unit_ne (isUnit_Jab 5 1 le_rfl (by norm_num))
  have k1 := hm_side
  have k2 := phi_side
  unfold ThetaId at hΘ
  apply mul_left_cancel₀ (mul_ne_zero hJ he)
  linear_combination (norm := (field_simp; ring)) e6 * k1 - 3 * q6 * k2 + hΘ

lemma ιN_inv {f : PowerSeries ℤ} (hf : IsUnit f) : ιN h6 (Ring.inverse f) = (ιN h6 f)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← map_mul, Ring.mul_inverse_cancel _ hf, map_one]

/-- **the χ₀ mock theta conjecture**, conditional on `ThetaId`:
`χ₀(q) − 2 = 3(Φ(q) − 1) − (q⁵;q⁵)²_∞ J_{5,2}/J_{5,1}²` with `Φ = 1 + φ` the rank function. -/
theorem chi0_identity_of (hΘ : ThetaId) :
    MockTheta5.Formal.chi0 - 2 =
      3 * (RankProof.Phi 1 - 1) - MockTheta5.JTP.eQ ^ 2 * CrankProof.Jab 5 2 * Ring.inverse (CrankProof.Jab 5 1) ^ 2 := by
  have hq := MockTheta5.JTP.isUnit_qfacInf
  apply hq.mul_left_cancel
  apply ιN_injective h6
  have h := chi0_L hΘ
  have h51 := isUnit_Jab 5 1 le_rfl (by norm_num)
  rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_mul, map_pow, map_pow, ιN_inv h51, map_sub, map_one]
  rw [mul_sub, map_mul] at h
  have he : ιN h6 MockTheta5.JTP.eQ = e6 := rfl
  rw [he, show ((3 : PowerSeries ℤ)) = (3 : ℕ) by norm_num, map_natCast, show ((2 : PowerSeries ℤ)) = (2 : ℕ) by norm_num,
    map_natCast]
  push_cast
  linear_combination h

/-- **Andrews–Garvan's combinatorial form**, conditional on `ThetaId`: for `n ≥ 1`,
`N(1,5,5n) − N(0,5,5n) = [qⁿ] χ₀`. -/
theorem rank_chi0_of (hΘ : ThetaId) (n : ℕ) (hn : 1 ≤ n) :
    (CrankProof.rankCount (5 * n) 1 : ℤ) - CrankProof.rankCount (5 * n) 0 = PowerSeries.coeff n MockTheta5.Formal.chi0 := by
  obtain ⟨h1, h2, -⟩ := CrankProof.rank_diff_mod5 n
  have hc := congrArg (PowerSeries.coeff n) (chi0_identity_of hΘ)
  simp only [map_sub, map_mul] at hc
  rw [show (5 * n + 0) = 5 * n by ring] at h1 h2
  have h2c : PowerSeries.coeff n (2 : PowerSeries ℤ) = 0 := by
    rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 by rfl, PowerSeries.coeff_C, if_neg (by omega)]
  have h3c : PowerSeries.coeff n ((3 : PowerSeries ℤ) * (RankProof.Phi 1 - 1)) = 3 * PowerSeries.coeff n (RankProof.Phi 1 - 1) := by
    rw [show (3 : PowerSeries ℤ) = PowerSeries.C 3 by rfl, PowerSeries.coeff_C_mul]
  rw [h2c, sub_zero] at hc
  rw [hc, h3c]
  push_cast at h1 h2 ⊢
  linarith
