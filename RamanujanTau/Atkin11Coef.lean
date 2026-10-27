/-
# Atkin 11^k: the certified theta identities in `ℤ⟦q⟧`

The certificates were checked at the theta point `cx` of `ℂ((t))`. At `t = q` (modulus `N = 11`) that point is
the image of `cPs` under the injective embedding `ιN`, so every certified identity holds at `cPs` in `ℤ⟦q⟧`.
We also identify the characteristic-polynomial coefficients `Ẽ_j = Q⁵e_j` (six variables) with
`Q^{5−k_j} F_j` (five variables).
-/
import RamanujanTau.Atkin11Norm
import RamanujanTau.Atkin11CertL

set_option autoImplicit false

namespace Atkin11
open PowerSeries ALz ALz11 MTC Atkin11Cert SPoly

lemma h11 : 1 ≤ 11 := by norm_num
lemma hd1 : 11 = 11 * 1 := by norm_num

lemma Jt1_ι (a : ℕ) (h0 : 1 ≤ a) (h1 : a < 11) :
    Jt h11 hd1 (a : ℤ) = ιN h1' (ηP a) * ιN h1' (RankProof.Pinf 11 11) := by
  have h := θ_eq_ιN_prod (d := 1) (a := 11) (b := a) h1' h0 h1 (by norm_num)
  rw [θ_congrN (show 1 * 11 = 11 by norm_num) _ h11] at h
  rw [ALz11.Jt, ← map_mul, ηP, show ((1 : ℕ) : ℤ) * (a : ℤ) = ((1 * a : ℕ) : ℤ) by push_cast; ring, h]

lemma ιN1_ne {a : ℕ} (h0 : 1 ≤ a) (h1 : a < 11) : ιN h1' (ηP a) ≠ 0 := ((isUnit_ηP h0 h1).map _).ne_zero

lemma cx_eq : cx h11 hd1 = cPs.map (ιN h1') := by
  have hB : ιN h1' (RankProof.Pinf 11 11) ≠ 0 :=
    ((RankProof.isUnit_Pinf 11 11 (by norm_num) (by norm_num)).map _).ne_zero
  have hQ : Qt hd1 = ιN h1' X := by rw [X_ι]; rfl
  have j1 := Jt1_ι 1 le_rfl (by norm_num)
  have j2 := Jt1_ι 2 (by norm_num) (by norm_num)
  have j3 := Jt1_ι 3 (by norm_num) (by norm_num)
  have j4 := Jt1_ι 4 (by norm_num) (by norm_num)
  have j5 := Jt1_ι 5 (by norm_num) (by norm_num)
  push_cast at j1 j2 j3 j4 j5
  have n1 := ιN1_ne (a := 1) le_rfl (by norm_num)
  have n2 := ιN1_ne (a := 2) (by norm_num) (by norm_num)
  have n3 := ιN1_ne (a := 3) (by norm_num) (by norm_num)
  have n4 := ιN1_ne (a := 4) (by norm_num) (by norm_num)
  have n5 := ιN1_ne (a := 5) (by norm_num) (by norm_num)
  simp only [cx, cPs, List.map_cons, List.map_nil, List.cons.injEq, and_true, cP0, cP1, cP2, cP4, cP7, map_mul,
    map_neg, ιN1_inv (isUnit_ηP (a := 1) le_rfl (by norm_num)), ιN1_inv (isUnit_ηP (a := 2) (by norm_num) (by norm_num)),
    ιN1_inv (isUnit_ηP (a := 3) (by norm_num) (by norm_num)), ιN1_inv (isUnit_ηP (a := 4) (by norm_num) (by norm_num)),
    ιN1_inv (isUnit_ηP (a := 5) (by norm_num) (by norm_num)), j1, j2, j3, j4, j5, hQ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- **pull-back**: a certified identity at the theta point holds at `cPs`. -/
lemma pull (e : PE) (h : e.eval (cx h11 hd1) = 0) : e.eval cPs = 0 :=
  PE.eval_eq_zero_of_map (ιN h1') (MTC.ιN_injective h1') cPs e (by rw [← cx_eq]; exact h)

/-! ### `Q` and the five-to-six-variable lift -/

/-- `Q^m = (−c₀c₁c₂c₄c₇)^m`. -/
def Qm (m : ℕ) : Poly := [(m * 1100586419201, (-1) ^ m)]

lemma Qm_eval (m : ℕ) (hm : m < 6) : evalP cPs (Qm m) = X ^ m := by
  have hd : dec (m * 1100586419201) = [m, m, m, m, m] := by
    interval_cases m <;> decide
  simp only [Qm, evalP, evalM, hd, evalL, cPs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    mul_one]
  push_cast
  rw [show (-1 : PS) ^ m * (cP0 ^ m * (cP1 ^ m * (cP2 ^ m * (cP4 ^ m * cP7 ^ m))))
      = (-(cP0 * cP1 * cP2 * cP4 * cP7)) ^ m by ring, prod_cP, neg_neg]

/-- a five-variable polynomial as a six-variable one with no `q`. -/
def lift (p : Poly) : SPoly6.Poly := p.map fun t => (t.1 * 1024, t.2)

lemma evalL6 (xs : List PS) (l : List ℕ) : SPoly6.evalL xs l = SPoly.evalL xs l := by
  induction xs generalizing l with
  | nil => cases l <;> simp [SPoly6.evalL, SPoly.evalL]
  | cons y ys ih => cases l <;> simp [SPoly6.evalL, SPoly.evalL, ih]

lemma evalP_lift (a : PS) (xs : List PS) (p : Poly) : SPoly6.evalP (a :: xs) (lift p) = evalP xs p := by
  induction p with
  | nil => simp [lift]
  | cons t p ih =>
    simp only [lift, List.map_cons] at ih ⊢
    rw [SPoly6.evalP_cons, evalP_cons, ih]
    congr 2
    have : SPoly6.dec (t.1 * 1024) = 0 :: dec t.1 := by
      simp only [SPoly6.dec, dec, List.cons.injEq, and_true]; omega
    rw [SPoly6.evalM, this, SPoly6.evalL, pow_zero, one_mul, evalL6, evalM]

lemma Et_def (p : SPoly6.Poly) : Et p = SPoly6.evalP (X :: cPs) p := rfl

lemma CH_E3_lift : SPoly6.certifyR [(lift (Qm 4), lift PF3)] CH_E3 = true := by
  decide +kernel
lemma CH_E4_lift : SPoly6.certifyR [(lift (Qm 4), lift PF4)] CH_E4 = true := by
  decide +kernel
lemma CH_E5_lift : SPoly6.certifyR [(lift (Qm 3), lift PF5)] CH_E5 = true := by
  decide +kernel
lemma CH_E6_lift : SPoly6.certifyR [(lift (Qm 3), lift PF6)] CH_E6 = true := by
  decide +kernel
lemma CH_E7_lift : SPoly6.certifyR [(lift (Qm 2), lift PF7)] CH_E7 = true := by
  decide +kernel
lemma CH_E8_lift : SPoly6.certifyR [(lift (Qm 2), lift PF8)] CH_E8 = true := by
  decide +kernel
lemma CH_E9_lift : SPoly6.certifyR [(lift (Qm 1), lift PF9)] CH_E9 = true := by
  decide +kernel
lemma CH_E10_lift : SPoly6.certifyR [(lift (Qm 1), lift PF10)] CH_E10 = true := by
  decide +kernel
lemma CH_E11_lift : SPoly6.certifyR [(lift (Qm 0), lift PF11)] CH_E11 = true := by
  decide +kernel

lemma CH_E1_lift : SPoly6.certifyR [(lift (Qm 5), [(0, 11)])] CH_E1 = true := by decide +kernel
lemma CH_E2_lift : SPoly6.certifyR [(lift (Qm 5), [(0, 55)])] CH_E2 = true := by decide +kernel

lemma Et_E3 : Et CH_E3 = X ^ 4 * evalP cPs PF3 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E3_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 4 < 6)]

lemma Et_E4 : Et CH_E4 = X ^ 4 * evalP cPs PF4 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E4_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 4 < 6)]

lemma Et_E5 : Et CH_E5 = X ^ 3 * evalP cPs PF5 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E5_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 3 < 6)]

lemma Et_E6 : Et CH_E6 = X ^ 3 * evalP cPs PF6 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E6_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 3 < 6)]

lemma Et_E7 : Et CH_E7 = X ^ 2 * evalP cPs PF7 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E7_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 2 < 6)]

lemma Et_E8 : Et CH_E8 = X ^ 2 * evalP cPs PF8 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E8_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 2 < 6)]

lemma Et_E9 : Et CH_E9 = X ^ 1 * evalP cPs PF9 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E9_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 1 < 6)]

lemma Et_E10 : Et CH_E10 = X ^ 1 * evalP cPs PF10 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E10_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 1 < 6)]

lemma Et_E11 : Et CH_E11 = X ^ 0 * evalP cPs PF11 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E11_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 0 < 6)]

lemma Et_E1 : Et CH_E1 = X ^ 5 * 11 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E1_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 5 < 6)]
  simp [SPoly6.evalP, SPoly6.evalM, SPoly6.dec, SPoly6.evalL, cPs]

lemma Et_E2 : Et CH_E2 = X ^ 5 * 55 := by
  rw [Et_def, SPoly6.certifyR_sound _ _ _ CH_E2_lift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, evalP_lift,
    Qm_eval _ (by norm_num : 5 < 6)]
  simp [SPoly6.evalP, SPoly6.evalM, SPoly6.dec, SPoly6.evalL, cPs]

end Atkin11
