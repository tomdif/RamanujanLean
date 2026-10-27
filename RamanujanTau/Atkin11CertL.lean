/-
# Atkin 11^k: the certified theta identities at the theta point

For each certified identity `X`: the Gröbner certificate (single check, or a tree of unit products and
partial sums) and the vanishing of the Gröbner basis at the theta point give `X_T(c) = 0`; the meaning check
(`X_mean`) turns this into the cleared identity `eX.eval c = 0`.
-/
import RamanujanTau.Atkin11CertEval
import RamanujanTau.SPolyFast
import RamanujanTau.Atkin11Cert.E3Mean
import RamanujanTau.Atkin11Cert.E4Mean
import RamanujanTau.Atkin11Cert.M6Mean
import RamanujanTau.Atkin11Cert.M5Mean
import RamanujanTau.Atkin11Cert.M4Mean
import RamanujanTau.Atkin11Cert.M3Mean
import RamanujanTau.Atkin11Cert.M2Mean
import RamanujanTau.Atkin11Cert.M1Mean
import RamanujanTau.Atkin11Cert.QUMean

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ALz11
open HahnSeries ALz SPoly Atkin11Cert

section Ident
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 11 * d)
include hN hd

lemma cx_ne : ∀ v ∈ cx hN hd, v ≠ 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  intro v hv
  simp only [cx, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact div_ne_zero h4 h2
  · exact neg_ne_zero.mpr (div_ne_zero h2 h1)
  · exact neg_ne_zero.mpr (div_ne_zero h5 h3)
  · exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hQ h1) h5)
  · exact div_ne_zero h3 h4

omit hN hd in
lemma evalL_ne (x : List L) (hx : ∀ v ∈ x, v ≠ 0) : ∀ e : List ℕ, evalL x e ≠ 0 := by
  induction x with
  | nil => intro e; simp [evalL]
  | cons y ys ih =>
    intro e
    cases e with
    | nil => simp [evalL]
    | cons a es =>
      simp only [evalL]
      exact mul_ne_zero (pow_ne_zero _ (hx y (List.mem_cons_self ..)))
        (ih (fun v hv => hx v (List.mem_cons_of_mem _ hv)) es)

lemma evalM_cx_ne (m : ℕ) : evalM (cx hN hd) m ≠ 0 := evalL_ne _ (cx_ne hN hd) _

theorem E3_eval : eE3.eval (cx hN hd) = 0 := by
  have hT0 : evalP (cx hN hd) (mulTerm 1100586419201 1 E3_T) = 0 := by
    rw [certify_sound _ _ _ E3_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [evalP_mulTerm _ _ _ _ (by decide +kernel)] at hT0
  have hT : evalP (cx hN hd) E3_T = 0 := by
    rcases mul_eq_zero.mp hT0 with h | h
    · exact absurd h (by simpa using evalM_cx_ne hN hd 1100586419201)
    · exact h
  rw [← eqCheckPE_sound _ _ _ E3_mean, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

theorem E4_eval : eE4.eval (cx hN hd) = 0 := by
  have hT0 : evalP (cx hN hd) (mulTerm 1100586419201 1 E4_T) = 0 := by
    rw [certify_sound _ _ _ E4_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [evalP_mulTerm _ _ _ _ (by decide +kernel)] at hT0
  have hT : evalP (cx hN hd) E4_T = 0 := by
    rcases mul_eq_zero.mp hT0 with h | h
    · exact absurd h (by simpa using evalM_cx_ne hN hd 1100586419201)
    · exact h
  rw [← eqCheckPE_sound _ _ _ E4_mean, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

theorem M6_eval : eM6.eval (cx hN hd) = 0 := by
  have hT : evalP (cx hN hd) M6_T = 0 := by
    rw [certify_sound _ _ _ M6_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [← eqCheckPE_sound _ _ _ M6_mean, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

theorem M5_eval : eM5.eval (cx hN hd) = 0 := by
  have hT : evalP (cx hN hd) M5_T = 0 := by
    rw [certify_sound _ _ _ M5_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [← eqCheckPE_sound _ _ _ M5_mean, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

theorem M4_eval : eM4.eval (cx hN hd) = 0 := by
  have hT : evalP (cx hN hd) M4_T = 0 := by
    rw [certify_sound _ _ _ M4_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [← eqCheckPE_sound _ _ _ M4_mean, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

theorem M3_eval : eM3.eval (cx hN hd) = 0 := by
  have hT : evalP (cx hN hd) M3_T = 0 := by
    rw [certify_sound _ _ _ M3_ok]
    simp [G1_zero hN hd, G2_zero hN hd, G3_zero hN hd, G4_zero hN hd, G5_zero hN hd, G6_zero hN hd, G7_zero hN hd, G8_zero hN hd, G9_zero hN hd, G10_zero hN hd, G11_zero hN hd, G12_zero hN hd, G13_zero hN hd, G14_zero hN hd, G15_zero hN hd, G16_zero hN hd, G17_zero hN hd, G18_zero hN hd, G19_zero hN hd, G20_zero hN hd, G21_zero hN hd, G22_zero hN hd, G23_zero hN hd, G24_zero hN hd, G25_zero hN hd]
  rw [← M3_meanE, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

lemma M2_R0_zero : evalP (cx hN hd) M2_R0 = 0 := by
  rw [certifyR_sound _ _ _ M2_R0_ok]; simp [G1_zero hN hd]

lemma M2_R1_zero : evalP (cx hN hd) M2_R1 = 0 := by
  rw [certifyR_sound _ _ _ M2_R1_ok]; simp [G1_zero hN hd]

lemma M2_R2_zero : evalP (cx hN hd) M2_R2 = 0 := by
  rw [certifyR_sound _ _ _ M2_R2_ok]; simp [G1_zero hN hd]

lemma M2_R3_zero : evalP (cx hN hd) M2_R3 = 0 := by
  rw [certifyR_sound _ _ _ M2_R3_ok]; simp [G1_zero hN hd]

lemma M2_R4_zero : evalP (cx hN hd) M2_R4 = 0 := by
  rw [certifyR_sound _ _ _ M2_R4_ok]; simp [G1_zero hN hd]

lemma M2_R5_zero : evalP (cx hN hd) M2_R5 = 0 := by
  rw [certifyR_sound _ _ _ M2_R5_ok]; simp [G1_zero hN hd]

lemma M2_R6_zero : evalP (cx hN hd) M2_R6 = 0 := by
  rw [certifyR_sound _ _ _ M2_R6_ok]; simp [G1_zero hN hd]

lemma M2_R7_zero : evalP (cx hN hd) M2_R7 = 0 := by
  rw [certifyR_sound _ _ _ M2_R7_ok]; simp [G1_zero hN hd]

lemma M2_R8_zero : evalP (cx hN hd) M2_R8 = 0 := by
  rw [certifyR_sound _ _ _ M2_R8_ok]; simp [G2_zero hN hd]

lemma M2_R9_zero : evalP (cx hN hd) M2_R9 = 0 := by
  rw [certifyR_sound _ _ _ M2_R9_ok]; simp [G3_zero hN hd]

lemma M2_R10_zero : evalP (cx hN hd) M2_R10 = 0 := by
  rw [certifyR_sound _ _ _ M2_R10_ok]; simp [G4_zero hN hd]

lemma M2_R11_zero : evalP (cx hN hd) M2_R11 = 0 := by
  rw [certifyR_sound _ _ _ M2_R11_ok]; simp [G5_zero hN hd]

lemma M2_R12_zero : evalP (cx hN hd) M2_R12 = 0 := by
  rw [certifyR_sound _ _ _ M2_R12_ok]; simp [G8_zero hN hd]

lemma M2_R13_zero : evalP (cx hN hd) M2_R13 = 0 := by
  rw [certifyR_sound _ _ _ M2_R13_ok]; simp [G10_zero hN hd]

lemma M2_R14_zero : evalP (cx hN hd) M2_R14 = 0 := by
  rw [certifyR_sound _ _ _ M2_R14_ok]; simp [G11_zero hN hd]

lemma M2_R15_zero : evalP (cx hN hd) M2_R15 = 0 := by
  rw [certifyR_sound _ _ _ M2_R15_ok]; simp [G13_zero hN hd]

lemma M2_R16_zero : evalP (cx hN hd) M2_R16 = 0 := by
  rw [certifyR_sound _ _ _ M2_R16_ok]; simp [G14_zero hN hd]

lemma M2_R17_zero : evalP (cx hN hd) M2_R17 = 0 := by
  rw [certifyR_sound _ _ _ M2_R17_ok]; simp [G16_zero hN hd]

lemma M2_R18_zero : evalP (cx hN hd) M2_R18 = 0 := by
  rw [certifyR_sound _ _ _ M2_R18_ok]; simp [G18_zero hN hd]

lemma M2_R19_zero : evalP (cx hN hd) M2_R19 = 0 := by
  rw [certifyR_sound _ _ _ M2_R19_ok]; simp [G19_zero hN hd]

lemma M2_R20_zero : evalP (cx hN hd) M2_R20 = 0 := by
  rw [certifyR_sound _ _ _ M2_R20_ok]; simp [G20_zero hN hd]

lemma M2_R21_zero : evalP (cx hN hd) M2_R21 = 0 := by
  rw [certifyR_sound _ _ _ M2_R21_ok]; simp [G21_zero hN hd]

lemma M2_R22_zero : evalP (cx hN hd) M2_R22 = 0 := by
  rw [certifyR_sound _ _ _ M2_R22_ok]; simp [G22_zero hN hd]

lemma M2_R23_zero : evalP (cx hN hd) M2_R23 = 0 := by
  rw [certifyR_sound _ _ _ M2_R23_ok]; simp [G23_zero hN hd]

lemma M2_R24_zero : evalP (cx hN hd) M2_R24 = 0 := by
  rw [certifyR_sound _ _ _ M2_R24_ok]; simp [G25_zero hN hd]

lemma M2_S0_0_zero : evalP (cx hN hd) M2_S0_0 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_0_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R0_zero hN hd, M2_R1_zero hN hd, M2_R2_zero hN hd, M2_R3_zero hN hd, add_zero]

lemma M2_S0_1_zero : evalP (cx hN hd) M2_S0_1 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_1_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R4_zero hN hd, M2_R5_zero hN hd, M2_R6_zero hN hd, M2_R7_zero hN hd, add_zero]

lemma M2_S0_2_zero : evalP (cx hN hd) M2_S0_2 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_2_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R8_zero hN hd, M2_R9_zero hN hd, M2_R10_zero hN hd, M2_R11_zero hN hd, add_zero]

lemma M2_S0_3_zero : evalP (cx hN hd) M2_S0_3 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_3_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R12_zero hN hd, M2_R13_zero hN hd, M2_R14_zero hN hd, M2_R15_zero hN hd, add_zero]

lemma M2_S0_4_zero : evalP (cx hN hd) M2_S0_4 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_4_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R16_zero hN hd, M2_R17_zero hN hd, M2_R18_zero hN hd, M2_R19_zero hN hd, add_zero]

lemma M2_S0_5_zero : evalP (cx hN hd) M2_S0_5 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_5_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R20_zero hN hd, M2_R21_zero hN hd, M2_R22_zero hN hd, M2_R23_zero hN hd, add_zero]

lemma M2_S0_6_zero : evalP (cx hN hd) M2_S0_6 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S0_6_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_R24_zero hN hd, add_zero]

lemma M2_S1_0_zero : evalP (cx hN hd) M2_S1_0 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S1_0_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_S0_0_zero hN hd, M2_S0_1_zero hN hd, M2_S0_2_zero hN hd, M2_S0_3_zero hN hd, add_zero]

lemma M2_S1_1_zero : evalP (cx hN hd) M2_S1_1 = 0 := by
  rw [eqRuns_sound _ _ _ M2_S1_1_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_S0_4_zero hN hd, M2_S0_5_zero hN hd, M2_S0_6_zero hN hd, add_zero]

lemma M2_root_zero : evalP (cx hN hd) M2_root = 0 := by
  rw [eqRuns_sound _ _ _ M2_root_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M2_S1_0_zero hN hd, M2_S1_1_zero hN hd, add_zero]

theorem M2_eval : eM2.eval (cx hN hd) = 0 := by
  rw [← M2_meanE, evalP_mulTerm _ _ _ _ (by decide +kernel), M2_root_zero hN hd, mul_zero]

lemma M1_R0_zero : evalP (cx hN hd) M1_R0 = 0 := by
  rw [certifyR_sound _ _ _ M1_R0_ok]; simp [G1_zero hN hd]

lemma M1_R1_zero : evalP (cx hN hd) M1_R1 = 0 := by
  rw [certifyR_sound _ _ _ M1_R1_ok]; simp [G1_zero hN hd]

lemma M1_R2_zero : evalP (cx hN hd) M1_R2 = 0 := by
  rw [certifyR_sound _ _ _ M1_R2_ok]; simp [G1_zero hN hd]

lemma M1_R3_zero : evalP (cx hN hd) M1_R3 = 0 := by
  rw [certifyR_sound _ _ _ M1_R3_ok]; simp [G1_zero hN hd]

lemma M1_R4_zero : evalP (cx hN hd) M1_R4 = 0 := by
  rw [certifyR_sound _ _ _ M1_R4_ok]; simp [G1_zero hN hd]

lemma M1_R5_zero : evalP (cx hN hd) M1_R5 = 0 := by
  rw [certifyR_sound _ _ _ M1_R5_ok]; simp [G1_zero hN hd]

lemma M1_R6_zero : evalP (cx hN hd) M1_R6 = 0 := by
  rw [certifyR_sound _ _ _ M1_R6_ok]; simp [G1_zero hN hd]

lemma M1_R7_zero : evalP (cx hN hd) M1_R7 = 0 := by
  rw [certifyR_sound _ _ _ M1_R7_ok]; simp [G1_zero hN hd]

lemma M1_R8_zero : evalP (cx hN hd) M1_R8 = 0 := by
  rw [certifyR_sound _ _ _ M1_R8_ok]; simp [G2_zero hN hd]

lemma M1_R9_zero : evalP (cx hN hd) M1_R9 = 0 := by
  rw [certifyR_sound _ _ _ M1_R9_ok]; simp [G3_zero hN hd]

lemma M1_R10_zero : evalP (cx hN hd) M1_R10 = 0 := by
  rw [certifyR_sound _ _ _ M1_R10_ok]; simp [G4_zero hN hd]

lemma M1_R11_zero : evalP (cx hN hd) M1_R11 = 0 := by
  rw [certifyR_sound _ _ _ M1_R11_ok]; simp [G5_zero hN hd]

lemma M1_R12_zero : evalP (cx hN hd) M1_R12 = 0 := by
  rw [certifyR_sound _ _ _ M1_R12_ok]; simp [G8_zero hN hd]

lemma M1_R13_zero : evalP (cx hN hd) M1_R13 = 0 := by
  rw [certifyR_sound _ _ _ M1_R13_ok]; simp [G10_zero hN hd]

lemma M1_R14_zero : evalP (cx hN hd) M1_R14 = 0 := by
  rw [certifyR_sound _ _ _ M1_R14_ok]; simp [G11_zero hN hd]

lemma M1_R15_zero : evalP (cx hN hd) M1_R15 = 0 := by
  rw [certifyR_sound _ _ _ M1_R15_ok]; simp [G13_zero hN hd]

lemma M1_R16_zero : evalP (cx hN hd) M1_R16 = 0 := by
  rw [certifyR_sound _ _ _ M1_R16_ok]; simp [G14_zero hN hd]

lemma M1_R17_zero : evalP (cx hN hd) M1_R17 = 0 := by
  rw [certifyR_sound _ _ _ M1_R17_ok]; simp [G16_zero hN hd]

lemma M1_R18_zero : evalP (cx hN hd) M1_R18 = 0 := by
  rw [certifyR_sound _ _ _ M1_R18_ok]; simp [G18_zero hN hd]

lemma M1_R19_zero : evalP (cx hN hd) M1_R19 = 0 := by
  rw [certifyR_sound _ _ _ M1_R19_ok]; simp [G19_zero hN hd]

lemma M1_R20_zero : evalP (cx hN hd) M1_R20 = 0 := by
  rw [certifyR_sound _ _ _ M1_R20_ok]; simp [G20_zero hN hd]

lemma M1_R21_zero : evalP (cx hN hd) M1_R21 = 0 := by
  rw [certifyR_sound _ _ _ M1_R21_ok]; simp [G21_zero hN hd]

lemma M1_R22_zero : evalP (cx hN hd) M1_R22 = 0 := by
  rw [certifyR_sound _ _ _ M1_R22_ok]; simp [G22_zero hN hd]

lemma M1_R23_zero : evalP (cx hN hd) M1_R23 = 0 := by
  rw [certifyR_sound _ _ _ M1_R23_ok]; simp [G23_zero hN hd]

lemma M1_R24_zero : evalP (cx hN hd) M1_R24 = 0 := by
  rw [certifyR_sound _ _ _ M1_R24_ok]; simp [G25_zero hN hd]

lemma M1_S0_0_zero : evalP (cx hN hd) M1_S0_0 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_0_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R0_zero hN hd, M1_R1_zero hN hd, M1_R2_zero hN hd, M1_R3_zero hN hd, add_zero]

lemma M1_S0_1_zero : evalP (cx hN hd) M1_S0_1 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_1_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R4_zero hN hd, M1_R5_zero hN hd, M1_R6_zero hN hd, M1_R7_zero hN hd, add_zero]

lemma M1_S0_2_zero : evalP (cx hN hd) M1_S0_2 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_2_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R8_zero hN hd, M1_R9_zero hN hd, M1_R10_zero hN hd, M1_R11_zero hN hd, add_zero]

lemma M1_S0_3_zero : evalP (cx hN hd) M1_S0_3 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_3_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R12_zero hN hd, M1_R13_zero hN hd, M1_R14_zero hN hd, M1_R15_zero hN hd, add_zero]

lemma M1_S0_4_zero : evalP (cx hN hd) M1_S0_4 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_4_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R16_zero hN hd, M1_R17_zero hN hd, M1_R18_zero hN hd, M1_R19_zero hN hd, add_zero]

lemma M1_S0_5_zero : evalP (cx hN hd) M1_S0_5 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_5_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R20_zero hN hd, M1_R21_zero hN hd, M1_R22_zero hN hd, M1_R23_zero hN hd, add_zero]

lemma M1_S0_6_zero : evalP (cx hN hd) M1_S0_6 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S0_6_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_R24_zero hN hd, add_zero]

lemma M1_S1_0_zero : evalP (cx hN hd) M1_S1_0 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S1_0_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_S0_0_zero hN hd, M1_S0_1_zero hN hd, M1_S0_2_zero hN hd, M1_S0_3_zero hN hd, add_zero]

lemma M1_S1_1_zero : evalP (cx hN hd) M1_S1_1 = 0 := by
  rw [eqRuns_sound _ _ _ M1_S1_1_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_S0_4_zero hN hd, M1_S0_5_zero hN hd, M1_S0_6_zero hN hd, add_zero]

lemma M1_root_zero : evalP (cx hN hd) M1_root = 0 := by
  rw [eqRuns_sound _ _ _ M1_root_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, M1_S1_0_zero hN hd, M1_S1_1_zero hN hd, add_zero]

theorem M1_eval : eM1.eval (cx hN hd) = 0 := by
  rw [← M1_meanE, evalP_mulTerm _ _ _ _ (by decide +kernel), M1_root_zero hN hd, mul_zero]

lemma QU_R0_zero : evalP (cx hN hd) QU_R0 = 0 := by
  rw [certify_sound _ _ _ QU_R0_ok]; simp [G1_zero hN hd]

lemma QU_R1_zero : evalP (cx hN hd) QU_R1 = 0 := by
  rw [certify_sound _ _ _ QU_R1_ok]; simp [G1_zero hN hd]

lemma QU_R2_zero : evalP (cx hN hd) QU_R2 = 0 := by
  rw [certify_sound _ _ _ QU_R2_ok]; simp [G1_zero hN hd]

lemma QU_R3_zero : evalP (cx hN hd) QU_R3 = 0 := by
  rw [certify_sound _ _ _ QU_R3_ok]; simp [G1_zero hN hd]

lemma QU_R4_zero : evalP (cx hN hd) QU_R4 = 0 := by
  rw [certify_sound _ _ _ QU_R4_ok]; simp [G1_zero hN hd]

lemma QU_R5_zero : evalP (cx hN hd) QU_R5 = 0 := by
  rw [certify_sound _ _ _ QU_R5_ok]; simp [G1_zero hN hd]

lemma QU_R6_zero : evalP (cx hN hd) QU_R6 = 0 := by
  rw [certify_sound _ _ _ QU_R6_ok]; simp [G1_zero hN hd]

lemma QU_R7_zero : evalP (cx hN hd) QU_R7 = 0 := by
  rw [certify_sound _ _ _ QU_R7_ok]; simp [G1_zero hN hd]

lemma QU_R8_zero : evalP (cx hN hd) QU_R8 = 0 := by
  rw [certify_sound _ _ _ QU_R8_ok]; simp [G1_zero hN hd]

lemma QU_R9_zero : evalP (cx hN hd) QU_R9 = 0 := by
  rw [certify_sound _ _ _ QU_R9_ok]; simp [G1_zero hN hd]

lemma QU_R10_zero : evalP (cx hN hd) QU_R10 = 0 := by
  rw [certify_sound _ _ _ QU_R10_ok]; simp [G1_zero hN hd]

lemma QU_R11_zero : evalP (cx hN hd) QU_R11 = 0 := by
  rw [certify_sound _ _ _ QU_R11_ok]; simp [G1_zero hN hd]

lemma QU_R12_zero : evalP (cx hN hd) QU_R12 = 0 := by
  rw [certify_sound _ _ _ QU_R12_ok]; simp [G1_zero hN hd]

lemma QU_R13_zero : evalP (cx hN hd) QU_R13 = 0 := by
  rw [certify_sound _ _ _ QU_R13_ok]; simp [G1_zero hN hd]

lemma QU_R14_zero : evalP (cx hN hd) QU_R14 = 0 := by
  rw [certify_sound _ _ _ QU_R14_ok]; simp [G1_zero hN hd]

lemma QU_R15_zero : evalP (cx hN hd) QU_R15 = 0 := by
  rw [certify_sound _ _ _ QU_R15_ok]; simp [G1_zero hN hd]

lemma QU_R16_zero : evalP (cx hN hd) QU_R16 = 0 := by
  rw [certify_sound _ _ _ QU_R16_ok]; simp [G1_zero hN hd]

lemma QU_R17_zero : evalP (cx hN hd) QU_R17 = 0 := by
  rw [certify_sound _ _ _ QU_R17_ok]; simp [G1_zero hN hd]

lemma QU_R18_zero : evalP (cx hN hd) QU_R18 = 0 := by
  rw [certify_sound _ _ _ QU_R18_ok]; simp [G1_zero hN hd]

lemma QU_R19_zero : evalP (cx hN hd) QU_R19 = 0 := by
  rw [certify_sound _ _ _ QU_R19_ok]; simp [G1_zero hN hd]

lemma QU_R20_zero : evalP (cx hN hd) QU_R20 = 0 := by
  rw [certify_sound _ _ _ QU_R20_ok]; simp [G1_zero hN hd]

lemma QU_R21_zero : evalP (cx hN hd) QU_R21 = 0 := by
  rw [certify_sound _ _ _ QU_R21_ok]; simp [G1_zero hN hd]

lemma QU_R22_zero : evalP (cx hN hd) QU_R22 = 0 := by
  rw [certify_sound _ _ _ QU_R22_ok]; simp [G1_zero hN hd]

lemma QU_R23_zero : evalP (cx hN hd) QU_R23 = 0 := by
  rw [certify_sound _ _ _ QU_R23_ok]; simp [G1_zero hN hd]

lemma QU_R24_zero : evalP (cx hN hd) QU_R24 = 0 := by
  rw [certify_sound _ _ _ QU_R24_ok]; simp [G1_zero hN hd]

lemma QU_R25_zero : evalP (cx hN hd) QU_R25 = 0 := by
  rw [certify_sound _ _ _ QU_R25_ok]; simp [G1_zero hN hd]

lemma QU_R26_zero : evalP (cx hN hd) QU_R26 = 0 := by
  rw [certify_sound _ _ _ QU_R26_ok]; simp [G1_zero hN hd]

lemma QU_R27_zero : evalP (cx hN hd) QU_R27 = 0 := by
  rw [certify_sound _ _ _ QU_R27_ok]; simp [G1_zero hN hd]

lemma QU_R28_zero : evalP (cx hN hd) QU_R28 = 0 := by
  rw [certify_sound _ _ _ QU_R28_ok]; simp [G1_zero hN hd]

lemma QU_R29_zero : evalP (cx hN hd) QU_R29 = 0 := by
  rw [certify_sound _ _ _ QU_R29_ok]; simp [G1_zero hN hd]

lemma QU_R30_zero : evalP (cx hN hd) QU_R30 = 0 := by
  rw [certify_sound _ _ _ QU_R30_ok]; simp [G1_zero hN hd]

lemma QU_R31_zero : evalP (cx hN hd) QU_R31 = 0 := by
  rw [certify_sound _ _ _ QU_R31_ok]; simp [G1_zero hN hd]

lemma QU_R32_zero : evalP (cx hN hd) QU_R32 = 0 := by
  rw [certify_sound _ _ _ QU_R32_ok]; simp [G1_zero hN hd]

lemma QU_R33_zero : evalP (cx hN hd) QU_R33 = 0 := by
  rw [certify_sound _ _ _ QU_R33_ok]; simp [G1_zero hN hd]

lemma QU_R34_zero : evalP (cx hN hd) QU_R34 = 0 := by
  rw [certify_sound _ _ _ QU_R34_ok]; simp [G1_zero hN hd]

lemma QU_R35_zero : evalP (cx hN hd) QU_R35 = 0 := by
  rw [certify_sound _ _ _ QU_R35_ok]; simp [G1_zero hN hd]

lemma QU_R36_zero : evalP (cx hN hd) QU_R36 = 0 := by
  rw [certify_sound _ _ _ QU_R36_ok]; simp [G1_zero hN hd]

lemma QU_R37_zero : evalP (cx hN hd) QU_R37 = 0 := by
  rw [certify_sound _ _ _ QU_R37_ok]; simp [G1_zero hN hd]

lemma QU_R38_zero : evalP (cx hN hd) QU_R38 = 0 := by
  rw [certify_sound _ _ _ QU_R38_ok]; simp [G1_zero hN hd]

lemma QU_R39_zero : evalP (cx hN hd) QU_R39 = 0 := by
  rw [certify_sound _ _ _ QU_R39_ok]; simp [G1_zero hN hd]

lemma QU_R40_zero : evalP (cx hN hd) QU_R40 = 0 := by
  rw [certify_sound _ _ _ QU_R40_ok]; simp [G1_zero hN hd]

lemma QU_R41_zero : evalP (cx hN hd) QU_R41 = 0 := by
  rw [certify_sound _ _ _ QU_R41_ok]; simp [G1_zero hN hd]

lemma QU_R42_zero : evalP (cx hN hd) QU_R42 = 0 := by
  rw [certify_sound _ _ _ QU_R42_ok]; simp [G1_zero hN hd]

lemma QU_R43_zero : evalP (cx hN hd) QU_R43 = 0 := by
  rw [certify_sound _ _ _ QU_R43_ok]; simp [G2_zero hN hd]

lemma QU_R44_zero : evalP (cx hN hd) QU_R44 = 0 := by
  rw [certify_sound _ _ _ QU_R44_ok]; simp [G3_zero hN hd]

lemma QU_R45_zero : evalP (cx hN hd) QU_R45 = 0 := by
  rw [certify_sound _ _ _ QU_R45_ok]; simp [G3_zero hN hd]

lemma QU_R46_zero : evalP (cx hN hd) QU_R46 = 0 := by
  rw [certify_sound _ _ _ QU_R46_ok]; simp [G3_zero hN hd]

lemma QU_R47_zero : evalP (cx hN hd) QU_R47 = 0 := by
  rw [certify_sound _ _ _ QU_R47_ok]; simp [G4_zero hN hd]

lemma QU_R48_zero : evalP (cx hN hd) QU_R48 = 0 := by
  rw [certify_sound _ _ _ QU_R48_ok]; simp [G5_zero hN hd]

lemma QU_R49_zero : evalP (cx hN hd) QU_R49 = 0 := by
  rw [certify_sound _ _ _ QU_R49_ok]; simp [G6_zero hN hd]

lemma QU_R50_zero : evalP (cx hN hd) QU_R50 = 0 := by
  rw [certify_sound _ _ _ QU_R50_ok]; simp [G8_zero hN hd]

lemma QU_R51_zero : evalP (cx hN hd) QU_R51 = 0 := by
  rw [certify_sound _ _ _ QU_R51_ok]; simp [G10_zero hN hd]

lemma QU_R52_zero : evalP (cx hN hd) QU_R52 = 0 := by
  rw [certify_sound _ _ _ QU_R52_ok]; simp [G11_zero hN hd]

lemma QU_R53_zero : evalP (cx hN hd) QU_R53 = 0 := by
  rw [certify_sound _ _ _ QU_R53_ok]; simp [G11_zero hN hd]

lemma QU_R54_zero : evalP (cx hN hd) QU_R54 = 0 := by
  rw [certify_sound _ _ _ QU_R54_ok]; simp [G13_zero hN hd]

lemma QU_R55_zero : evalP (cx hN hd) QU_R55 = 0 := by
  rw [certify_sound _ _ _ QU_R55_ok]; simp [G14_zero hN hd]

lemma QU_R56_zero : evalP (cx hN hd) QU_R56 = 0 := by
  rw [certify_sound _ _ _ QU_R56_ok]; simp [G16_zero hN hd]

lemma QU_R57_zero : evalP (cx hN hd) QU_R57 = 0 := by
  rw [certify_sound _ _ _ QU_R57_ok]; simp [G18_zero hN hd]

lemma QU_R58_zero : evalP (cx hN hd) QU_R58 = 0 := by
  rw [certify_sound _ _ _ QU_R58_ok]; simp [G19_zero hN hd]

lemma QU_R59_zero : evalP (cx hN hd) QU_R59 = 0 := by
  rw [certify_sound _ _ _ QU_R59_ok]; simp [G20_zero hN hd]

lemma QU_R60_zero : evalP (cx hN hd) QU_R60 = 0 := by
  rw [certify_sound _ _ _ QU_R60_ok]; simp [G21_zero hN hd]

lemma QU_R61_zero : evalP (cx hN hd) QU_R61 = 0 := by
  rw [certify_sound _ _ _ QU_R61_ok]; simp [G22_zero hN hd]

lemma QU_R62_zero : evalP (cx hN hd) QU_R62 = 0 := by
  rw [certify_sound _ _ _ QU_R62_ok]; simp [G23_zero hN hd]

lemma QU_R63_zero : evalP (cx hN hd) QU_R63 = 0 := by
  rw [certify_sound _ _ _ QU_R63_ok]; simp [G25_zero hN hd]

lemma QU_S0_0_zero : evalP (cx hN hd) QU_S0_0 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_0_ok]
  simp only [evalP_append, QU_R0_zero hN hd, QU_R1_zero hN hd, QU_R2_zero hN hd, QU_R3_zero hN hd, add_zero]

lemma QU_S0_1_zero : evalP (cx hN hd) QU_S0_1 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_1_ok]
  simp only [evalP_append, QU_R4_zero hN hd, QU_R5_zero hN hd, QU_R6_zero hN hd, QU_R7_zero hN hd, add_zero]

lemma QU_S0_2_zero : evalP (cx hN hd) QU_S0_2 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_2_ok]
  simp only [evalP_append, QU_R8_zero hN hd, QU_R9_zero hN hd, QU_R10_zero hN hd, QU_R11_zero hN hd, add_zero]

lemma QU_S0_3_zero : evalP (cx hN hd) QU_S0_3 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_3_ok]
  simp only [evalP_append, QU_R12_zero hN hd, QU_R13_zero hN hd, QU_R14_zero hN hd, QU_R15_zero hN hd, add_zero]

lemma QU_S0_4_zero : evalP (cx hN hd) QU_S0_4 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_4_ok]
  simp only [evalP_append, QU_R16_zero hN hd, QU_R17_zero hN hd, QU_R18_zero hN hd, QU_R19_zero hN hd, add_zero]

lemma QU_S0_5_zero : evalP (cx hN hd) QU_S0_5 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_5_ok]
  simp only [evalP_append, QU_R20_zero hN hd, QU_R21_zero hN hd, QU_R22_zero hN hd, QU_R23_zero hN hd, add_zero]

lemma QU_S0_6_zero : evalP (cx hN hd) QU_S0_6 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_6_ok]
  simp only [evalP_append, QU_R24_zero hN hd, QU_R25_zero hN hd, QU_R26_zero hN hd, QU_R27_zero hN hd, add_zero]

lemma QU_S0_7_zero : evalP (cx hN hd) QU_S0_7 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_7_ok]
  simp only [evalP_append, QU_R28_zero hN hd, QU_R29_zero hN hd, QU_R30_zero hN hd, QU_R31_zero hN hd, add_zero]

lemma QU_S0_8_zero : evalP (cx hN hd) QU_S0_8 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_8_ok]
  simp only [evalP_append, QU_R32_zero hN hd, QU_R33_zero hN hd, QU_R34_zero hN hd, QU_R35_zero hN hd, add_zero]

lemma QU_S0_9_zero : evalP (cx hN hd) QU_S0_9 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_9_ok]
  simp only [evalP_append, QU_R36_zero hN hd, QU_R37_zero hN hd, QU_R38_zero hN hd, QU_R39_zero hN hd, add_zero]

lemma QU_S0_10_zero : evalP (cx hN hd) QU_S0_10 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_10_ok]
  simp only [evalP_append, QU_R40_zero hN hd, QU_R41_zero hN hd, QU_R42_zero hN hd, QU_R43_zero hN hd, add_zero]

lemma QU_S0_11_zero : evalP (cx hN hd) QU_S0_11 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_11_ok]
  simp only [evalP_append, QU_R44_zero hN hd, QU_R45_zero hN hd, QU_R46_zero hN hd, QU_R47_zero hN hd, add_zero]

lemma QU_S0_12_zero : evalP (cx hN hd) QU_S0_12 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_12_ok]
  simp only [evalP_append, QU_R48_zero hN hd, QU_R49_zero hN hd, QU_R50_zero hN hd, QU_R51_zero hN hd, add_zero]

lemma QU_S0_13_zero : evalP (cx hN hd) QU_S0_13 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_13_ok]
  simp only [evalP_append, QU_R52_zero hN hd, QU_R53_zero hN hd, QU_R54_zero hN hd, QU_R55_zero hN hd, add_zero]

lemma QU_S0_14_zero : evalP (cx hN hd) QU_S0_14 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_14_ok]
  simp only [evalP_append, QU_R56_zero hN hd, QU_R57_zero hN hd, QU_R58_zero hN hd, QU_R59_zero hN hd, add_zero]

lemma QU_S0_15_zero : evalP (cx hN hd) QU_S0_15 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S0_15_ok]
  simp only [evalP_append, QU_R60_zero hN hd, QU_R61_zero hN hd, QU_R62_zero hN hd, QU_R63_zero hN hd, add_zero]

lemma QU_S1_0_zero : evalP (cx hN hd) QU_S1_0 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S1_0_ok]
  simp only [evalP_append, QU_S0_0_zero hN hd, QU_S0_1_zero hN hd, QU_S0_2_zero hN hd, QU_S0_3_zero hN hd, add_zero]

lemma QU_S1_1_zero : evalP (cx hN hd) QU_S1_1 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S1_1_ok]
  simp only [evalP_append, QU_S0_4_zero hN hd, QU_S0_5_zero hN hd, QU_S0_6_zero hN hd, QU_S0_7_zero hN hd, add_zero]

lemma QU_S1_2_zero : evalP (cx hN hd) QU_S1_2 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S1_2_ok]
  simp only [evalP_append, QU_S0_8_zero hN hd, QU_S0_9_zero hN hd, QU_S0_10_zero hN hd, QU_S0_11_zero hN hd, add_zero]

lemma QU_S1_3_zero : evalP (cx hN hd) QU_S1_3 = 0 := by
  rw [← eqCheck_sound _ _ _ QU_S1_3_ok]
  simp only [evalP_append, QU_S0_12_zero hN hd, QU_S0_13_zero hN hd, QU_S0_14_zero hN hd, QU_S0_15_zero hN hd, add_zero]

lemma QU_root_zero : evalP (cx hN hd) QU_root = 0 := by
  rw [eqRuns_sound _ _ _ QU_root_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, QU_S1_0_zero hN hd, QU_S1_1_zero hN hd,
    QU_S1_2_zero hN hd, QU_S1_3_zero hN hd, add_zero]

theorem QU_eval : eQU.eval (cx hN hd) = 0 := by
  rw [← QU_meanE, evalP_mulTerm _ _ _ _ (by decide +kernel), QU_root_zero hN hd, mul_zero]

end Ident
end ALz11
