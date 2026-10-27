/-
# Atkin 11^k: evaluating the certificate polynomials at the theta point

At `x = (c₀, c₁, c₂, c₄, c₇) = (J₄/J₂, −J₂/J₁, −J₅/J₃, −Q J₁/J₅, J₃/J₄)` (`J_a = θ(Q^a; Q¹¹)`), each certificate
generator `W_i` is a three-term relation divided by a monomial, hence vanishes.
-/
import RamanujanTau.Atkin11Weier
import RamanujanTau.Atkin11Cert.Common

set_option autoImplicit false

namespace ALz11
open HahnSeries ALz SPoly

section Eval
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 11 * d)
include hN hd

/-- the theta point. -/
noncomputable def cx : List L :=
  [Jt hN hd 4 / Jt hN hd 2, -(Jt hN hd 2 / Jt hN hd 1), -(Jt hN hd 5 / Jt hN hd 3),
    -(Qt hd * Jt hN hd 1 / Jt hN hd 5), Jt hN hd 3 / Jt hN hd 4]

lemma W1_zero : evalP (cx hN hd) Atkin11Cert.W1 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel7 hN hd
  simp only [Atkin11Cert.W1, Atkin11Cert.W1_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W2_zero : evalP (cx hN hd) Atkin11Cert.W2 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel8 hN hd
  simp only [Atkin11Cert.W2, Atkin11Cert.W2_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W3_zero : evalP (cx hN hd) Atkin11Cert.W3 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel9 hN hd
  simp only [Atkin11Cert.W3, Atkin11Cert.W3_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W4_zero : evalP (cx hN hd) Atkin11Cert.W4 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel10 hN hd
  simp only [Atkin11Cert.W4, Atkin11Cert.W4_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W5_zero : evalP (cx hN hd) Atkin11Cert.W5 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel5 hN hd
  simp only [Atkin11Cert.W5, Atkin11Cert.W5_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W6_zero : evalP (cx hN hd) Atkin11Cert.W6 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel3 hN hd
  simp only [Atkin11Cert.W6, Atkin11Cert.W6_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W7_zero : evalP (cx hN hd) Atkin11Cert.W7 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel1 hN hd
  simp only [Atkin11Cert.W7, Atkin11Cert.W7_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W8_zero : evalP (cx hN hd) Atkin11Cert.W8 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel6 hN hd
  simp only [Atkin11Cert.W8, Atkin11Cert.W8_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W9_zero : evalP (cx hN hd) Atkin11Cert.W9 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel2 hN hd
  simp only [Atkin11Cert.W9, Atkin11Cert.W9_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma W10_zero : evalP (cx hN hd) Atkin11Cert.W10 = 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  have r := rel4 hN hd
  simp only [Atkin11Cert.W10, Atkin11Cert.W10_0, ofPacked, List.map, decTerm, evalP, evalM, dec,
    evalL, cx] at *
  norm_num
  field_simp
  first | linear_combination r | linear_combination -r

lemma Ws_zero : ∀ w ∈ Atkin11Cert.Ws, evalP (cx hN hd) w = 0 := by
  intro w hw
  simp only [Atkin11Cert.Ws, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G1_zero : evalP (cx hN hd) Atkin11Cert.G1 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G1_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G2_zero : evalP (cx hN hd) Atkin11Cert.G2 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G2_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G3_zero : evalP (cx hN hd) Atkin11Cert.G3 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G3_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G4_zero : evalP (cx hN hd) Atkin11Cert.G4 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G4_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G5_zero : evalP (cx hN hd) Atkin11Cert.G5 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G5_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G6_zero : evalP (cx hN hd) Atkin11Cert.G6 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G6_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G7_zero : evalP (cx hN hd) Atkin11Cert.G7 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G7_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G8_zero : evalP (cx hN hd) Atkin11Cert.G8 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G8_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G9_zero : evalP (cx hN hd) Atkin11Cert.G9 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G9_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G10_zero : evalP (cx hN hd) Atkin11Cert.G10 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G10_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G11_zero : evalP (cx hN hd) Atkin11Cert.G11 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G11_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G12_zero : evalP (cx hN hd) Atkin11Cert.G12 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G12_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G13_zero : evalP (cx hN hd) Atkin11Cert.G13 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G13_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G14_zero : evalP (cx hN hd) Atkin11Cert.G14 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G14_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G15_zero : evalP (cx hN hd) Atkin11Cert.G15 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G15_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G16_zero : evalP (cx hN hd) Atkin11Cert.G16 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G16_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G17_zero : evalP (cx hN hd) Atkin11Cert.G17 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G17_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G18_zero : evalP (cx hN hd) Atkin11Cert.G18 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G18_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G19_zero : evalP (cx hN hd) Atkin11Cert.G19 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G19_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G20_zero : evalP (cx hN hd) Atkin11Cert.G20 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G20_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G21_zero : evalP (cx hN hd) Atkin11Cert.G21 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G21_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G22_zero : evalP (cx hN hd) Atkin11Cert.G22 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G22_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G23_zero : evalP (cx hN hd) Atkin11Cert.G23 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G23_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G24_zero : evalP (cx hN hd) Atkin11Cert.G24 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G24_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

lemma G25_zero : evalP (cx hN hd) Atkin11Cert.G25 = 0 := by
  rw [certify_sound _ _ _ Atkin11Cert.G25_ok]
  simp [W1_zero hN hd, W2_zero hN hd, W3_zero hN hd, W4_zero hN hd, W5_zero hN hd, W6_zero hN hd, W7_zero hN hd,
    W8_zero hN hd, W9_zero hN hd, W10_zero hN hd]

end Eval
end ALz11
