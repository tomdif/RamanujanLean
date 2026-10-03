/-
# Dyson's rank mod 7: assembly

From `newform` and the `m`-level 7-split of the two Appell–Lerch sums, `R(ζ;q)` is a sum of class-pure mock
pieces (the only class-5 pair cancels, `orbit7`) and a theta part equal to the explicit `Θ_g`
(by the 38 level-21 identities of `ALCore7`), which has no class-5 exponents.
-/
import RamanujanTau.ALRank7Pre

set_option autoImplicit false

namespace ALz
open HahnSeries

section Decomp
variable {ζ : ℂ} (h7 : ζ ^ 7 = 1) (hζ : ζ ≠ 1)
include h7 hζ

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem decomp :
    ι1 (CrankProof.Dser ζ ζ⁻¹) = mono 0 (1 - ζ) * (1 - msum h3 7 (by norm_num) 2 (ζ ^ 4) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1) (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2]) - mono 0 (ζ ^ 6) * msum h3 7 (by norm_num) 1 (ζ ^ 4) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1) (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])) + ThetaG ζ := by
  have h0 := zeta_ne0 h7
  have hd7 : 3 * 7 * 7 = 21 * 7 := by norm_num
  obtain ⟨C2, ms2, hC2⟩ := m_split_msum h3 7 (by norm_num) (a := 2) (β := 0) (by norm_num) (by norm_num) (cx := ζ ^ 4) (cp := ζ ^ 2)
    (pow_ne_zero _ h0) (pow_ne_zero _ h0) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1) (fun _ => one_ne_zero)
    (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])
    (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])
    (by intro s; fin_cases s <;> simp) (by intro s; fin_cases s <;> simp)
    (by intro s; fin_cases s <;> exact mono_ne_one_of (Or.inl (by simp [spA, c2])))
  obtain ⟨C1, ms1, hC1⟩ := m_split_msum h3 7 (by norm_num) (a := 1) (β := 0) (by norm_num) (by norm_num) (cx := ζ ^ 4) (cp := ζ ^ 2)
    (pow_ne_zero _ h0) (pow_ne_zero _ h0) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1) (fun _ => one_ne_zero)
    (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])
    (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])
    (by intro s; fin_cases s <;> simp) (by intro s; fin_cases s <;> simp)
    (by intro s; fin_cases s <;> exact mono_ne_one_of (Or.inl (by simp [spA, c2])))
  rw [Aser_eq_Ab h3 _ _ (pow_ne_zero _ h0) (pow_ne_zero _ h0)] at ms2 ms1
  have hnf := newform h7 hζ
  have tdis := θ_dissect h3 7 (by norm_num) 0 (c := ζ ^ 2) (pow_ne_zero _ h0)
  have hT : θ h3 0 (ζ ^ 2) ≠ 0 := θ_ne0 h3 (zeta_pow_ne h7 hζ (by norm_num) (by norm_num))
  apply mul_right_cancel₀ hT
  rw [hC2] at ms2
  rw [hC1] at ms1
  linear_combination (norm := skip) hnf - mono 0 (1 - ζ) * ms2 - mono 0 (1 - ζ) * mono 0 (ζ ^ 6) * ms1 - ThetaG ζ * tdis - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 0 * core7_0_0 hP hd7 - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 1 * core7_0_1 hP hd7 - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 2 * core7_0_2 hP hd7 - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 3 * core7_0_3 hP hd7 - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 4 * core7_0_4 hP hd7 - (-hs (kF hP 0)) * mono 0 (1:ℂ) * mono 0 ζ ^ 5 * core7_0_5 hP hd7 - (-hs (kF hP 0)) * mono 1 (1:ℂ) * mono 0 ζ ^ 0 * core7_1_0 hP hd7 - (-hs (kF hP 0)) * mono 1 (1:ℂ) * mono 0 ζ ^ 1 * core7_1_1 hP hd7 - (-hs (kF hP 0)) * mono 1 (1:ℂ) * mono 0 ζ ^ 2 * core7_1_2 hP hd7 - (-hs (kF hP 0)) * mono 1 (1:ℂ) * mono 0 ζ ^ 3 * core7_1_3 hP hd7 - (-hs (kF hP 0)) * mono 1 (1:ℂ) * mono 0 ζ ^ 5 * core7_1_5 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 0 * core7_2_0 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 1 * core7_2_1 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 2 * core7_2_2 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 3 * core7_2_3 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 4 * core7_2_4 hP hd7 - (-hs (kF hP 0)) * mono 2 (1:ℂ) * mono 0 ζ ^ 5 * core7_2_5 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 0 * core7_3_0 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 1 * core7_3_1 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 2 * core7_3_2 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 3 * core7_3_3 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 4 * core7_3_4 hP hd7 - (-hs (kF hP 0)) * mono 3 (1:ℂ) * mono 0 ζ ^ 5 * core7_3_5 hP hd7 - (-hs (kF hP 0)) * mono 4 (1:ℂ) * mono 0 ζ ^ 0 * core7_4_0 hP hd7 - (-hs (kF hP 0)) * mono 4 (1:ℂ) * mono 0 ζ ^ 2 * core7_4_2 hP hd7 - (-hs (kF hP 0)) * mono 4 (1:ℂ) * mono 0 ζ ^ 4 * core7_4_4 hP hd7 - (-hs (kF hP 0)) * mono 4 (1:ℂ) * mono 0 ζ ^ 5 * core7_4_5 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 0 * core7_5_0 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 1 * core7_5_1 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 2 * core7_5_2 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 3 * core7_5_3 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 4 * core7_5_4 hP hd7 - (-hs (kF hP 0)) * mono 5 (1:ℂ) * mono 0 ζ ^ 5 * core7_5_5 hP hd7 - (-hs (kF hP 0)) * mono 6 (1:ℂ) * mono 0 ζ ^ 0 * core7_6_0 hP hd7 - (-hs (kF hP 0)) * mono 6 (1:ℂ) * mono 0 ζ ^ 1 * core7_6_1 hP hd7 - (-hs (kF hP 0)) * mono 6 (1:ℂ) * mono 0 ζ ^ 3 * core7_6_3 hP hd7 - (-hs (kF hP 0)) * mono 6 (1:ℂ) * mono 0 ζ ^ 4 * core7_6_4 hP hd7 - (-hs (kF hP 0)) * mono 6 (1:ℂ) * mono 0 ζ ^ 5 * core7_6_5 hP hd7
  have b5 : (![7, 7, 7, 7, 140, 140, 140] : Fin 7 → ℤ) 5 = 140 := rfl
  have b6 : (![7, 7, 7, 7, 140, 140, 140] : Fin 7 → ℤ) 6 = 140 := rfl
  unfold ThetaG
  simp only [b5, b6, Fin.sum_univ_seven, spB, spE, spC, spCX, spCP, c2, spA, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Jt, Qt]
  have p7 : ∀ k : ℕ, (ζ ^ k) ^ 7 = 1 := fun k => by rw [← pow_mul, mul_comm, pow_mul, h7, one_pow]
  simp only [mono]
  set q : L := single 1 (1 : ℂ) with hq
  have hsq : ∀ (e : ℤ) (c : ℂ), (single e c : L) = q ^ e * HahnSeries.C c := fun e c => by
    rw [hq, ← mono, mono_zpow, HahnSeries.C_apply, mono, single_mul_single]; simp
  simp only [hsq, map_mul, map_pow, map_inv₀, map_neg, map_one, map_zpow₀, map_sub, map_ofNat]
  set Z : L := HahnSeries.C ζ with hZ
  simp only [p7, mul_one, one_mul, inv_one]
  norm_num
  have nθm119 : θ hP (-119) 1 = (-1 : L) * q ^ ((-119 : ℤ)) * θ hP 28 1 := by
    have := Jt_norm hP hd7 (-17) (4) (-1) (-17) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-119 : ℤ) = ((7 : ℕ) : ℤ) * (-17) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm98 : θ hP (-98) 1 = (-1 : L) * q ^ ((-98 : ℤ)) * θ hP 49 1 := by
    have := Jt_norm hP hd7 (-14) (7) (-1) (-14) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-98 : ℤ) = ((7 : ℕ) : ℤ) * (-14) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm77 : θ hP (-77) 1 = (-1 : L) * q ^ ((-77 : ℤ)) * θ hP 70 1 := by
    have := Jt_norm hP hd7 (-11) (10) (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-77 : ℤ) = ((7 : ℕ) : ℤ) * (-11) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm70 : θ hP (-70) 1 = (-1 : L) * q ^ ((-70 : ℤ)) * θ hP 70 1 := by
    have := Jt_norm hP hd7 (-10) (11) (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-70 : ℤ) = ((7 : ℕ) : ℤ) * (-10) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm63 : θ hP (-63) 1 = (-1 : L) * q ^ ((-63 : ℤ)) * θ hP 63 1 := by
    have := Jt_norm hP hd7 (-9) (12) (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-63 : ℤ) = ((7 : ℕ) : ℤ) * (-9) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm56 : θ hP (-56) 1 = (-1 : L) * q ^ ((-56 : ℤ)) * θ hP 56 1 := by
    have := Jt_norm hP hd7 (-8) (13) (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-56 : ℤ) = ((7 : ℕ) : ℤ) * (-8) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm49 : θ hP (-49) 1 = (-1 : L) * q ^ ((-49 : ℤ)) * θ hP 49 1 := by
    have := Jt_norm hP hd7 (-7) (14) (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-49 : ℤ) = ((7 : ℕ) : ℤ) * (-7) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm42 : θ hP (-42) 1 = (-1 : L) * q ^ ((-42 : ℤ)) * θ hP 42 1 := by
    have := Jt_norm hP hd7 (-6) (15) (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-42 : ℤ) = ((7 : ℕ) : ℤ) * (-6) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm35 : θ hP (-35) 1 = (-1 : L) * q ^ ((-35 : ℤ)) * θ hP 35 1 := by
    have := Jt_norm hP hd7 (-5) (16) (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-35 : ℤ) = ((7 : ℕ) : ℤ) * (-5) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm28 : θ hP (-28) 1 = (-1 : L) * q ^ ((-28 : ℤ)) * θ hP 28 1 := by
    have := Jt_norm hP hd7 (-4) (17) (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-28 : ℤ) = ((7 : ℕ) : ℤ) * (-4) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm21 : θ hP (-21) 1 = (-1 : L) * q ^ ((-21 : ℤ)) * θ hP 21 1 := by
    have := Jt_norm hP hd7 (-3) (18) (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-21 : ℤ) = ((7 : ℕ) : ℤ) * (-3) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm14 : θ hP (-14) 1 = (-1 : L) * q ^ ((-14 : ℤ)) * θ hP 14 1 := by
    have := Jt_norm hP hd7 (-2) (19) (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-14 : ℤ) = ((7 : ℕ) : ℤ) * (-2) by norm_num, this, map_one, mul_one]
    norm_num
  have nθm7 : θ hP (-7) 1 = (-1 : L) * q ^ ((-7 : ℤ)) * θ hP 7 1 := by
    have := Jt_norm hP hd7 (-1) (20) (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (-7 : ℤ) = ((7 : ℕ) : ℤ) * (-1) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ0 : θ hP 0 1 = 0 := by
    have := Jt_norm0 hP hd7 0 0 (by norm_num)
    simpa using this
  have nθ77 : θ hP (77) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 70 1 := by
    have := Jt_norm hP hd7 (11) (11) (0) (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (77 : ℤ) = ((7 : ℕ) : ℤ) * (11) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ84 : θ hP (84) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 63 1 := by
    have := Jt_norm hP hd7 (12) (12) (0) (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (84 : ℤ) = ((7 : ℕ) : ℤ) * (12) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ91 : θ hP (91) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 56 1 := by
    have := Jt_norm hP hd7 (13) (13) (0) (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (91 : ℤ) = ((7 : ℕ) : ℤ) * (13) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ98 : θ hP (98) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 49 1 := by
    have := Jt_norm hP hd7 (14) (14) (0) (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (98 : ℤ) = ((7 : ℕ) : ℤ) * (14) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ105 : θ hP (105) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 42 1 := by
    have := Jt_norm hP hd7 (15) (15) (0) (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (105 : ℤ) = ((7 : ℕ) : ℤ) * (15) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ112 : θ hP (112) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 35 1 := by
    have := Jt_norm hP hd7 (16) (16) (0) (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (112 : ℤ) = ((7 : ℕ) : ℤ) * (16) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ119 : θ hP (119) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 28 1 := by
    have := Jt_norm hP hd7 (17) (17) (0) (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (119 : ℤ) = ((7 : ℕ) : ℤ) * (17) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ126 : θ hP (126) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 21 1 := by
    have := Jt_norm hP hd7 (18) (18) (0) (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (126 : ℤ) = ((7 : ℕ) : ℤ) * (18) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ133 : θ hP (133) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 14 1 := by
    have := Jt_norm hP hd7 (19) (19) (0) (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (133 : ℤ) = ((7 : ℕ) : ℤ) * (19) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ140 : θ hP (140) 1 = (1 : L) * q ^ ((0 : ℤ)) * θ hP 7 1 := by
    have := Jt_norm hP hd7 (20) (20) (0) (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (140 : ℤ) = ((7 : ℕ) : ℤ) * (20) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ147 : θ hP 147 1 = 0 := by
    have := Jt_norm0 hP hd7 21 1 (by norm_num)
    simpa using this
  have nθ154 : θ hP (154) 1 = (-1 : L) * q ^ ((-7 : ℤ)) * θ hP 7 1 := by
    have := Jt_norm hP hd7 (22) (1) (1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (154 : ℤ) = ((7 : ℕ) : ℤ) * (22) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ168 : θ hP (168) 1 = (-1 : L) * q ^ ((-21 : ℤ)) * θ hP 21 1 := by
    have := Jt_norm hP hd7 (24) (3) (1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (168 : ℤ) = ((7 : ℕ) : ℤ) * (24) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ175 : θ hP (175) 1 = (-1 : L) * q ^ ((-28 : ℤ)) * θ hP 28 1 := by
    have := Jt_norm hP hd7 (25) (4) (1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (175 : ℤ) = ((7 : ℕ) : ℤ) * (25) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ189 : θ hP (189) 1 = (-1 : L) * q ^ ((-42 : ℤ)) * θ hP 42 1 := by
    have := Jt_norm hP hd7 (27) (6) (1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (189 : ℤ) = ((7 : ℕ) : ℤ) * (27) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ196 : θ hP (196) 1 = (-1 : L) * q ^ ((-49 : ℤ)) * θ hP 49 1 := by
    have := Jt_norm hP hd7 (28) (7) (1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (196 : ℤ) = ((7 : ℕ) : ℤ) * (28) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ210 : θ hP (210) 1 = (-1 : L) * q ^ ((-63 : ℤ)) * θ hP 63 1 := by
    have := Jt_norm hP hd7 (30) (9) (1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (210 : ℤ) = ((7 : ℕ) : ℤ) * (30) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ217 : θ hP (217) 1 = (-1 : L) * q ^ ((-70 : ℤ)) * θ hP 70 1 := by
    have := Jt_norm hP hd7 (31) (10) (1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (217 : ℤ) = ((7 : ℕ) : ℤ) * (31) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ231 : θ hP (231) 1 = (-1 : L) * q ^ ((-84 : ℤ)) * θ hP 63 1 := by
    have := Jt_norm hP hd7 (33) (12) (1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (231 : ℤ) = ((7 : ℕ) : ℤ) * (33) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ238 : θ hP (238) 1 = (-1 : L) * q ^ ((-91 : ℤ)) * θ hP 56 1 := by
    have := Jt_norm hP hd7 (34) (13) (1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (238 : ℤ) = ((7 : ℕ) : ℤ) * (34) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ252 : θ hP (252) 1 = (-1 : L) * q ^ ((-105 : ℤ)) * θ hP 42 1 := by
    have := Jt_norm hP hd7 (36) (15) (1) (-15) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (252 : ℤ) = ((7 : ℕ) : ℤ) * (36) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ259 : θ hP (259) 1 = (-1 : L) * q ^ ((-112 : ℤ)) * θ hP 35 1 := by
    have := Jt_norm hP hd7 (37) (16) (1) (-16) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (259 : ℤ) = ((7 : ℕ) : ℤ) * (37) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ273 : θ hP (273) 1 = (-1 : L) * q ^ ((-126 : ℤ)) * θ hP 21 1 := by
    have := Jt_norm hP hd7 (39) (18) (1) (-18) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (273 : ℤ) = ((7 : ℕ) : ℤ) * (39) by norm_num, this, map_one, mul_one]
    norm_num
  have nθ280 : θ hP (280) 1 = (-1 : L) * q ^ ((-133 : ℤ)) * θ hP 14 1 := by
    have := Jt_norm hP hd7 (40) (19) (1) (-19) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)
    rw [Qt_zpow, Jt, mono, hsq] at this
    rw [show (280 : ℤ) = ((7 : ℕ) : ℤ) * (40) by norm_num, this, map_one, mul_one]
    norm_num

  simp only [nθm119, nθm98, nθm77, nθm70, nθm63, nθm56, nθm49, nθm42, nθm35, nθm28, nθm21, nθm14, nθm7, nθ0, nθ77, nθ84, nθ91, nθ98, nθ105, nθ112, nθ119, nθ126, nθ133, nθ140, nθ147, nθ154, nθ168, nθ175, nθ189, nθ196, nθ210, nθ217, nθ231, nθ238, nθ252, nθ259, nθ273, nθ280]
  have hq0 : q ≠ 0 := by rw [hq]; simp
  have hZ0 : Z ≠ 0 := by rw [hZ]; simpa using h0
  have tz1 : θ hP 7 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz2 : θ hP 14 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz3 : θ hP 21 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz4 : θ hP 28 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz5 : θ hP 35 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz6 : θ hP 42 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz7 : θ hP 49 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz8 : θ hP 56 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz9 : θ hP 63 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have tz10 : θ hP 70 1 ≠ 0 := θ_ne hP (by norm_num) (by norm_num) 1
  have hZ7 : Z ^ 7 = 1 := by rw [hZ, ← map_pow, h7, map_one]
  have hΦc : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = 0 := by linear_combination h7
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ)
  have hZ6 : Z ^ 6 = -(1 + Z + Z ^ 2 + Z ^ 3 + Z ^ 4 + Z ^ 5) := by
    have h := congrArg (HahnSeries.C (Γ := ℤ) (R := ℂ)) hΦc
    simp only [map_add, map_pow, map_one, map_zero] at h
    rw [← hZ] at h
    linear_combination h
  have r7 : Z ^ 7 = Z ^ 0 := by rw [show 7 = 0 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r8 : Z ^ 8 = Z ^ 1 := by rw [show 8 = 1 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r9 : Z ^ 9 = Z ^ 2 := by rw [show 9 = 2 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r10 : Z ^ 10 = Z ^ 3 := by rw [show 10 = 3 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r11 : Z ^ 11 = Z ^ 4 := by rw [show 11 = 4 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r12 : Z ^ 12 = Z ^ 5 := by rw [show 12 = 5 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r13 : Z ^ 13 = Z ^ 6 := by rw [show 13 = 6 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r14 : Z ^ 14 = Z ^ 0 := by rw [show 14 = 0 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r15 : Z ^ 15 = Z ^ 1 := by rw [show 15 = 1 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r16 : Z ^ 16 = Z ^ 2 := by rw [show 16 = 2 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r17 : Z ^ 17 = Z ^ 3 := by rw [show 17 = 3 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r18 : Z ^ 18 = Z ^ 4 := by rw [show 18 = 4 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r19 : Z ^ 19 = Z ^ 5 := by rw [show 19 = 5 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r20 : Z ^ 20 = Z ^ 6 := by rw [show 20 = 6 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r21 : Z ^ 21 = Z ^ 0 := by rw [show 21 = 0 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r22 : Z ^ 22 = Z ^ 1 := by rw [show 22 = 1 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r23 : Z ^ 23 = Z ^ 2 := by rw [show 23 = 2 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r24 : Z ^ 24 = Z ^ 3 := by rw [show 24 = 3 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r25 : Z ^ 25 = Z ^ 4 := by rw [show 25 = 4 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r26 : Z ^ 26 = Z ^ 5 := by rw [show 26 = 5 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r27 : Z ^ 27 = Z ^ 6 := by rw [show 27 = 6 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r28 : Z ^ 28 = Z ^ 0 := by rw [show 28 = 0 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r29 : Z ^ 29 = Z ^ 1 := by rw [show 29 = 1 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r30 : Z ^ 30 = Z ^ 2 := by rw [show 30 = 2 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r31 : Z ^ 31 = Z ^ 3 := by rw [show 31 = 3 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r32 : Z ^ 32 = Z ^ 4 := by rw [show 32 = 4 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r33 : Z ^ 33 = Z ^ 5 := by rw [show 33 = 5 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r34 : Z ^ 34 = Z ^ 6 := by rw [show 34 = 6 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r35 : Z ^ 35 = Z ^ 0 := by rw [show 35 = 0 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r36 : Z ^ 36 = Z ^ 1 := by rw [show 36 = 1 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r37 : Z ^ 37 = Z ^ 2 := by rw [show 37 = 2 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r38 : Z ^ 38 = Z ^ 3 := by rw [show 38 = 3 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r39 : Z ^ 39 = Z ^ 4 := by rw [show 39 = 4 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r40 : Z ^ 40 = Z ^ 5 := by rw [show 40 = 5 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r41 : Z ^ 41 = Z ^ 6 := by rw [show 41 = 6 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r42 : Z ^ 42 = Z ^ 0 := by rw [show 42 = 0 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r43 : Z ^ 43 = Z ^ 1 := by rw [show 43 = 1 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r44 : Z ^ 44 = Z ^ 2 := by rw [show 44 = 2 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r45 : Z ^ 45 = Z ^ 3 := by rw [show 45 = 3 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r46 : Z ^ 46 = Z ^ 4 := by rw [show 46 = 4 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r47 : Z ^ 47 = Z ^ 5 := by rw [show 47 = 5 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r48 : Z ^ 48 = Z ^ 6 := by rw [show 48 = 6 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r49 : Z ^ 49 = Z ^ 0 := by rw [show 49 = 0 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r50 : Z ^ 50 = Z ^ 1 := by rw [show 50 = 1 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r51 : Z ^ 51 = Z ^ 2 := by rw [show 51 = 2 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r52 : Z ^ 52 = Z ^ 3 := by rw [show 52 = 3 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r53 : Z ^ 53 = Z ^ 4 := by rw [show 53 = 4 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r54 : Z ^ 54 = Z ^ 5 := by rw [show 54 = 5 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r55 : Z ^ 55 = Z ^ 6 := by rw [show 55 = 6 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r56 : Z ^ 56 = Z ^ 0 := by rw [show 56 = 0 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r57 : Z ^ 57 = Z ^ 1 := by rw [show 57 = 1 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r58 : Z ^ 58 = Z ^ 2 := by rw [show 58 = 2 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r59 : Z ^ 59 = Z ^ 3 := by rw [show 59 = 3 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r60 : Z ^ 60 = Z ^ 4 := by rw [show 60 = 4 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r61 : Z ^ 61 = Z ^ 5 := by rw [show 61 = 5 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r62 : Z ^ 62 = Z ^ 6 := by rw [show 62 = 6 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r63 : Z ^ 63 = Z ^ 0 := by rw [show 63 = 0 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r64 : Z ^ 64 = Z ^ 1 := by rw [show 64 = 1 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r65 : Z ^ 65 = Z ^ 2 := by rw [show 65 = 2 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r66 : Z ^ 66 = Z ^ 3 := by rw [show 66 = 3 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r67 : Z ^ 67 = Z ^ 4 := by rw [show 67 = 4 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r68 : Z ^ 68 = Z ^ 5 := by rw [show 68 = 5 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r69 : Z ^ 69 = Z ^ 6 := by rw [show 69 = 6 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r70 : Z ^ 70 = Z ^ 0 := by rw [show 70 = 0 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r71 : Z ^ 71 = Z ^ 1 := by rw [show 71 = 1 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r72 : Z ^ 72 = Z ^ 2 := by rw [show 72 = 2 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r73 : Z ^ 73 = Z ^ 3 := by rw [show 73 = 3 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r74 : Z ^ 74 = Z ^ 4 := by rw [show 74 = 4 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r75 : Z ^ 75 = Z ^ 5 := by rw [show 75 = 5 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r76 : Z ^ 76 = Z ^ 6 := by rw [show 76 = 6 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r77 : Z ^ 77 = Z ^ 0 := by rw [show 77 = 0 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r78 : Z ^ 78 = Z ^ 1 := by rw [show 78 = 1 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r79 : Z ^ 79 = Z ^ 2 := by rw [show 79 = 2 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r80 : Z ^ 80 = Z ^ 3 := by rw [show 80 = 3 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r81 : Z ^ 81 = Z ^ 4 := by rw [show 81 = 4 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r82 : Z ^ 82 = Z ^ 5 := by rw [show 82 = 5 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r83 : Z ^ 83 = Z ^ 6 := by rw [show 83 = 6 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r84 : Z ^ 84 = Z ^ 0 := by rw [show 84 = 0 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r85 : Z ^ 85 = Z ^ 1 := by rw [show 85 = 1 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r86 : Z ^ 86 = Z ^ 2 := by rw [show 86 = 2 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r87 : Z ^ 87 = Z ^ 3 := by rw [show 87 = 3 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r88 : Z ^ 88 = Z ^ 4 := by rw [show 88 = 4 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r89 : Z ^ 89 = Z ^ 5 := by rw [show 89 = 5 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r90 : Z ^ 90 = Z ^ 6 := by rw [show 90 = 6 + 7 * 12 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r91 : Z ^ 91 = Z ^ 0 := by rw [show 91 = 0 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r92 : Z ^ 92 = Z ^ 1 := by rw [show 92 = 1 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r93 : Z ^ 93 = Z ^ 2 := by rw [show 93 = 2 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r94 : Z ^ 94 = Z ^ 3 := by rw [show 94 = 3 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r95 : Z ^ 95 = Z ^ 4 := by rw [show 95 = 4 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r96 : Z ^ 96 = Z ^ 5 := by rw [show 96 = 5 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r97 : Z ^ 97 = Z ^ 6 := by rw [show 97 = 6 + 7 * 13 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r98 : Z ^ 98 = Z ^ 0 := by rw [show 98 = 0 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r99 : Z ^ 99 = Z ^ 1 := by rw [show 99 = 1 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r100 : Z ^ 100 = Z ^ 2 := by rw [show 100 = 2 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r101 : Z ^ 101 = Z ^ 3 := by rw [show 101 = 3 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r102 : Z ^ 102 = Z ^ 4 := by rw [show 102 = 4 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r103 : Z ^ 103 = Z ^ 5 := by rw [show 103 = 5 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r104 : Z ^ 104 = Z ^ 6 := by rw [show 104 = 6 + 7 * 14 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r105 : Z ^ 105 = Z ^ 0 := by rw [show 105 = 0 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r106 : Z ^ 106 = Z ^ 1 := by rw [show 106 = 1 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r107 : Z ^ 107 = Z ^ 2 := by rw [show 107 = 2 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r108 : Z ^ 108 = Z ^ 3 := by rw [show 108 = 3 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r109 : Z ^ 109 = Z ^ 4 := by rw [show 109 = 4 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r110 : Z ^ 110 = Z ^ 5 := by rw [show 110 = 5 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r111 : Z ^ 111 = Z ^ 6 := by rw [show 111 = 6 + 7 * 15 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r112 : Z ^ 112 = Z ^ 0 := by rw [show 112 = 0 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r113 : Z ^ 113 = Z ^ 1 := by rw [show 113 = 1 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r114 : Z ^ 114 = Z ^ 2 := by rw [show 114 = 2 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r115 : Z ^ 115 = Z ^ 3 := by rw [show 115 = 3 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r116 : Z ^ 116 = Z ^ 4 := by rw [show 116 = 4 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r117 : Z ^ 117 = Z ^ 5 := by rw [show 117 = 5 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r118 : Z ^ 118 = Z ^ 6 := by rw [show 118 = 6 + 7 * 16 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r119 : Z ^ 119 = Z ^ 0 := by rw [show 119 = 0 + 7 * 17 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  field_simp
  ring_nf
  simp only [r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99, r100, r101, r102, r103, r104, r105, r106, r107, r108, r109, r110, r111, r112, r113, r114, r115, r116, r117, r118, r119]
  ring_nf
  linear_combination ((1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 17 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 28 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 10 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 11 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 35 1) ^ 2 * (q) ^ 22 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 56 1) ^ 3 * (q) ^ 17 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 3 * (q) ^ 11 + (1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 3 * (θ hP 56 1) ^ 3 * (θ hP 63 1) ^ 2 * (q) ^ 8 + (-1 : L) * (hs (kF hP 0)) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 7 1) * (θ hP 14 1) ^ 3 * (θ hP 35 1) ^ 3 * (θ hP 49 1) ^ 2 * (θ hP 63 1) ^ 2 * (q) ^ 13 + (1 : L) * (hs (kF hP 0)) * (θ hP 56 1) * (θ hP 7 1) * (θ hP 14 1) ^ 3 * (θ hP 35 1) ^ 3 * (θ hP 49 1) ^ 2 * (θ hP 63 1) ^ 3 * (q) ^ 10 + (1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 2 * (q) ^ 23 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 49 1) ^ 2 * (q) ^ 18 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 30 + (1 : L) * (hs (kF hP 0)) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 2 * (q) ^ 18 + (1 : L) * (hs (kF hP 0)) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 10 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 35 1) ^ 2 * (q) ^ 17 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 42 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 3 * (q) ^ 17 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 16 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 13 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 8 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 3 * (q) ^ 15 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 2 * (q) ^ 14 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 2 * (θ hP 63 1) ^ 2 * (q) ^ 13 + (2 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 3 * (q) ^ 13 + (-2 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 27 + (2 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 11 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 25 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 3 * (q) ^ 10 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 63 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 21 + (1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 21 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 42 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 56 1) ^ 2 * (q) ^ 6 + (1 : L) * (hs (kF hP 0)) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 3 * (q) ^ 11 + (-1 : L) * (hs (kF hP 0)) * (θ hP 42 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 3 * (θ hP 63 1) ^ 2 * (q) ^ 8 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 63 1) ^ 2 * (q) ^ 6 + (2 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 3 * (θ hP 56 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 6 + (1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 18 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 3 + (1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 7 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 3 * (θ hP 63 1) ^ 2 * (q) ^ 3 + (-1 : L) * (hs (kF hP 0)) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 70 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 63 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 15 + (-1 : L) * (hs (kF hP 0)) * (θ hP 63 1) * (θ hP 14 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 42 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 15 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 56 1) * (θ hP 7 1) * (θ hP 21 1) ^ 3 * (θ hP 28 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 17 + (-1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 7 1) * (θ hP 21 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 11 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 21 1) ^ 2 * (θ hP 28 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 8 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 28 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) ^ 2 * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 3 * (q) ^ 9 + (-1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 70 1) * (θ hP 21 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 20 + (-1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 7 1) * (θ hP 70 1) * (θ hP 35 1) ^ 3 * (θ hP 56 1) ^ 3 * (θ hP 63 1) ^ 2 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 7 1) * (θ hP 35 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 70 1) ^ 2 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 3 * (θ hP 7 1) ^ 2 * (q) ^ 15 + (-1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 14 + (-1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * (θ hP 63 1) * (θ hP 35 1) ^ 2 * (θ hP 7 1) ^ 2 * (θ hP 70 1) ^ 2 * (q) ^ 13 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 70 1) * (θ hP 42 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 14 + (1 : L) * (hs (kF hP 0)) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 63 1) * (θ hP 42 1) ^ 2 * (θ hP 49 1) ^ 2 * (θ hP 56 1) ^ 3 * (θ hP 7 1) ^ 3 * (q) ^ 14 + (-1 : L) * (hs (kF hP 0)) * (θ hP 21 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 63 1) * (θ hP 70 1) * (θ hP 28 1) ^ 2 * (θ hP 35 1) ^ 2 * (θ hP 56 1) ^ 2 * (θ hP 7 1) ^ 2 * (q) ^ 9) * hZ6

end Decomp


/-- `R(ζ;q)` at a nontrivial 7th root of unity has no exponent `≡ 5 (mod 7)`. -/
theorem rank7_no5 {ζ : ℂ} (h7 : ζ ^ 7 = 1) (hζ : ζ ≠ 1) : No5 (ι1 (CrankProof.Dser ζ ζ⁻¹)) := by
  rw [decomp h7 hζ]
  exact No5.add (No5.cls0_mul (c0_mono (dvd_zero 7) _) (mock_no5 h7 (zeta_ne0 h7))) (ThetaG_no5 ζ)

end ALz

namespace CrankProof
open Finset

/-- `Σ_{λ ⊢ 7n+5} ζ₇^{rank λ} = 0`. -/
theorem rank_sum_root7_zero (n : ℕ) : ∑ l : (7 * n + 5).Partition, ω7 ^ rank l = 0 := by
  have h := ALz.rank7_no5 ω7_pow7 (ω7_prim.ne_one (by norm_num)) ((7 * n + 5 : ℕ) : ℤ) (by omega)
  rw [ALz.ι1_coeff_nat] at h
  rw [rank_durfee ω7_ne, h]

/-- the number of partitions of `n` with rank `≡ k (mod 7)`. -/
noncomputable def rankCount7 (n k : ℕ) : ℕ := (univ.filter fun l : n.Partition => (rank l % 7).toNat = k).card

lemma rank_sum_grouped7 (n : ℕ) :
    ∑ l : n.Partition, ω7 ^ rank l = ∑ k ∈ range 7, (rankCount7 n k : ℂ) * ω7 ^ k := by
  simp_rw [ω7_zpow_crank]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 7) (g := fun l : n.Partition => (rank l % 7).toNat)
    (fun l _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (show (rank l % 7).toNat < 7 by omega)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ω7 ^ k) (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
    Finset.sum_const, nsmul_eq_mul, rankCount7]

lemma rankCount7_sum (n : ℕ) : ∑ k ∈ range 7, rankCount7 n k = Fintype.card n.Partition := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fun l : n.Partition => (rank l % 7).toNat)
    (t := range 7) (fun l _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (show (rank l % 7).toNat < 7 by omega)))]
  rfl

/-- **Dyson's rank conjecture mod 7** (Atkin–Swinnerton-Dyer 1954): the rank splits the partitions of `7n+5`
into seven equal classes, `N(i, 7, 7n+5) = p(7n+5)/7`. -/
theorem rank_equidistribution_mod7 (n : ℕ) {i : ℕ} (hi : i < 7) :
    7 * (univ.filter fun l : (7 * n + 5).Partition => rank l % 7 = i).card
      = Fintype.card (7 * n + 5).Partition := by
  have h := rank_sum_root7_zero n
  rw [rank_sum_grouped7] at h
  have e : ∀ k < 6, rankCount7 (7 * n + 5) k = rankCount7 (7 * n + 5) 6 := fun k hk => cyc_equal7 _ h hk
  have hs := rankCount7_sum (7 * n + 5)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  have hfilt : (univ.filter fun l : (7 * n + 5).Partition => rank l % 7 = i) =
      univ.filter fun l => (rank l % 7).toNat = i :=
    Finset.filter_congr fun l _ => by omega
  rw [hfilt, ← rankCount7]
  have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num); have e4 := e 4 (by norm_num); have e5 := e 5 (by norm_num)
  interval_cases i <;> omega

end CrankProof
