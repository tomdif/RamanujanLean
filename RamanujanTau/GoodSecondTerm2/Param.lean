/-
# Parameter choice: `H = T^{299/300}`, `ε = 1/600`, `M₀ = ⌊H⌋`, `h₂ = ⌊T^{1/150}⌋`

`avgOff_le`: for `T ≥ 2^{300}` and `T₁ ∈ [T − H, T]`, `T₁ ≥ 16`: `‖Σ_p zz T₁ H p‖ ≤ C T^{599/600}`.
-/
import RamanujanTau.GoodSecondTerm2.Avg

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

lemma floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx)
  linarith

lemma rpow_le_rpow_T {T a b : ℝ} (hT : 1 ≤ T) (hab : a ≤ b) : T ^ a ≤ T ^ b :=
  Real.rpow_le_rpow_of_exponent_le hT hab

lemma E_le {T₁ H T : ℝ} (hH : 0 ≤ H) (h16 : 16 ≤ T₁) (hT₁ : T₁ ≤ T) (hHT : H ≤ T) :
    Real.exp (ellT (T₁ + H)) ≤ T := by
  rw [exp_ellT (by linarith)]
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith [mul_le_mul_of_nonneg_left (show (2:ℝ) ≤ 2 * Real.pi by linarith) (show (0:ℝ) ≤ T by linarith)]

lemma exp_mul_ellT_le {T₁ H T a : ℝ} (ha : 0 ≤ a) (hH : 0 ≤ H) (h16 : 16 ≤ T₁) (hT₁ : T₁ ≤ T) (hHT : H ≤ T) :
    Real.exp (a * ellT (T₁ + H)) ≤ T ^ a := by
  rw [mul_comm, Real.exp_mul]
  exact Real.rpow_le_rpow (Real.exp_pos _).le (E_le hH h16 hT₁ hHT) ha

set_option maxHeartbeats 1600000 in
theorem avgOff_le : ∃ C : ℝ, ∀ T T₁ : ℝ, 2 ^ (300 : ℕ) ≤ T → 16 ≤ T₁ → T₁ ≤ T →
    ‖∑' p, zz T₁ (T ^ (299 / 300 : ℝ)) p‖ ≤ C * T ^ (599 / 600 : ℝ) := by
  obtain ⟨K, A, hK0, hA0, hB⟩ := off_avg_bound
  set ε : ℝ := 1 / 600
  set c1 : ℝ := c16 * (Zl (13 / 2) * Zl (11 / 2))
  set c2 : ℝ := 4 * (7 * Kphi + 3 * KW) * (Zl (1 + ε) * Zl (1 + ε))
  set c3 : ℝ := Cn * (12 * A)
  set c4 : ℝ := Cn * 2 * 36 * 2 * Su (1 + ε)
  set c5 : ℝ := 2 * K * 2 + 2 * K * 2 * 4
  refine ⟨2 * (c1 + c2 + c3 + c4) + 2 * c5, fun T T₁ hT h16 hT₁ => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hT
  clear hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set H : ℝ := T ^ (299 / 300 : ℝ) with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hT1 (by norm_num)
  have hH0 : 0 < H := by linarith
  have hHT : H ≤ T := by
    calc H ≤ T ^ (1 : ℝ) := rpow_le_rpow_T hT1 (by norm_num)
      _ = T := Real.rpow_one T
  set M₀ : ℕ := ⌊H⌋₊ with hM₀
  set h₂ : ℕ := ⌊T ^ (1 / 150 : ℝ)⌋₊ with hh₂
  have hM₀H : (M₀ : ℝ) ≤ H := Nat.floor_le hH0.le
  have hM₀ge : H / 2 ≤ (M₀ : ℝ) := floor_ge_half hH1
  have hu1 : 1 ≤ T ^ (1 / 150 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hh₂1 : 1 ≤ h₂ := Nat.le_floor (by exact_mod_cast hu1)
  have hh₂M : h₂ ≤ M₀ := Nat.floor_le_floor (rpow_le_rpow_T hT1 (by norm_num))
  have hh₂le : (h₂ : ℝ) ≤ T ^ (1 / 150 : ℝ) := Nat.floor_le (by positivity)
  have hh₂ge : T ^ (1 / 150 : ℝ) / 2 ≤ (h₂ : ℝ) := floor_ge_half hu1
  obtain ⟨-, hbd⟩ := hB T₁ H ε M₀ h₂ h16 hH0 (by norm_num) (by norm_num) hM₀H hh₂1 hh₂M
  refine hbd.trans ?_
  have hTp : (1 : ℝ) ≤ T ^ (599 / 600 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  -- Bnon
  have hBn : Bnon T₁ H ε M₀ h₂ A ≤ (c1 + c2 + c3 + c4) * T ^ (599 / 600 : ℝ) := by
    unfold Bnon
    have hZ1 : 0 ≤ Zl (13 / 2) * Zl (11 / 2) := mul_nonneg (Zl_nonneg _) (Zl_nonneg _)
    have hZ2 : 0 ≤ Zl (1 + ε) * Zl (1 + ε) := mul_nonneg (Zl_nonneg _) (Zl_nonneg _)
    have hSu : 0 ≤ Su (1 + ε) := tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (by positivity)
    have hCn := Cn_pos
    have hK := Kphi_pos
    have hKW := KW_pos
    -- (a)
    have ta : c16 * (Zl (13 / 2) * Zl (11 / 2)) ≤ c1 * T ^ (599 / 600 : ℝ) := by
      have : 0 ≤ c1 := mul_nonneg c16_pos.le hZ1
      nlinarith
    -- (b)
    have hcF : cF (T₁ + H) H ε ≤ (7 * Kphi + 3 * KW) * T ^ (599 / 600 : ℝ) := by
      unfold cF
      have e1 := exp_mul_ellT_le (a := 2 * ε) (by norm_num) hH0.le h16 hT₁ hHT
      have e2 := exp_mul_ellT_le (a := 1 + 2 * ε) (by norm_num) hH0.le h16 hT₁ hHT
      have r1 : T ^ (2 * ε) ≤ T ^ (599 / 600 : ℝ) := rpow_le_rpow_T hT1 (by norm_num)
      have r2 : T ^ (1 + 2 * ε) / H ≤ T ^ (599 / 600 : ℝ) := by
        rw [hH, div_le_iff₀ (by positivity), ← Real.rpow_add hT0]
        exact rpow_le_rpow_T hT1 (by norm_num)
      have : 3 * KW / H * Real.exp ((1 + 2 * ε) * ellT (T₁ + H)) ≤ 3 * KW * T ^ (599 / 600 : ℝ) := by
        calc 3 * KW / H * Real.exp ((1 + 2 * ε) * ellT (T₁ + H)) ≤ 3 * KW / H * T ^ (1 + 2 * ε) := by gcongr
          _ = 3 * KW * (T ^ (1 + 2 * ε) / H) := by ring
          _ ≤ _ := by gcongr
      have : 7 * Kphi * Real.exp (2 * ε * ellT (T₁ + H)) ≤ 7 * Kphi * T ^ (599 / 600 : ℝ) := by
        gcongr; exact e1.trans r1
      nlinarith
    have tb : 4 * cF (T₁ + H) H ε * (Zl (1 + ε) * Zl (1 + ε)) ≤ c2 * T ^ (599 / 600 : ℝ) := by
      calc 4 * cF (T₁ + H) H ε * (Zl (1 + ε) * Zl (1 + ε))
          ≤ 4 * ((7 * Kphi + 3 * KW) * T ^ (599 / 600 : ℝ)) * (Zl (1 + ε) * Zl (1 + ε)) := by gcongr
        _ = _ := by ring
    -- (c)
    have tc : Cn * (12 * A * M₀) ≤ c3 * T ^ (599 / 600 : ℝ) := by
      have : (M₀ : ℝ) ≤ T ^ (599 / 600 : ℝ) := hM₀H.trans (rpow_le_rpow_T hT1 (by norm_num))
      calc Cn * (12 * A * M₀) = Cn * (12 * A) * M₀ := by ring
        _ ≤ Cn * (12 * A) * T ^ (599 / 600 : ℝ) := by gcongr
    -- (d)
    have td : Cn * (1 + Real.exp (ellT (T₁ + H)) / H) * Real.exp (ellT (T₁ + H)) ^ (1 + ε) *
        (36 / (h₂ : ℝ) * Su (1 + ε)) ≤ c4 * T ^ (599 / 600 : ℝ) := by
      have hE := E_le hH0.le h16 hT₁ hHT
      have hE0 : 0 < Real.exp (ellT (T₁ + H)) := Real.exp_pos _
      have d1 : 1 + Real.exp (ellT (T₁ + H)) / H ≤ 2 * T ^ (1 / 300 : ℝ) := by
        have : Real.exp (ellT (T₁ + H)) / H ≤ T ^ (1 / 300 : ℝ) := by
          rw [div_le_iff₀ hH0, hH, ← Real.rpow_add hT0]
          refine hE.trans (le_of_eq ?_); norm_num
        have : 1 ≤ T ^ (1 / 300 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
        linarith
      have d2 : Real.exp (ellT (T₁ + H)) ^ (1 + ε) ≤ T ^ (1 + ε) := Real.rpow_le_rpow hE0.le hE (by norm_num)
      have d3 : 36 / (h₂ : ℝ) ≤ 36 * (2 * T ^ (-(1 / 150 : ℝ))) := by
        have hpos : 0 < T ^ (1 / 150 : ℝ) := by positivity
        rw [Real.rpow_neg hT0.le, div_le_iff₀ (by linarith)]
        have : T ^ (1 / 150 : ℝ) ≤ 2 * h₂ := by linarith
        calc (36 : ℝ) = 36 * (2 * (T ^ (1 / 150 : ℝ))⁻¹) * (T ^ (1 / 150 : ℝ) / 2) := by field_simp
          _ ≤ 36 * (2 * (T ^ (1 / 150 : ℝ))⁻¹) * h₂ := by gcongr
      have hprod : (2 * T ^ (1 / 300 : ℝ)) * T ^ (1 + ε) * (36 * (2 * T ^ (-(1 / 150 : ℝ)))) =
          144 * T ^ (599 / 600 : ℝ) := by
        have : T ^ (1 / 300 : ℝ) * T ^ (1 + ε) * T ^ (-(1 / 150 : ℝ)) = T ^ (599 / 600 : ℝ) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
        linear_combination 144 * this
      have h36 : 0 ≤ 36 / (h₂ : ℝ) := by positivity
      calc Cn * (1 + Real.exp (ellT (T₁ + H)) / H) * Real.exp (ellT (T₁ + H)) ^ (1 + ε) *
            (36 / (h₂ : ℝ) * Su (1 + ε))
          = Cn * Su (1 + ε) * ((1 + Real.exp (ellT (T₁ + H)) / H) * Real.exp (ellT (T₁ + H)) ^ (1 + ε) *
            (36 / (h₂ : ℝ))) := by ring
        _ ≤ Cn * Su (1 + ε) * ((2 * T ^ (1 / 300 : ℝ)) * T ^ (1 + ε) * (36 * (2 * T ^ (-(1 / 150 : ℝ))))) := by
            gcongr
        _ = _ := by rw [hprod]; ring
    linarith
  -- SCS part
  have hS : ∑ h ∈ Finset.Ico 1 h₂, (T₁ + H) * (K * (h : ℝ) ^ (1 / 21 : ℝ) * ((M₀ : ℝ) ^ (-(1 / 42 : ℝ)) +
      (T₁ + H) * h * (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)))) ≤ c5 * T ^ (599 / 600 : ℝ) := by
    have hT' : T₁ + H ≤ 2 * T := by linarith
    have hM₀0 : 0 < (M₀ : ℝ) := by linarith
    have hterm : ∀ h ∈ Finset.Ico 1 h₂, (T₁ + H) * (K * (h : ℝ) ^ (1 / 21 : ℝ) * ((M₀ : ℝ) ^ (-(1 / 42 : ℝ)) +
        (T₁ + H) * h * (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)))) ≤
        2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T ^ (-(299 / 12600 : ℝ)) +
          2 * T * T ^ (1 / 150 : ℝ) * (4 * T ^ (-(12857 / 12600 : ℝ))))) := by
      intro h hh
      rw [Finset.mem_Ico] at hh
      have hhr : (h : ℝ) ≤ T ^ (1 / 150 : ℝ) := by
        have : (h : ℝ) ≤ h₂ := by exact_mod_cast hh.2.le
        linarith
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      have p1 : (h : ℝ) ^ (1 / 21 : ℝ) ≤ T ^ (1 / 3150 : ℝ) := by
        calc (h : ℝ) ^ (1 / 21 : ℝ) ≤ (T ^ (1 / 150 : ℝ)) ^ (1 / 21 : ℝ) :=
              Real.rpow_le_rpow hh0 hhr (by norm_num)
          _ = T ^ (1 / 3150 : ℝ) := by rw [← Real.rpow_mul hT0.le]; norm_num
      have p2 : (M₀ : ℝ) ^ (-(1 / 42 : ℝ)) ≤ 2 * T ^ (-(299 / 12600 : ℝ)) := by
        calc (M₀ : ℝ) ^ (-(1 / 42 : ℝ)) ≤ (H / 2) ^ (-(1 / 42 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hM₀ge (by norm_num)
          _ = 2 ^ (1 / 42 : ℝ) * T ^ (-(299 / 12600 : ℝ)) := by
              rw [Real.div_rpow hH0.le (by norm_num), hH, ← Real.rpow_mul hT0.le,
                Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
              norm_num; ring
          _ ≤ 2 * T ^ (-(299 / 12600 : ℝ)) := by
              gcongr
              calc (2 : ℝ) ^ (1 / 42 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      have p3 : (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)) ≤ 4 * T ^ (-(12857 / 12600 : ℝ)) := by
        calc (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)) ≤ (H / 2) ^ (-(1 + 1 / 42 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hM₀ge (by norm_num)
          _ = 2 ^ (1 + 1 / 42 : ℝ) * T ^ (-(12857 / 12600 : ℝ)) := by
              rw [Real.div_rpow hH0.le (by norm_num), hH, ← Real.rpow_mul hT0.le,
                Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
              norm_num; ring
          _ ≤ 4 * T ^ (-(12857 / 12600 : ℝ)) := by
              gcongr
              calc (2 : ℝ) ^ (1 + 1 / 42 : ℝ) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 4 := by norm_num
      have hT'0 : 0 ≤ T₁ + H := by linarith
      gcongr
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((h₂ - 1 : ℕ) : ℝ) ≤ T ^ (1 / 150 : ℝ) := by
      have : ((h₂ - 1 : ℕ) : ℝ) ≤ h₂ := by exact_mod_cast Nat.sub_le h₂ 1
      linarith
    have e1 : T ^ (1 / 150 : ℝ) * (2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T ^ (-(299 / 12600 : ℝ))))) =
        4 * K * T ^ (12389 / 12600 : ℝ) := by
      have : T ^ (1 / 150 : ℝ) * T * T ^ (1 / 3150 : ℝ) * T ^ (-(299 / 12600 : ℝ)) = T ^ (12389 / 12600 : ℝ) := by
        simp only [← Real.rpow_add_one hT0.ne', ← Real.rpow_add hT0]; norm_num
      linear_combination 4 * K * this
    have e2 : T ^ (1 / 150 : ℝ) * (2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T * T ^ (1 / 150 : ℝ) *
        (4 * T ^ (-(12857 / 12600 : ℝ)))))) = 16 * K * T ^ (12515 / 12600 : ℝ) := by
      have : T ^ (1 / 150 : ℝ) * T * T ^ (1 / 3150 : ℝ) * T * T ^ (1 / 150 : ℝ) * T ^ (-(12857 / 12600 : ℝ)) =
          T ^ (12515 / 12600 : ℝ) := by
        simp only [← Real.rpow_add_one hT0.ne', ← Real.rpow_add hT0]; norm_num
      linear_combination 16 * K * this
    have hX : 0 ≤ 2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T ^ (-(299 / 12600 : ℝ)) +
          2 * T * T ^ (1 / 150 : ℝ) * (4 * T ^ (-(12857 / 12600 : ℝ))))) := by positivity
    have r1 : T ^ (12389 / 12600 : ℝ) ≤ T ^ (599 / 600 : ℝ) := rpow_le_rpow_T hT1 (by norm_num)
    have r2 : T ^ (12515 / 12600 : ℝ) ≤ T ^ (599 / 600 : ℝ) := rpow_le_rpow_T hT1 (by norm_num)
    calc ((h₂ - 1 : ℕ) : ℝ) * (2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T ^ (-(299 / 12600 : ℝ)) +
          2 * T * T ^ (1 / 150 : ℝ) * (4 * T ^ (-(12857 / 12600 : ℝ))))))
        ≤ T ^ (1 / 150 : ℝ) * (2 * T * (K * T ^ (1 / 3150 : ℝ) * (2 * T ^ (-(299 / 12600 : ℝ)) +
          2 * T * T ^ (1 / 150 : ℝ) * (4 * T ^ (-(12857 / 12600 : ℝ)))))) := by gcongr
      _ = 4 * K * T ^ (12389 / 12600 : ℝ) + 16 * K * T ^ (12515 / 12600 : ℝ) := by
          rw [← e1, ← e2]; ring
      _ ≤ 4 * K * T ^ (599 / 600 : ℝ) + 16 * K * T ^ (599 / 600 : ℝ) := by gcongr
      _ = c5 * T ^ (599 / 600 : ℝ) := by ring
  linarith

end RamanujanTau.GoodSecondTerm2
