/-
# Parameter choice for a generic sequence (with shift `c`)

`gavgOff_le`: `‖Σ_p zz lam T₁ H p‖ ≤ C e^{8c} T^{599/600}` for `H = T^{299/300}`, `T ≥ 2^{300}`,
`16 ≤ T₁ ≤ T`, uniformly in `lam` (`C` absolute).
-/
import RamanujanTau.TwistedMoment.OffTotal
import RamanujanTau.GoodSecondTerm2.Param

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2

/-- Uniform bound for `Zl`. -/
noncomputable def Zb (s : ℝ) : ℝ := 1 / 2 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) + C1 * ∑' n : ℕ, (n : ℝ) ^ (-s))
/-- Uniform bound for `Su`. -/
noncomputable def Sb (s : ℝ) : ℝ := C1 * ∑' n : ℕ, (n : ℝ) ^ (-s)

lemma Zb_nonneg (s : ℝ) : 0 ≤ Zb s := by
  unfold Zb
  have h1 : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) := tsum_nonneg fun n => by positivity
  have h2 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := C1_pos; positivity

lemma Sb_nonneg (s : ℝ) : 0 ≤ Sb s := by
  unfold Sb
  have h2 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := C1_pos; positivity

lemma E_le' {T₁ H T c : ℝ} (hH : 0 ≤ H) (h16 : 16 ≤ T₁) (hT₁ : T₁ ≤ T) (hHT : H ≤ T) :
    Real.exp (ellT ((T₁ + H) * Real.exp (c / 2))) ≤ T * Real.exp (c / 2) := by
  rw [exp_ellT (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  have hq := Real.exp_pos (c / 2)
  have : T₁ + H ≤ T * (2 * Real.pi) := by nlinarith
  nlinarith

lemma rpow_le_Q {E T Q a : ℝ} (hE0 : 0 ≤ E) (hT : 0 ≤ T) (hQ : 1 ≤ Q) (hE : E ≤ T * Q) (ha0 : 0 ≤ a) (ha : a ≤ 2) :
    E ^ a ≤ T ^ a * Q ^ (2 : ℝ) := by
  calc E ^ a ≤ (T * Q) ^ a := Real.rpow_le_rpow hE0 hE ha0
    _ = T ^ a * Q ^ a := Real.mul_rpow hT (by linarith)
    _ ≤ T ^ a * Q ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ ha) (by positivity)

set_option maxHeartbeats 3200000 in
theorem gavgOff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℕ → ℝ) [GoodSeq lam] (T T₁ : ℝ), 2 ^ (300 : ℕ) ≤ T → 16 ≤ T₁ → T₁ ≤ T →
    Summable (zz lam T₁ (T ^ (299 / 300 : ℝ))) ∧
    ‖∑' p, zz lam T₁ (T ^ (299 / 300 : ℝ)) p‖ ≤ C * Real.exp (8 * GoodSeq.c lam) * T ^ (599 / 600 : ℝ) := by
  obtain ⟨K, hK0, hB⟩ := off_avg_bound
  set ε : ℝ := 1 / 600
  set c1 : ℝ := c16 * (Zb (13 / 2) * Zb (11 / 2))
  set c2 : ℝ := 4 * (7 * Kphi + 3 * KW) * (Zb (1 + ε) * Zb (1 + ε))
  set c3 : ℝ := Cn * (12 * C1)
  set c4 : ℝ := Cn * 2 * 36 * 2 * Sb (1 + ε)
  set c5 : ℝ := 2 * K * 2 + 2 * K * 2 * 4
  have hc1 : 0 ≤ c1 := mul_nonneg c16_pos.le (mul_nonneg (Zb_nonneg _) (Zb_nonneg _))
  have hc2 : 0 ≤ c2 := by have := Kphi_pos; have := KW_pos; have := Zb_nonneg (1 + ε); positivity
  have hc3 : 0 ≤ c3 := by have := Cn_pos; have := C1_pos; positivity
  have hc4 : 0 ≤ c4 := by have := Cn_pos; have := Sb_nonneg (1 + ε); positivity
  have hc5 : 0 ≤ c5 := by positivity
  refine ⟨2 * (c1 + c2 + c3 + c4) + 2 * c5, by positivity, fun lam _ T T₁ hT h16 hT₁ => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hT
  clear hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set c := GoodSeq.c lam with hcdef
  have hc : 0 ≤ c := GoodSeq.hc
  set Q : ℝ := Real.exp (c / 2) with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_exp (by linarith)
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
  obtain ⟨hsum, hbd⟩ := hB lam T₁ H ε M₀ h₂ h16 hH0 (by norm_num) (by norm_num) hM₀H hh₂1 hh₂M
  refine ⟨hsum, hbd.trans ?_⟩
  have hTp : (1 : ℝ) ≤ T ^ (599 / 600 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  set E : ℝ := Real.exp (ellT ((T₁ + H) * Q)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE : E ≤ T * Q := E_le' hH0.le h16 hT₁ hHT
  have hEa : ∀ a : ℝ, 0 ≤ a → a ≤ 2 → Real.exp (a * ellT ((T₁ + H) * Q)) ≤ T ^ a * Q ^ (2 : ℝ) := by
    intro a ha0 ha
    rw [mul_comm, Real.exp_mul]
    exact rpow_le_Q hE0.le hT0.le hQ1 hE ha0 ha
  have hQ2 : Q ^ (2 : ℝ) = Q ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hQ3 : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hQ13 : 1 ≤ Q ^ 3 := one_le_pow₀ hQ1
  have hZ13 := Zl_le (lam := lam) (s := 13 / 2) (by norm_num)
  have hZ11 := Zl_le (lam := lam) (s := 11 / 2) (by norm_num)
  have hZe := Zl_le (lam := lam) (s := 1 + ε) (by norm_num)
  have hSu := Su_le (lam := lam) (s := 1 + ε) (by norm_num)
  have hZ13' : Zl lam (13 / 2) ≤ Zb (13 / 2) := hZ13
  have hZ11' : Zl lam (11 / 2) ≤ Zb (11 / 2) := hZ11
  have hZe' : Zl lam (1 + ε) ≤ Zb (1 + ε) := hZe
  have hSu' : Su lam (1 + ε) ≤ Sb (1 + ε) := hSu
  have hZl0 : ∀ s, 0 ≤ Zl lam s := fun s => Zl_nonneg s
  have hSu0 : 0 ≤ Su lam (1 + ε) := tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (by positivity)
  have hCn := Cn_pos
  have hK := Kphi_pos
  have hKW := KW_pos
  -- Bnon
  have hBn : Bnon lam T₁ H ε M₀ h₂ C1 ≤ Real.exp (8 * c) * ((c1 + c2 + c3 + c4) * T ^ (599 / 600 : ℝ)) := by
    unfold Bnon
    rw [← hcdef, ← hQ, ← hEdef]
    have ta : c16 * (Zl lam (13 / 2) * Zl lam (11 / 2)) ≤ Q ^ 3 * (c1 * T ^ (599 / 600 : ℝ)) := by
      have : c16 * (Zl lam (13 / 2) * Zl lam (11 / 2)) ≤ c1 :=
        mul_le_mul_of_nonneg_left (mul_le_mul hZ13' hZ11' (hZl0 _) (Zb_nonneg _)) c16_pos.le
      have : c1 ≤ c1 * T ^ (599 / 600 : ℝ) := le_mul_of_one_le_right hc1 hTp
      have : c1 * T ^ (599 / 600 : ℝ) ≤ Q ^ 3 * (c1 * T ^ (599 / 600 : ℝ)) :=
        le_mul_of_one_le_left (by positivity) hQ13
      linarith
    have hcF : cF ((T₁ + H) * Q) H ε ≤ Q ^ 3 * ((7 * Kphi + 3 * KW) * T ^ (599 / 600 : ℝ)) := by
      unfold cF
      have e1 := hEa (2 * ε) (by norm_num) (by norm_num)
      have e2 := hEa (1 + 2 * ε) (by norm_num) (by norm_num)
      rw [hQ2] at e1 e2
      have r1 : T ^ (2 * ε) ≤ T ^ (599 / 600 : ℝ) := rpow_le_rpow_T hT1 (by norm_num)
      have r2 : T ^ (1 + 2 * ε) / H ≤ T ^ (599 / 600 : ℝ) := by
        rw [hH, div_le_iff₀ (by positivity), ← Real.rpow_add hT0]
        exact rpow_le_rpow_T hT1 (by norm_num)
      have hp : 0 ≤ T ^ (599 / 600 : ℝ) := by positivity
      have a1 : 7 * Kphi * Real.exp (2 * ε * ellT ((T₁ + H) * Q)) ≤ 7 * Kphi * (Q ^ 3 * T ^ (599 / 600 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (e1.trans ?_) (by positivity)
        calc T ^ (2 * ε) * Q ^ 2 ≤ T ^ (599 / 600 : ℝ) * Q ^ 3 := mul_le_mul r1 hQ3 (by positivity) hp
          _ = _ := by ring
      have a2 : 3 * KW / H * Real.exp ((1 + 2 * ε) * ellT ((T₁ + H) * Q)) ≤ 3 * KW * (Q ^ 3 * T ^ (599 / 600 : ℝ)) := by
        calc 3 * KW / H * Real.exp ((1 + 2 * ε) * ellT ((T₁ + H) * Q)) ≤ 3 * KW / H * (T ^ (1 + 2 * ε) * Q ^ 2) := by
              gcongr
          _ = 3 * KW * (T ^ (1 + 2 * ε) / H * Q ^ 2) := by ring
          _ ≤ 3 * KW * (T ^ (599 / 600 : ℝ) * Q ^ 3) := by
              gcongr
          _ = _ := by ring
      nlinarith
    have tb : 4 * cF ((T₁ + H) * Q) H ε * (Zl lam (1 + ε) * Zl lam (1 + ε)) ≤ Q ^ 3 * (c2 * T ^ (599 / 600 : ℝ)) := by
      have hZZ : Zl lam (1 + ε) * Zl lam (1 + ε) ≤ Zb (1 + ε) * Zb (1 + ε) :=
        mul_le_mul hZe' hZe' (hZl0 _) (Zb_nonneg _)
      have hcF0 : 0 ≤ cF ((T₁ + H) * Q) H ε := by unfold cF; positivity
      calc 4 * cF ((T₁ + H) * Q) H ε * (Zl lam (1 + ε) * Zl lam (1 + ε))
          ≤ 4 * (Q ^ 3 * ((7 * Kphi + 3 * KW) * T ^ (599 / 600 : ℝ))) * (Zb (1 + ε) * Zb (1 + ε)) := by
            gcongr
            exact mul_nonneg (hZl0 _) (hZl0 _)
        _ = _ := by ring
    have tc : Cn * (12 * C1 * M₀) ≤ Q ^ 3 * (c3 * T ^ (599 / 600 : ℝ)) := by
      have : (M₀ : ℝ) ≤ T ^ (599 / 600 : ℝ) := hM₀H.trans (rpow_le_rpow_T hT1 (by norm_num))
      have h1 : Cn * (12 * C1 * M₀) ≤ c3 * T ^ (599 / 600 : ℝ) := by
        calc Cn * (12 * C1 * M₀) = Cn * (12 * C1) * M₀ := by ring
          _ ≤ Cn * (12 * C1) * T ^ (599 / 600 : ℝ) := by gcongr
      have : c3 * T ^ (599 / 600 : ℝ) ≤ Q ^ 3 * (c3 * T ^ (599 / 600 : ℝ)) :=
        le_mul_of_one_le_left (by positivity) hQ13
      linarith
    have td : Cn * (1 + E / H) * E ^ (1 + ε) * (36 / (h₂ : ℝ) * Su lam (1 + ε)) ≤
        Q ^ 3 * (c4 * T ^ (599 / 600 : ℝ)) := by
      have d1 : 1 + E / H ≤ 2 * Q * T ^ (1 / 300 : ℝ) := by
        have : E / H ≤ Q * T ^ (1 / 300 : ℝ) := by
          rw [div_le_iff₀ hH0, hH]
          calc E ≤ T * Q := hE
            _ = Q * T ^ (1 / 300 : ℝ) * T ^ (299 / 300 : ℝ) := by
                rw [mul_assoc, ← Real.rpow_add hT0]; norm_num; ring
        have : 1 ≤ T ^ (1 / 300 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
        nlinarith
      have d2 : E ^ (1 + ε) ≤ T ^ (1 + ε) * Q ^ 2 := by
        have := rpow_le_Q hE0.le hT0.le hQ1 hE (a := 1 + ε) (by norm_num) (by norm_num)
        rwa [hQ2] at this
      have d3 : 36 / (h₂ : ℝ) ≤ 36 * (2 * T ^ (-(1 / 150 : ℝ))) := by
        have hpos : 0 < T ^ (1 / 150 : ℝ) := by positivity
        rw [Real.rpow_neg hT0.le, div_le_iff₀ (by linarith)]
        have : T ^ (1 / 150 : ℝ) ≤ 2 * h₂ := by linarith
        calc (36 : ℝ) = 36 * (2 * (T ^ (1 / 150 : ℝ))⁻¹) * (T ^ (1 / 150 : ℝ) / 2) := by field_simp
          _ ≤ 36 * (2 * (T ^ (1 / 150 : ℝ))⁻¹) * h₂ := by gcongr
      have hprod : (2 * Q * T ^ (1 / 300 : ℝ)) * (T ^ (1 + ε) * Q ^ 2) * (36 * (2 * T ^ (-(1 / 150 : ℝ)))) =
          144 * Q ^ 3 * T ^ (599 / 600 : ℝ) := by
        have : T ^ (1 / 300 : ℝ) * T ^ (1 + ε) * T ^ (-(1 / 150 : ℝ)) = T ^ (599 / 600 : ℝ) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
        linear_combination 144 * Q ^ 3 * this
      have h36 : 0 ≤ 36 / (h₂ : ℝ) := by positivity
      have hE1 : 0 ≤ 1 + E / H := by positivity
      have hEe : 0 ≤ E ^ (1 + ε) := by positivity
      calc Cn * (1 + E / H) * E ^ (1 + ε) * (36 / (h₂ : ℝ) * Su lam (1 + ε))
          = Cn * Su lam (1 + ε) * ((1 + E / H) * E ^ (1 + ε) * (36 / (h₂ : ℝ))) := by ring
        _ ≤ Cn * Sb (1 + ε) * ((2 * Q * T ^ (1 / 300 : ℝ)) * (T ^ (1 + ε) * Q ^ 2) *
              (36 * (2 * T ^ (-(1 / 150 : ℝ))))) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hSu' hCn.le) _ (by positivity)
              (mul_nonneg hCn.le (Sb_nonneg _))
            exact mul_le_mul (mul_le_mul d1 d2 hEe (by positivity)) d3 h36 (by positivity)
        _ = _ := by rw [hprod]; ring
    have hE8 : Real.exp (6 * c) * Q ^ 3 ≤ Real.exp (8 * c) := by
      rw [hQ, ← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    have hsum4 : 0 ≤ (c1 + c2 + c3 + c4) * T ^ (599 / 600 : ℝ) := by positivity
    calc Real.exp (6 * c) * (c16 * (Zl lam (13 / 2) * Zl lam (11 / 2)) +
          4 * cF ((T₁ + H) * Q) H ε * (Zl lam (1 + ε) * Zl lam (1 + ε)) + Cn * (12 * C1 * M₀) +
          Cn * (1 + E / H) * E ^ (1 + ε) * (36 / (h₂ : ℝ) * Su lam (1 + ε)))
        ≤ Real.exp (6 * c) * (Q ^ 3 * ((c1 + c2 + c3 + c4) * T ^ (599 / 600 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          nlinarith
      _ = (Real.exp (6 * c) * Q ^ 3) * ((c1 + c2 + c3 + c4) * T ^ (599 / 600 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hE8 hsum4
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
  have he8 : 1 ≤ Real.exp (8 * c) := Real.one_le_exp (by linarith)
  have hp0 : 0 ≤ T ^ (599 / 600 : ℝ) := by positivity
  have : c5 * T ^ (599 / 600 : ℝ) ≤ Real.exp (8 * c) * (c5 * T ^ (599 / 600 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) he8
  nlinarith

end RamanujanTau.TwistedMoment
