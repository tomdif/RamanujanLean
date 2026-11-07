/-
# M3 step 6c: polynomial bounds on the quadruple sums

For `(a,b,c,d) ∈ [1,y]⁴`: `|κ| ≤ y²`, `P₁, Q₁ ≤ y²`, `|ρ(m)|, |ρ(m,1−iv)| ≤ m^{K+2}`, so
`|𝒮⁰(v)|, |𝒮(v)| ≤ y^{4K+14}`; `|ε(v)| ≤ 5C₁`.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Final2

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset MeasureTheory RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2 RamanujanTau.SelbergKey
open scoped Real

lemma norm_sum4_le (y : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) {B : ℝ}
    (hf : ∀ a ∈ Icc 1 y, ∀ b ∈ Icc 1 y, ∀ c ∈ Icc 1 y, ∀ d ∈ Icc 1 y, ‖f a b c d‖ ≤ B) :
    ‖sum4 y f‖ ≤ (y : ℝ) ^ 4 * B := by
  unfold sum4
  have hcard : ((Icc 1 y).card : ℝ) = y := by simp
  calc ‖∑ a ∈ Icc 1 y, ∑ b ∈ Icc 1 y, ∑ c ∈ Icc 1 y, ∑ d ∈ Icc 1 y, f a b c d‖
      ≤ ∑ a ∈ Icc 1 y, ∑ b ∈ Icc 1 y, ∑ c ∈ Icc 1 y, ∑ d ∈ Icc 1 y, ‖f a b c d‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 y, ∑ b ∈ Icc 1 y, ∑ c ∈ Icc 1 y, ∑ d ∈ Icc 1 y, B :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun c hc =>
          Finset.sum_le_sum fun d hd => hf a ha b hb c hc d hd
    _ = (y : ℝ) ^ 4 * B := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]; ring

lemma abs_kap_le {y a b c d : ℕ} (ha : a ∈ Icc 1 y) (hb : b ∈ Icc 1 y) (hc : c ∈ Icc 1 y) (hd : d ∈ Icc 1 y) :
    |kap y a b c d| ≤ (y : ℝ) ^ 2 := by
  have hs : ∀ n ∈ Icc 1 y, |HafnerMV2.βSel y n| ≤ Real.sqrt y := fun n hn =>
    (HafnerMV2.abs_βSel_le y n).trans (Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.1 hn).2))
  have hl : (1:ℝ) ≤ (Nat.lcm (a * c) (b * d) : ℝ) := by
    exact_mod_cast Nat.lcm_pos (Nat.mul_pos (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hc).1)
      (Nat.mul_pos (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hd).1)
  unfold kap
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < (Nat.lcm (a * c) (b * d) : ℝ)), abs_mul, abs_mul, abs_mul]
  have hsq : Real.sqrt y * Real.sqrt y * Real.sqrt y * Real.sqrt y = (y : ℝ) ^ 2 := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]; ring
  rw [div_le_iff₀ (by linarith)]
  calc |HafnerMV2.βSel y a| * |HafnerMV2.βSel y b| * |HafnerMV2.βSel y c| * |HafnerMV2.βSel y d|
      ≤ Real.sqrt y * Real.sqrt y * Real.sqrt y * Real.sqrt y := by
        gcongr <;> [exact hs a ha; exact hs b hb; exact hs c hc; exact hs d hd]
    _ = (y : ℝ) ^ 2 := hsq
    _ ≤ (y : ℝ) ^ 2 * (Nat.lcm (a * c) (b * d) : ℝ) := le_mul_of_one_le_right (by positivity) hl

lemma P1_le_sq {y a b c d : ℕ} (ha : a ∈ Icc 1 y) (hc : c ∈ Icc 1 y) : P1 a b c d ≤ y ^ 2 := by
  have h1 : P1 a b c d ≤ a * c := Nat.div_le_self _ _
  have h2 : a * c ≤ y * y := Nat.mul_le_mul (Finset.mem_Icc.1 ha).2 (Finset.mem_Icc.1 hc).2
  nlinarith

lemma Q1_le_sq {y a b c d : ℕ} (hb : b ∈ Icc 1 y) (hd : d ∈ Icc 1 y) : Q1 a b c d ≤ y ^ 2 := by
  have h1 : Q1 a b c d ≤ b * d := Nat.div_le_self _ _
  have h2 : b * d ≤ y * y := Nat.mul_le_mul (Finset.mem_Icc.1 hb).2 (Finset.mem_Icc.1 hd).2
  nlinarith

/-- The constants: `M ≤ 2^K` from `Gp_bound`. -/
lemma rho_bounds : ∃ K : ℕ, ∀ m : ℕ, 1 ≤ m → |rho m| ≤ (m : ℝ) ^ (K + 2) ∧
    ∀ s : ℂ, s.re = 1 → ‖rhoC m s‖ ≤ (m : ℝ) ^ (K + 2) := by
  obtain ⟨M, hM1, hM⟩ := Gp_bound
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt M (by norm_num : (1:ℝ) < 2)
  refine ⟨K, fun m hm => ⟨?_, fun s hs => ?_⟩⟩
  · refine (abs_rho_le hM hm).trans ?_
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_card_pf_le (by linarith) hK.le hm) (by positivity)
  · refine (norm_rhoC_le hM hm hs).trans ?_
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_card_pf_le (by linarith) hK.le hm) (by positivity)

lemma pow_le_ysq {m y : ℕ} (hm : m ≤ y ^ 2) (K : ℕ) : (m : ℝ) ^ (K + 2) ≤ (y : ℝ) ^ (2 * K + 4) := by
  calc (m : ℝ) ^ (K + 2) ≤ ((y : ℝ) ^ 2) ^ (K + 2) := by gcongr; exact_mod_cast hm
    _ = (y : ℝ) ^ (2 * K + 4) := by rw [← pow_mul]; ring_nf

theorem S_bounds : ∃ K : ℕ, ∀ (y : ℕ) (v : ℝ),
    ‖S0v y v‖ ≤ (y : ℝ) ^ (4 * K + 14) ∧ ‖Sv y v‖ ≤ (y : ℝ) ^ (4 * K + 14) := by
  obtain ⟨K, hK⟩ := rho_bounds
  refine ⟨K, fun y v => ⟨?_, ?_⟩⟩
  · unfold S0v
    refine (norm_sum4_le y _ (B := (y : ℝ) ^ 2 * ((y : ℝ) ^ (2 * K + 4) * (y : ℝ) ^ (2 * K + 4)))
      fun a ha b hb c hc d hd => ?_).trans (le_of_eq (by ring))
    have hP := SelbergKeyDiag.P1_pos (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hc).1
      (Finset.mem_Icc.1 hd).1
    have hQ := SelbergKeyDiag.Q1_pos (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hc).1
      (Finset.mem_Icc.1 hd).1
    have e1 : ‖SelbergKey.ev a b c d v‖ = 1 := by
      unfold SelbergKey.ev; rw [show (v : ℂ) * I * _ = ((v * (Real.log (P1 a b c d) + Real.log d - Real.log c) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have e2 : ‖cexp (-((v : ℂ) * I * ((Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2 : ℝ) : ℂ)))‖ = 1 := by
      rw [show -((v : ℂ) * I * ((Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2 : ℝ) : ℂ)) =
        ((-(v * (Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2)) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_mul, norm_mul, e1, e2, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, mul_one, mul_one]
    gcongr
    · exact abs_kap_le ha hb hc hd
    · exact (hK _ hP).1.trans (pow_le_ysq (P1_le_sq ha hc) K)
    · exact (hK _ hQ).1.trans (pow_le_ysq (Q1_le_sq hb hd) K)
  · unfold Sv
    refine (norm_sum4_le y _ (B := (y : ℝ) ^ 2 * ((y : ℝ) ^ (2 * K + 4) * (y : ℝ) ^ (2 * K + 4)))
      fun a ha b hb c hc d hd => ?_).trans (le_of_eq (by ring))
    have hP := SelbergKeyDiag.P1_pos (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hc).1
      (Finset.mem_Icc.1 hd).1
    have hQ := SelbergKeyDiag.Q1_pos (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hc).1
      (Finset.mem_Icc.1 hd).1
    have e1 : ‖SelbergKey.ev a b c d v‖ = 1 := by
      unfold SelbergKey.ev; rw [show (v : ℂ) * I * _ = ((v * (Real.log (P1 a b c d) + Real.log d - Real.log c) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hs : (1 - (v : ℂ) * I).re = 1 := by simp
    rw [norm_mul, norm_mul, norm_mul, e1, Complex.norm_real, Real.norm_eq_abs, mul_one]
    have h1 := abs_kap_le ha hb hc hd
    have h2 := (hK _ hP).2 _ hs |>.trans (pow_le_ysq (P1_le_sq ha hc) K)
    have h3 := (hK _ hQ).2 _ hs |>.trans (pow_le_ysq (Q1_le_sq hb hd) K)
    calc _ = |kap y a b c d| * (‖rhoC (P1 a b c d) (1 - v * I)‖ * ‖rhoC (Q1 a b c d) (1 - v * I)‖) := by ring
      _ ≤ _ := mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)

theorem eps_bound : ∃ Cε : ℝ, 0 ≤ Cε ∧ ∀ v : ℝ, ‖epsv v‖ ≤ Cε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Et_bound
  refine ⟨5 * C₁, by positivity, fun v => ?_⟩
  have hint := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(6 / 5 : ℝ)) < -1) one_pos).const_mul C₁
  unfold epsv
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
  · have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, norm_cpow_I_sub_one ht0, Complex.norm_real, Real.norm_eq_abs]
    calc t⁻¹ * |Et t| ≤ t⁻¹ * (C₁ * t ^ (-(1 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hC₁ t (le_of_lt ht)) (by positivity)
      _ = C₁ * t ^ (-(6 / 5 : ℝ)) := by
          rw [← Real.rpow_neg_one, show t ^ (-1:ℝ) * (C₁ * t ^ (-(1 / 5 : ℝ))) =
            C₁ * (t ^ (-1:ℝ) * t ^ (-(1 / 5 : ℝ))) by ring, ← Real.rpow_add ht0]; norm_num
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]; norm_num; ring

end RamanujanTau.SelbergKeyDiag2
