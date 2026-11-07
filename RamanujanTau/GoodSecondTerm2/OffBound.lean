/-
# Bound for the averaged off-diagonal `Σ_p zz(p)`
-/
import RamanujanTau.GoodSecondTerm2.SPart

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond
open scoped Interval ComplexConjugate

lemma iI_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

lemma Ptil_neg (Λ lam T H : ℝ) : Ptil Λ (-lam) T H = conj (Ptil Λ lam T H) := by
  unfold Ptil
  rw [map_add, map_mul, ← iI_conj, ← iI_conj]
  have h1 : ∀ t : ℝ, cexp (t * I * ((-lam : ℝ) : ℂ)) = conj (cexp (t * I * (lam : ℂ))) := by
    intro t; rw [← Complex.exp_conj]; congr 1; simp [map_mul, Complex.conj_ofReal]
  congr 1
  · congr 1; funext t; rw [h1, map_mul, Complex.conj_ofReal]
  · congr 1
    · simp [map_div₀, Complex.conj_ofReal]
    · congr 1; funext t; rw [h1, map_mul, Complex.conj_ofReal]

lemma coefD_swap (m n : ℕ) : coefD (n, m) = coefD (m, n) := by
  unfold coefD; simp only; ring_nf

lemma zz_swap (T H : ℝ) (m n : ℕ) : zz T H (n, m) = conj (zz T H (m, n)) := by
  unfold zz
  simp only
  by_cases h : m = n
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, coefD_swap, map_mul, Complex.conj_ofReal]
    congr 1
    rw [show lg m - lg n = -(lg n - lg m) by ring, add_comm (lg n), Ptil_neg]

lemma norm_zz_swap (T H : ℝ) (p : ℕ × ℕ) : ‖zz T H p.swap‖ = ‖zz T H p‖ := by
  rw [show p.swap = (p.2, p.1) from rfl, zz_swap, Complex.norm_conj]

lemma zz_diag (T H : ℝ) (m : ℕ) : zz T H (m, m) = 0 := by simp [zz]

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond
open scoped Interval ComplexConjugate

noncomputable def cF (T' H ε : ℝ) : ℝ :=
  7 * Kphi * Real.exp (2 * ε * ellT T') + 3 * KW / H * Real.exp ((1 + 2 * ε) * ellT T')

noncomputable def gP1 (m n : ℕ) : ℝ := c16 * ((|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(13 / 2 : ℝ))) *
  (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(11 / 2 : ℝ))))
noncomputable def gFar (T' H ε : ℝ) (m n : ℕ) : ℝ := 4 * cF T' H ε *
  ((|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(1 + ε))) * (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(1 + ε))))
noncomputable def gNM (m n : ℕ) : ℝ := ll m n * (4 / ((n : ℝ) - m) ^ 2) * Cn
noncomputable def gNH (T' H ε : ℝ) (m n : ℕ) : ℝ := ll m n * (4 / ((n : ℝ) - m) ^ 2) *
  (Cn * (1 + Real.exp (ellT T') / H) * (Real.exp (ellT T') ^ (1 + ε) * ((m : ℝ) + 1) ^ (-(1 + ε))))

lemma P1_le_gP1 (m n : ℕ) (hmn : m < n) : P1 m n ≤ gP1 m n := by
  have := P1_le m n hmn; unfold gP1; linarith

lemma norm_zz_all {T H ε : ℝ} (hT : 16 ≤ T) (hH : 0 < H) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {m n : ℕ} (hmn : m < n) :
    ‖zz T H (m, n)‖ ≤ gP1 m n + (if 2 * m + 1 ≤ n then gFar (T + H) H ε m n else gNH (T + H) H ε m n) := by
  refine (norm_zz_le' hT hH hmn).trans ?_
  have h1 := P1_le_gP1 m n hmn
  split_ifs with hf
  · have := P2_far (H := H) (T' := T + H) (s := ε) hH hε0.le (by linarith) hf
    unfold gFar cF; linarith
  · have := P2_nearH (H := H) (T' := T + H) hH hε0.le (by linarith) hmn (by omega)
    unfold gNH; linarith

lemma norm_zz_nonS {T H ε : ℝ} (hT : 16 ≤ T) (hH : 0 < H) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {M₀ h₂ : ℕ}
    (hM₀H : (M₀ : ℝ) ≤ H) {m n : ℕ} (hmn : m < n) (hS : ¬(M₀ ≤ m ∧ n - m < h₂)) :
    ‖zz T H (m, n)‖ ≤ gP1 m n + (if 2 * m + 1 ≤ n then gFar (T + H) H ε m n else 0) +
      (if n < 2 * m + 1 ∧ m + 1 ≤ M₀ then gNM m n else 0) +
      (if n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m then gNH (T + H) H ε m n else 0) := by
  refine (norm_zz_le' hT hH hmn).trans ?_
  have h1 := P1_le_gP1 m n hmn
  have hll := ll_nonneg m n
  have g0 : 0 ≤ gNM m n := by unfold gNM; have := Cn_pos; positivity
  have g1 : 0 ≤ gNH (T + H) H ε m n := by
    unfold gNH; have := Cn_pos; positivity
  have g2 : 0 ≤ gFar (T + H) H ε m n := by
    unfold gFar cF; have := Kphi_pos; have := KW_pos
    exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (mul_nonneg (abs_nonneg _) (by positivity)))
  by_cases hf : 2 * m + 1 ≤ n
  · have := P2_far (H := H) (T' := T + H) (s := ε) hH hε0.le (by linarith) hf
    rw [if_pos hf, if_neg (by omega), if_neg (by omega)]
    unfold gFar cF; linarith
  · rw [if_neg hf]
    by_cases hM : m + 1 ≤ M₀
    · have := P2_nearM (H := H) (T' := T + H) hH hmn (by omega)
        (by have : ((m + 1 : ℕ) : ℝ) ≤ M₀ := by exact_mod_cast hM
            push_cast at this; linarith)
      rw [if_pos ⟨by omega, hM⟩]
      unfold gNM
      split_ifs <;> linarith
    · have hh : h₂ ≤ n - m := by omega
      have := P2_nearH (H := H) (T' := T + H) hH hε0.le (by linarith) hmn (by omega)
      rw [if_neg (by omega), if_pos ⟨by omega, hh, by omega⟩]
      unfold gNH; linarith

/-- Nonneg function on `ℕ×ℕ` with uniformly bounded square partial sums is summable. -/
lemma summable_of_sq {f : ℕ × ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) {B : ℝ}
    (hB : ∀ K, ∑ p ∈ Finset.range K ×ˢ Finset.range K, f p ≤ B) : Summable f ∧ ∑' p, f p ≤ B := by
  have hs : ∀ s : Finset (ℕ × ℕ), ∑ p ∈ s, f p ≤ B := by
    intro s
    obtain ⟨K, hK⟩ : ∃ K, s ⊆ Finset.range K ×ˢ Finset.range K := by
      refine ⟨s.sup (fun p => max p.1 p.2) + 1, fun p hp => ?_⟩
      have := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
      have h1 : p.1 ≤ max p.1 p.2 := le_max_left _ _
      have h2 : p.2 ≤ max p.1 p.2 := le_max_right _ _
      simp only at this
      simp only [Finset.mem_product, Finset.mem_range]
      constructor <;> omega
    exact (Finset.sum_le_sum_of_subset_of_nonneg hK (fun p _ _ => hf p)).trans (hB K)
  exact ⟨summable_of_sum_le hf hs, (summable_of_sum_le hf hs).tsum_le_of_sum_le hs⟩

lemma sq_sum_eq (f : ℕ × ℕ → ℝ) (K : ℕ) :
    ∑ p ∈ Finset.range K ×ˢ Finset.range K, f p = ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, f (m, n) := Finset.sum_product _ _ _

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond
open scoped Interval ComplexConjugate

lemma sum_ite_add3 (K : ℕ) (c : ℕ → ℕ → Prop) [∀ m n, Decidable (c m n)] (f g : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if c m n then f m n + g m n else 0) =
      ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if c m n then f m n else 0) +
      ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if c m n then g m n else 0) := by
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

lemma gNH_eq (T' H ε : ℝ) (m n : ℕ) : gNH T' H ε m n =
    (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) *
      (ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε))) := by
  unfold gNH; ring

lemma gNH_coef_nonneg (T' H ε : ℝ) (hH : 0 < H) :
    0 ≤ Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε) := by
  have := Cn_pos; positivity

/-- Sum of the near-`h ≥ h₂` majorant. -/
lemma sum_gNH {T' H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (hε : ε ≤ 2) {h₂ : ℕ} (hh : 1 ≤ h₂) (M₀ K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
      (if m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m) then gNH T' H ε m n else 0) ≤
      (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) * (36 / (h₂ : ℝ) * Su (1 + ε)) := by
  have hc := gNH_coef_nonneg T' H ε hH
  have := sum_nearH hε0 hε hh K
  calc _ ≤ ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
        (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) *
        (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
          ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε)) else 0) := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
        rw [gNH_eq]
        by_cases h1 : m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m)
        · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
        · rw [if_neg h1]
          split_ifs
          · exact mul_nonneg hc (mul_nonneg (mul_nonneg (ll_nonneg m n) (by positivity)) (by positivity))
          · simp
    _ = (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) *
        ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
          ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε)) else 0) := by
        simp_rw [← Finset.mul_sum]
    _ ≤ _ := by gcongr

lemma sum_gNH_all {T' H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (hε : ε ≤ 2) (K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
      (if m < n then (if 2 * m + 1 ≤ n then 0 else gNH T' H ε m n) else 0) ≤
      (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) * (36 / ((1 : ℕ) : ℝ) * Su (1 + ε)) := by
  refine le_trans (le_of_eq ?_) (sum_gNH hH hε0 hε le_rfl 0 K)
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  by_cases h1 : m < n
  · by_cases h2 : 2 * m + 1 ≤ n
    · rw [if_pos h1, if_pos h2, if_neg (by omega)]
    · rw [if_pos h1, if_neg h2, if_pos ⟨h1, by omega, by omega, by omega⟩]
  · rw [if_neg h1, if_neg (by omega)]

lemma sum_gP1 (K : ℕ) : ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n then gP1 m n else 0) ≤
    c16 * (Zl (13 / 2) * Zl (11 / 2)) := by
  have := sum_prod_le (s := 13 / 2) (s' := 11 / 2) (by norm_num) (by norm_num) K (fun m n => m < n)
  have hc := c16_pos
  calc _ = c16 * ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n then
        (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(13 / 2 : ℝ))) * (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(11 / 2 : ℝ)))
        else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
        unfold gP1; split_ifs <;> simp
    _ ≤ _ := by gcongr

lemma sum_gFar {T' H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n then (if 2 * m + 1 ≤ n then gFar T' H ε m n else 0) else 0) ≤
      4 * cF T' H ε * (Zl (1 + ε) * Zl (1 + ε)) := by
  have := sum_prod_le (s := 1 + ε) (s' := 1 + ε) (by linarith) (by linarith) K (fun m n => m < n ∧ 2 * m + 1 ≤ n)
  have hc : 0 ≤ 4 * cF T' H ε := by unfold cF; have := Kphi_pos; have := KW_pos; positivity
  calc _ = 4 * cF T' H ε * ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n ∧ 2 * m + 1 ≤ n then
        (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(1 + ε))) * (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(1 + ε)))
        else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
        unfold gFar; split_ifs <;> first | rfl | (exfalso; omega) | simp
    _ ≤ _ := by gcongr

lemma sum_gNM {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ A * N) (M₀ K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n ∧ (n < 2 * m + 1 ∧ m + 1 ≤ M₀) then gNM m n else 0) ≤
      Cn * (12 * A * M₀) := by
  have := sum_nearM hA0 hA M₀ K
  have hc := Cn_pos
  calc _ = Cn * ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
        (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then ll m n * (4 / ((n : ℝ) - m) ^ 2) else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
        unfold gNM; split_ifs <;> first | ring | simp
    _ ≤ _ := by gcongr

end RamanujanTau.GoodSecondTerm2
