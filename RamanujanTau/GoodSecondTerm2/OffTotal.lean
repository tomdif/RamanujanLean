/-
# Total bound for the averaged off-diagonal

`off_avg_bound`: with `S₊ = {(m,n) : M₀ ≤ m < n < m + h₂}` treated by SCS and everything else by the
second-order first-derivative test,

    ‖Σ_p zz(p)‖ ≤ 2 B_non + 2 Σ_{1≤h<h₂} (T+H) K h^{1/21} (M₀^{−1/42} + (T+H) h M₀^{−1−1/42}).
-/
import RamanujanTau.GoodSecondTerm2.OffBound

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond
open scoped Interval ComplexConjugate

/-- `S₊(m,n)`: `M₀ ≤ m < n`, `n − m < h₂`. -/
def Splus (M₀ h₂ : ℕ) (p : ℕ × ℕ) : Prop := p.1 < p.2 ∧ M₀ ≤ p.1 ∧ p.2 - p.1 < h₂

instance (M₀ h₂ : ℕ) (p : ℕ × ℕ) : Decidable (Splus M₀ h₂ p) := by unfold Splus; infer_instance

noncomputable def Bnon (T H ε : ℝ) (M₀ h₂ : ℕ) (A : ℝ) : ℝ :=
  c16 * (Zl (13 / 2) * Zl (11 / 2)) + 4 * cF (T + H) H ε * (Zl (1 + ε) * Zl (1 + ε)) + Cn * (12 * A * M₀) +
    (Cn * (1 + Real.exp (ellT (T + H)) / H) * Real.exp (ellT (T + H)) ^ (1 + ε)) * (36 / (h₂ : ℝ) * Su (1 + ε))

/-- Square sums of a function vanishing on the diagonal and symmetric in norm. -/
lemma sq_sum_sym {f : ℕ × ℕ → ℝ} (hd : ∀ m, f (m, m) = 0) (hs : ∀ m n, f (n, m) = f (m, n)) (K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, f (m, n) =
      2 * ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n then f (m, n) else 0) := by
  have h1 : ∀ m n, f (m, n) = (if m < n then f (m, n) else 0) + (if n < m then f (m, n) else 0) := by
    intro m n
    rcases lt_trichotomy m n with h | h | h
    · rw [if_pos h, if_neg (by omega)]; ring
    · subst h; simp [hd]
    · rw [if_neg (by omega), if_pos h]; ring
  have h2 : ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if n < m then f (m, n) else 0) =
      ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, (if m < n then f (m, n) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [hs]
    · rfl
  rw [Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => h1 m n]
  have : ∀ m ∈ Finset.range K, ∑ n ∈ Finset.range K, ((if m < n then f (m, n) else 0) + (if n < m then f (m, n) else 0)) =
      (∑ n ∈ Finset.range K, (if m < n then f (m, n) else 0)) + ∑ n ∈ Finset.range K, (if n < m then f (m, n) else 0) :=
    fun m _ => Finset.sum_add_distrib
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, h2]; ring

theorem off_avg_bound : ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ ∀ (T H ε : ℝ) (M₀ h₂ : ℕ), 16 ≤ T → 0 < H →
    0 < ε → ε ≤ 1 / 2 → (M₀ : ℝ) ≤ H → 1 ≤ h₂ → h₂ ≤ M₀ →
    Summable (zz T H) ∧ ‖∑' p, zz T H p‖ ≤ 2 * Bnon T H ε M₀ h₂ A +
      2 * ∑ h ∈ Finset.Ico 1 h₂, (T + H) * (K * (h : ℝ) ^ (1 / 21 : ℝ) * ((M₀ : ℝ) ^ (-(1 / 42 : ℝ)) +
        (T + H) * h * (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)))) := by
  obtain ⟨K, hK0, hK⟩ := norm_Spart_h
  obtain ⟨A, hA0, hA⟩ := exists_rankin
  refine ⟨K, A, hK0, hA0, fun T H ε M₀ h₂ hT hH hε0 hε hM₀H hh₂ hh₂M => ?_⟩
  set T' := T + H
  -- norms are symmetric and vanish on the diagonal
  have hnd : ∀ m, ‖zz T H (m, m)‖ = 0 := fun m => by rw [zz_diag, norm_zero]
  have hns : ∀ m n, ‖zz T H (n, m)‖ = ‖zz T H (m, n)‖ := fun m n => by
    have := norm_zz_swap T H (m, n); simpa using this
  -- summability
  set Ball : ℝ := c16 * (Zl (13 / 2) * Zl (11 / 2)) + 4 * cF T' H ε * (Zl (1 + ε) * Zl (1 + ε)) +
    (Cn * (1 + Real.exp (ellT T') / H) * Real.exp (ellT T') ^ (1 + ε)) * (36 / ((1 : ℕ) : ℝ) * Su (1 + ε)) with hBall
  have hsq_all : ∀ K', ∑ p ∈ Finset.range K' ×ˢ Finset.range K', ‖zz T H p‖ ≤ 2 * Ball := by
    intro K'
    rw [sq_sum_eq, sq_sum_sym (f := fun p => ‖zz T H p‖) hnd (fun m n => hns m n)]
    gcongr
    calc ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then ‖zz T H (m, n)‖ else 0)
        ≤ ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then gP1 m n +
            (if 2 * m + 1 ≤ n then gFar T' H ε m n else gNH T' H ε m n) else 0) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
          by_cases h1 : m < n
          · rw [if_pos h1, if_pos h1]; exact norm_zz_all hT hH hε0 hε h1
          · rw [if_neg h1, if_neg h1]
      _ = ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then gP1 m n else 0) +
          ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then (if 2 * m + 1 ≤ n then gFar T' H ε m n else 0) else 0) +
          ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then (if 2 * m + 1 ≤ n then 0 else gNH T' H ε m n) else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          split_ifs <;> ring
      _ ≤ _ := by
          have := sum_gP1 K'
          have := sum_gFar (T' := T') hH hε0 (ε := ε) K'
          have := sum_gNH_all (T' := T') hH hε0 (by linarith) K'
          rw [hBall]; linarith
  obtain ⟨hsumN, -⟩ := summable_of_sq (fun p => norm_nonneg (zz T H p)) hsq_all
  have hsum : Summable (zz T H) := hsumN.of_norm
  refine ⟨hsum, ?_⟩
  -- split
  set zP : ℕ × ℕ → ℂ := fun p => if Splus M₀ h₂ p then zz T H p else 0 with hzP
  set zM : ℕ × ℕ → ℂ := fun p => if Splus M₀ h₂ p.swap then zz T H p else 0 with hzM
  set zN : ℕ × ℕ → ℂ := fun p => if Splus M₀ h₂ p ∨ Splus M₀ h₂ p.swap then 0 else zz T H p with hzN
  have hdec : ∀ p, zz T H p = zN p + zP p + zM p := by
    intro p
    simp only [hzN, hzP, hzM]
    by_cases h1 : Splus M₀ h₂ p
    · have : ¬Splus M₀ h₂ p.swap := by
        unfold Splus at h1 ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; omega
      rw [if_pos (Or.inl h1), if_pos h1, if_neg this]; ring
    · by_cases h2 : Splus M₀ h₂ p.swap
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]; ring
  have hbN : ∀ p, ‖zN p‖ ≤ ‖zz T H p‖ := fun p => by simp only [hzN]; split_ifs <;> simp
  have hbP : ∀ p, ‖zP p‖ ≤ ‖zz T H p‖ := fun p => by simp only [hzP]; split_ifs <;> simp
  have hbM : ∀ p, ‖zM p‖ ≤ ‖zz T H p‖ := fun p => by simp only [hzM]; split_ifs <;> simp
  have hsN : Summable zN := Summable.of_norm_bounded hsumN hbN
  have hsP : Summable zP := Summable.of_norm_bounded hsumN hbP
  have hsM : Summable zM := Summable.of_norm_bounded hsumN hbM
  have htsum : ∑' p, zz T H p = ∑' p, zN p + ∑' p, zP p + ∑' p, zM p := by
    simp_rw [hdec]; rw [(hsN.add hsP).tsum_add hsM, hsN.tsum_add hsP]
  -- nonnegativity of the majorants
  have g0P : ∀ m n, 0 ≤ gP1 m n := fun m n => by
    unfold gP1; have := c16_pos
    exact mul_nonneg this.le (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (mul_nonneg (abs_nonneg _) (by positivity)))
  have g0F : ∀ m n, 0 ≤ gFar T' H ε m n := fun m n => by
    unfold gFar cF; have := Kphi_pos; have := KW_pos
    exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (mul_nonneg (abs_nonneg _) (by positivity)))
  have g0M : ∀ m n, 0 ≤ gNM m n := fun m n => by
    unfold gNM; have := Cn_pos; exact mul_nonneg (mul_nonneg (ll_nonneg m n) (by positivity)) this.le
  have g0H : ∀ m n, 0 ≤ gNH T' H ε m n := fun m n => by
    unfold gNH; have := Cn_pos
    exact mul_nonneg (mul_nonneg (ll_nonneg m n) (by positivity)) (by positivity)
  -- the non-SCS part
  have hNsq : ∀ K', ∑ p ∈ Finset.range K' ×ˢ Finset.range K', ‖zN p‖ ≤ 2 * Bnon T H ε M₀ h₂ A := by
    intro K'
    have hnd' : ∀ m, ‖zN (m, m)‖ = 0 := fun m => by
      simp only [hzN]; split_ifs
      · simp
      · rw [zz_diag, norm_zero]
    have hns' : ∀ m n, ‖zN (n, m)‖ = ‖zN (m, n)‖ := by
      intro m n; simp only [hzN, Prod.swap_prod_mk]
      by_cases hS : Splus M₀ h₂ (m, n) ∨ Splus M₀ h₂ (n, m)
      · rw [if_pos (Or.comm.mp hS), if_pos hS]
      · rw [if_neg (fun h => hS (Or.comm.mp h)), if_neg hS, hns]
    rw [sq_sum_eq, sq_sum_sym (f := fun p => ‖zN p‖) hnd' hns']
    gcongr
    calc ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then ‖zN (m, n)‖ else 0)
        ≤ ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', ((if m < n then gP1 m n else 0) +
            (if m < n then (if 2 * m + 1 ≤ n then gFar T' H ε m n else 0) else 0) +
            (if m < n ∧ (n < 2 * m + 1 ∧ m + 1 ≤ M₀) then gNM m n else 0) +
            (if m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m) then gNH T' H ε m n else 0)) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
          by_cases h1 : m < n
          · rw [if_pos h1, if_pos h1, if_pos h1]
            have hR : 0 ≤ (if 2 * m + 1 ≤ n then gFar T' H ε m n else 0) := by split_ifs; exacts [g0F m n, le_rfl]
            have hR2 : 0 ≤ (if m < n ∧ (n < 2 * m + 1 ∧ m + 1 ≤ M₀) then gNM m n else 0) := by
              split_ifs; exacts [g0M m n, le_rfl]
            have hR3 : 0 ≤ (if m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m) then gNH T' H ε m n else 0) := by
              split_ifs; exacts [g0H m n, le_rfl]
            simp only [hzN, Prod.swap_prod_mk]
            by_cases hS : Splus M₀ h₂ (m, n) ∨ Splus M₀ h₂ (n, m)
            · rw [if_pos hS, norm_zero]; have := g0P m n; linarith
            · rw [if_neg hS]
              have hb := norm_zz_nonS hT hH hε0 hε hM₀H (h₂ := h₂) h1 (fun h => hS (Or.inl ⟨h1, h.1, h.2⟩))
              have e1 : (if n < 2 * m + 1 ∧ m + 1 ≤ M₀ then gNM m n else 0) =
                  (if m < n ∧ (n < 2 * m + 1 ∧ m + 1 ≤ M₀) then gNM m n else 0) := by
                by_cases hc : n < 2 * m + 1 ∧ m + 1 ≤ M₀
                · rw [if_pos hc, if_pos ⟨h1, hc⟩]
                · rw [if_neg hc, if_neg (fun h => hc h.2)]
              have e2 : (if n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m then gNH T' H ε m n else 0) =
                  (if m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m) then gNH T' H ε m n else 0) := by
                by_cases hc : n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m
                · rw [if_pos hc, if_pos ⟨h1, hc⟩]
                · rw [if_neg hc, if_neg (fun h => hc h.2)]
              rw [e1, e2] at hb
              exact hb
          · rw [if_neg h1, if_neg h1, if_neg h1, if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]
            simp
      _ = ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then gP1 m n else 0) +
          ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n then (if 2 * m + 1 ≤ n then gFar T' H ε m n else 0) else 0) +
          ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K', (if m < n ∧ (n < 2 * m + 1 ∧ m + 1 ≤ M₀) then gNM m n else 0) +
          ∑ m ∈ Finset.range K', ∑ n ∈ Finset.range K',
            (if m < n ∧ (n < 2 * m + 1 ∧ h₂ ≤ n - m ∧ M₀ ≤ m) then gNH T' H ε m n else 0) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ Bnon T H ε M₀ h₂ A := by
          have := sum_gP1 K'
          have := sum_gFar (T' := T') hH hε0 (ε := ε) K'
          have := sum_gNM hA0 hA M₀ K'
          have := sum_gNH (T' := T') hH hε0 (by linarith) hh₂ M₀ K'
          unfold Bnon; linarith
  obtain ⟨-, hNt⟩ := summable_of_sq (fun p => norm_nonneg (zN p)) hNsq
  have hN : ‖∑' p, zN p‖ ≤ 2 * Bnon T H ε M₀ h₂ A :=
    (norm_tsum_le_tsum_norm hsN.norm).trans hNt
  -- the minus part is the conjugate of the plus part
  have hMP : ∑' p, zM p = conj (∑' p, zP p) := by
    rw [Complex.conj_tsum]
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
    congr 1; funext p
    simp only [hzM, hzP, Equiv.prodComm_apply, Prod.swap_swap]
    split_ifs
    · rw [show p.swap = (p.2, p.1) from rfl, zz_swap]
    · simp
  have hM : ‖∑' p, zM p‖ = ‖∑' p, zP p‖ := by rw [hMP, Complex.norm_conj]
  -- the plus part via the parametrization (h, k) ↦ (M₀ + k, M₀ + k + h)
  set g : ℕ × ℕ → ℕ × ℕ := fun q => (M₀ + q.2, M₀ + q.2 + q.1) with hg
  have hginj : Function.Injective g := by
    intro q r hqr
    simp only [hg, Prod.mk.injEq] at hqr
    ext <;> omega
  have hsupp : Function.support zP ⊆ Set.range g := by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [hzP] at hp
    split_ifs at hp with h
    · unfold Splus at h
      exact ⟨(p.2 - p.1, p.1 - M₀), by simp only [hg]; ext <;> simp <;> omega⟩
    · exact absurd rfl hp
  have hPg : ∑' p, zP p = ∑' q, zP (g q) := (hginj.tsum_eq hsupp).symm
  have hsPg : Summable (zP ∘ g) := hsP.comp_injective hginj
  have hval : ∀ q : ℕ × ℕ, zP (g q) = if 1 ≤ q.1 ∧ q.1 < h₂ then zz T H (M₀ + q.2, M₀ + q.2 + q.1) else 0 := by
    intro q
    simp only [hzP, hg, Splus]
    by_cases hc : 1 ≤ q.1 ∧ q.1 < h₂
    · rw [if_pos ⟨by omega, by omega, by omega⟩, if_pos hc]
    · rw [if_neg (fun h => hc ⟨by omega, by omega⟩), if_neg hc]
  have hX : ∑' q, zP (g q) = ∑ h ∈ Finset.Ico 1 h₂, ∑' k, zz T H (M₀ + k, M₀ + k + h) := by
    show ∑' q, (zP ∘ g) q = _
    rw [hsPg.tsum_prod' (fun h => hsPg.prod_factor h)]
    rw [tsum_eq_sum (s := Finset.Ico 1 h₂) (fun h hh => by
      simp only [Function.comp, hval]
      rw [Finset.mem_Ico] at hh
      simp [hh])]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_Ico] at hh
    simp only [Function.comp, hval, if_pos hh]
  have hP : ‖∑' p, zP p‖ ≤ ∑ h ∈ Finset.Ico 1 h₂, (T + H) * (K * (h : ℝ) ^ (1 / 21 : ℝ) *
      ((M₀ : ℝ) ^ (-(1 / 42 : ℝ)) + (T + H) * h * (M₀ : ℝ) ^ (-(1 + 1 / 42 : ℝ)))) := by
    rw [hPg, hX]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    rw [Finset.mem_Ico] at hh
    exact (hK T H M₀ h hT hH hh.1 (by omega)).2
  rw [htsum]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [hM]
  linarith

end RamanujanTau.GoodSecondTerm2
