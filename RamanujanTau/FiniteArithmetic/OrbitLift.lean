import RamanujanTau.BoylanWebb.InductionSeq

/-! Hensel lifting for a recurrence of any fixed shift. The precision increases
by one per iteration when the divided error returns to a rank-one image. -/

set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open AtkinOBrien BoylanWebb
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem lift_sequence_mem (s : ℕ) (ϖ κ : R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule R M)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : R, ∃ y : M, x = c • L b + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd ϖ 1 (L (β + s) - κ • L β)) :
    ∃ K : ℕ → R, K 0 = κ ∧ (∀ j, ∃ d : R, K (j + 1) = K j + ϖ ^ (j + 1) * d) ∧
      ∀ j β, j + 1 ≤ β → ∃ g ∈ A₂ β, L (β + s) - K j • L β = ϖ ^ (j + 1) • g := by
  -- `P b k`: for all `β ≥ b`, `L(β+s) − k L(β) = ϖ^b g` with `g ∈ A₂ β`
  let P : ℕ → R → Prop := fun b k => ∀ β, b ≤ β → ∃ g ∈ A₂ β, L (β + s) - k • L β = ϖ ^ b • g
  have he : ∀ k : R, ∀ β, 1 ≤ β → L (β + 1 + s) - k • L (β + 1) = T β (L (β + s) - k • L β) := by
    intro k β hβ
    rw [map_sub, map_smul, show β + 1 + s = (β + s) + 1 by ring, hLT (β + s) (by omega), hTper, hLT β hβ]
  have uniq : ∀ (b : ℕ) (g g' : M), ϖ ^ b • g = ϖ ^ b • g' → g = g' := by
    intro b g g' h
    exact sub_eq_zero.mp (cancel_pow ϖ hreg b _ (by rw [smul_sub, h, sub_self]))
  have memA₁ : ∀ (k : R) β, 1 ≤ β → L (β + s) - k • L β ∈ A₁ β := by
    intro k β hβ
    have h2 : L (β + s) ∈ A₁ β := by rw [← hA₁per β]; exact hL (β + s) (by omega)
    exact Submodule.sub_mem _ h2 (Submodule.smul_mem _ _ (hL β hβ))
  have base : P 1 κ := by
    intro β hβ
    obtain ⟨y, hy⟩ := hbase β hβ
    rw [pow_one] at hy
    exact ⟨y, hdiv β hβ _ (memA₁ κ β hβ) y hy, by rw [pow_one]; exact hy⟩
  have step : ∀ b, 1 ≤ b → ∀ k, P b k → ∃ d : R, P (b + 1) (k + ϖ ^ b * d) := by
    intro b hb k hk
    choose! G hGmem hGeq using hk
    have hrec : ∀ β (h : b ≤ β), G (β + 1) = T β (G β) := by
      intro β h
      apply uniq b
      rw [← hGeq (β + 1) (by omega), he k β (by omega), hGeq β h, map_smul]
    have hA1 : ∀ β (h : b ≤ β), G (β + 1) ∈ A₁ (β + 1) := by
      intro β h
      rw [hrec β h]; exact hT β (by omega) _ (hGmem β h)
    obtain ⟨c, h0, hc⟩ := hlead (b + 1) (by omega) _ (hA1 b le_rfl)
    have claim : ∀ i, ∃ h : M, G (b + 1 + i) = c • L (b + 1 + i) + ϖ • h := by
      intro i
      induction i with
      | zero => exact ⟨h0, hc⟩
      | succ i ih =>
        obtain ⟨h, hh⟩ := ih
        refine ⟨T (b + 1 + i) h, ?_⟩
        rw [show b + 1 + (i + 1) = b + 1 + i + 1 by ring, hrec (b + 1 + i) (by omega), hh, map_add,
          map_smul, map_smul, ← hLT _ (by omega)]
    refine ⟨c, fun β hβ => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, β = b + 1 + i := ⟨β - (b + 1), by omega⟩
    obtain ⟨h, hh⟩ := claim i
    have hGA : G (b + 1 + i) ∈ A₁ (b + 1 + i) := by
      rw [show b + 1 + i = (b + i) + 1 by ring]; exact hA1 (b + i) (by omega)
    have hx : G (b + 1 + i) - c • L (b + 1 + i) = ϖ • h := by rw [hh]; abel
    refine ⟨h, hdiv _ (by omega) _ (Submodule.sub_mem _ hGA (Submodule.smul_mem _ _ (hL _ (by omega)))) h hx, ?_⟩
    rw [add_smul, ← sub_sub, hGeq _ (by omega), mul_smul, ← smul_sub, hx, smul_smul, ← pow_succ]
  -- assemble the constants by recursion
  let F : ∀ j : ℕ, {k : R // P (j + 1) k} := fun j => Nat.rec ⟨κ, base⟩
    (fun j ih => ⟨ih.1 + ϖ ^ (j + 1) * Classical.choose (step (j + 1) (by omega) ih.1 ih.2),
      Classical.choose_spec (step (j + 1) (by omega) ih.1 ih.2)⟩) j
  exact ⟨fun j => (F j).1, rfl, fun j => ⟨_, rfl⟩, fun j β hβ => (F j).2 β hβ⟩

theorem lift_sequence (s : ℕ) (ϖ κ : R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule R M)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : R, ∃ y : M, x = c • L b + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd ϖ 1 (L (β + s) - κ • L β)) :
    ∃ K : ℕ → R, K 0 = κ ∧ (∀ j, ∃ d : R, K (j + 1) = K j + ϖ ^ (j + 1) * d) ∧
      ∀ j β, j + 1 ≤ β → Dvd ϖ (j + 1) (L (β + s) - K j • L β) := by
  obtain ⟨K, h0, hs, h⟩ := lift_sequence_mem s ϖ κ T L A₁ A₂ hreg hTper hLT hA₁per hL hT hlead hdiv hbase
  exact ⟨K, h0, hs, fun j β hβ => let ⟨g, _, hg⟩ := h j β hβ; ⟨g, hg⟩⟩

theorem lift_padic (s : ℕ) (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (κ : ℤ_[p]) (T : ℕ → M →ₗ[ℤ_[p]] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule ℤ_[p] M)
    (hreg : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : ℤ_[p], ∃ y : M, x = c • L b + (p : ℤ_[p]) • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = (p : ℤ_[p]) • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd (p : ℤ_[p]) 1 (L (β + s) - κ • L β)) :
    ∃ κlim : ℤ_[p], (∃ d : ℤ_[p], κlim = κ + p * d) ∧
      ∀ b, 1 ≤ b → Dvd (p : ℤ_[p]) b (L (b + s) - κlim • L b) := by
  obtain ⟨K, hK0, hKs, hKd⟩ := lift_sequence s (p : ℤ_[p]) κ T L A₁ A₂ hreg hTper hLT hA₁per hL hT hlead hdiv
    hbase
  obtain ⟨κlim, hκ⟩ := exists_limit_padic p K hKs
  refine ⟨κlim, ?_, fun b hb => ?_⟩
  · obtain ⟨d, hd⟩ := hκ 0
    exact ⟨d, by rw [hd, hK0, zero_add, pow_one]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
    obtain ⟨g, hg⟩ := hKd j (j + 1) le_rfl
    obtain ⟨d, hd⟩ := hκ j
    refine ⟨g - d • L (j + 1), ?_⟩
    rw [hd, add_smul, ← sub_sub, hg, smul_sub, mul_smul]

theorem lift_padic_mem (s : ℕ) (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (κ : ℤ_[p]) (T : ℕ → M →ₗ[ℤ_[p]] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule ℤ_[p] M)
    (hreg : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : ℤ_[p], ∃ y : M, x = c • L b + (p : ℤ_[p]) • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = (p : ℤ_[p]) • y → y ∈ A₂ b)
    (hL₂ : ∀ b, 1 ≤ b → L b ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd (p : ℤ_[p]) 1 (L (β + s) - κ • L β)) :
    ∃ κlim : ℤ_[p], (∃ d : ℤ_[p], κlim = κ + p * d) ∧
      ∀ b, 1 ≤ b → ∃ g ∈ A₂ b, L (b + s) - κlim • L b = (p : ℤ_[p]) ^ b • g := by
  obtain ⟨K, hK0, hKs, hKd⟩ := lift_sequence_mem s (p : ℤ_[p]) κ T L A₁ A₂ hreg hTper hLT hA₁per hL hT hlead hdiv
    hbase
  obtain ⟨κlim, hκ⟩ := exists_limit_padic p K hKs
  refine ⟨κlim, ?_, fun b hb => ?_⟩
  · obtain ⟨d, hd⟩ := hκ 0
    exact ⟨d, by rw [hd, hK0, zero_add, pow_one]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
    obtain ⟨g, hgmem, hg⟩ := hKd j (j + 1) le_rfl
    obtain ⟨d, hd⟩ := hκ j
    refine ⟨g - d • L (j + 1), (A₂ _).sub_mem hgmem ((A₂ _).smul_mem d (hL₂ _ (by omega))), ?_⟩
    rw [hd, add_smul, ← sub_sub, hg, smul_sub, mul_smul]

end RamanujanTau.FiniteArithmetic
