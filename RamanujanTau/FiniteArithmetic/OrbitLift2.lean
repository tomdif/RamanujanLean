import RamanujanTau.FiniteArithmetic.OrbitLift

/-! Hensel lifting for a second-order recurrence

`L(β+2s) − k₁ L(β+s) − k₀ L(β) ≡ 0 (mod ϖ^b)`, with the precision increasing by one per
iteration when every divided error returns to the rank-two span of `L(b), L(b+s)`
modulo `ϖ`. This is the rank-two analogue of `lift_sequence_mem`.
-/

set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open AtkinOBrien BoylanWebb
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- the second-order error `L(β+2s) − k₁ L(β+s) − k₀ L(β)`. -/
def rec2 (s : ℕ) (L : ℕ → M) (k₀ k₁ : R) (β : ℕ) : M :=
  L (β + 2 * s) - k₁ • L (β + s) - k₀ • L β

theorem lift_sequence_mem2 (s : ℕ) (ϖ k₀ k₁ : R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M)
    (A₁ A₂ : ℕ → Submodule R M)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c₀ c₁ : R, ∃ y : M,
      x = c₀ • L b + c₁ • L (b + s) + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd ϖ 1 (rec2 s L k₀ k₁ β)) :
    ∃ K₀ K₁ : ℕ → R, K₀ 0 = k₀ ∧ K₁ 0 = k₁ ∧
      (∀ j, ∃ d : R, K₀ (j + 1) = K₀ j + ϖ ^ (j + 1) * d) ∧
      (∀ j, ∃ d : R, K₁ (j + 1) = K₁ j + ϖ ^ (j + 1) * d) ∧
      ∀ j β, j + 1 ≤ β → ∃ g ∈ A₂ β, rec2 s L (K₀ j) (K₁ j) β = ϖ ^ (j + 1) • g := by
  let P : ℕ → R × R → Prop := fun b k =>
    ∀ β, b ≤ β → ∃ g ∈ A₂ β, rec2 s L k.1 k.2 β = ϖ ^ b • g
  have hLs : ∀ β, 1 ≤ β → ∀ i, L (β + i * s + 1) = T β (L (β + i * s)) := by
    intro β hβ i
    rw [hLT _ (by omega)]
    congr 1
    induction i with
    | zero => simp
    | succ i ih => rw [show β + (i + 1) * s = (β + i * s) + s by ring, hTper, ih]
  have he : ∀ k : R × R, ∀ β, 1 ≤ β →
      rec2 s L k.1 k.2 (β + 1) = T β (rec2 s L k.1 k.2 β) := by
    intro k β hβ
    have h2 := hLs β hβ 2
    have h1 := hLs β hβ 1
    rw [one_mul] at h1
    rw [rec2, rec2, map_sub, map_sub, map_smul, map_smul, ← hLT β hβ,
      show β + 1 + 2 * s = β + 2 * s + 1 by ring, show β + 1 + s = β + s + 1 by ring, h1, h2]
  have uniq : ∀ (b : ℕ) (g g' : M), ϖ ^ b • g = ϖ ^ b • g' → g = g' := by
    intro b g g' h
    exact sub_eq_zero.mp (cancel_pow ϖ hreg b _ (by rw [smul_sub, h, sub_self]))
  have hLA : ∀ β, 1 ≤ β → ∀ i, L (β + i * s) ∈ A₁ β := by
    intro β hβ i
    induction i with
    | zero => simpa using hL β hβ
    | succ i ih =>
      have := hL (β + (i + 1) * s) (by omega)
      rw [show β + (i + 1) * s = (β + i * s) + s by ring] at this ⊢
      rw [hA₁per] at this
      -- `A₁ (β + i*s) = A₁ β` by periodicity
      have hper : ∀ i, A₁ (β + i * s) = A₁ β := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [show β + (i + 1) * s = (β + i * s) + s by ring, hA₁per, ih]
      rwa [hper] at this
  have hL1 : ∀ β, 1 ≤ β → L (β + s) ∈ A₁ β := fun β hβ => by simpa using hLA β hβ 1
  have hL2 : ∀ β, 1 ≤ β → L (β + 2 * s) ∈ A₁ β := fun β hβ => by
    simpa [mul_comm] using hLA β hβ 2
  have memA₁ : ∀ k : R × R, ∀ β, 1 ≤ β → rec2 s L k.1 k.2 β ∈ A₁ β := by
    intro k β hβ
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (hL2 β hβ) (Submodule.smul_mem _ _ (hL1 β hβ)))
      (Submodule.smul_mem _ _ (hL β hβ))
  have base : P 1 (k₀, k₁) := by
    intro β hβ
    obtain ⟨y, hy⟩ := hbase β hβ
    rw [pow_one] at hy
    exact ⟨y, hdiv β hβ _ (memA₁ (k₀, k₁) β hβ) y hy, by rw [pow_one]; exact hy⟩
  have step : ∀ b, 1 ≤ b → ∀ k : R × R, P b k →
      ∃ d : R × R, P (b + 1) (k.1 + ϖ ^ b * d.1, k.2 + ϖ ^ b * d.2) := by
    intro b hb k hk
    choose! G hGmem hGeq using hk
    have hrec : ∀ β (h : b ≤ β), G (β + 1) = T β (G β) := by
      intro β h
      apply uniq b
      rw [← hGeq (β + 1) (by omega), he k β (by omega), hGeq β h, map_smul]
    have hA1 : ∀ β (h : b ≤ β), G (β + 1) ∈ A₁ (β + 1) := by
      intro β h
      rw [hrec β h]; exact hT β (by omega) _ (hGmem β h)
    obtain ⟨c₀, c₁, h0, hc⟩ := hlead (b + 1) (by omega) _ (hA1 b le_rfl)
    have claim : ∀ i, ∃ h : M,
        G (b + 1 + i) = c₀ • L (b + 1 + i) + c₁ • L (b + 1 + i + s) + ϖ • h := by
      intro i
      induction i with
      | zero => exact ⟨h0, by simpa using hc⟩
      | succ i ih =>
        obtain ⟨h, hh⟩ := ih
        refine ⟨T (b + 1 + i) h, ?_⟩
        have h1 := hLs (b + 1 + i) (by omega) 1
        rw [one_mul] at h1
        rw [show b + 1 + (i + 1) = b + 1 + i + 1 by ring, hrec (b + 1 + i) (by omega), hh, map_add,
          map_add, map_smul, map_smul, map_smul, ← hLT _ (by omega), ← h1,
          show b + 1 + i + 1 + s = b + 1 + i + s + 1 by ring]
    refine ⟨(c₀, c₁), fun β hβ => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, β = b + 1 + i := ⟨β - (b + 1), by omega⟩
    obtain ⟨h, hh⟩ := claim i
    have hGA : G (b + 1 + i) ∈ A₁ (b + 1 + i) := by
      rw [show b + 1 + i = (b + i) + 1 by ring]; exact hA1 (b + i) (by omega)
    have hx : G (b + 1 + i) - c₀ • L (b + 1 + i) - c₁ • L (b + 1 + i + s) = ϖ • h := by
      rw [hh]; abel
    refine ⟨h, hdiv _ (by omega) _ (Submodule.sub_mem _ (Submodule.sub_mem _ hGA
      (Submodule.smul_mem _ _ (hL _ (by omega)))) (Submodule.smul_mem _ _ (hL1 _ (by omega)))) h hx, ?_⟩
    have hG := hGeq (b + 1 + i) (by omega)
    simp only [rec2] at hG ⊢
    have : L (b + 1 + i + 2 * s) - (k.2 + ϖ ^ b * c₁) • L (b + 1 + i + s) -
        (k.1 + ϖ ^ b * c₀) • L (b + 1 + i) =
        (L (b + 1 + i + 2 * s) - k.2 • L (b + 1 + i + s) - k.1 • L (b + 1 + i)) -
          ϖ ^ b • (c₀ • L (b + 1 + i) + c₁ • L (b + 1 + i + s)) := by
      simp only [add_smul, mul_smul, smul_add]; abel
    rw [this, hG, ← smul_sub, show G (b + 1 + i) - (c₀ • L (b + 1 + i) + c₁ • L (b + 1 + i + s)) =
      ϖ • h by rw [← hx]; abel, smul_smul, ← pow_succ]
  let F : ∀ j : ℕ, {k : R × R // P (j + 1) k} := fun j => Nat.rec ⟨(k₀, k₁), base⟩
    (fun j ih => ⟨(ih.1.1 + ϖ ^ (j + 1) * (Classical.choose (step (j + 1) (by omega) ih.1 ih.2)).1,
      ih.1.2 + ϖ ^ (j + 1) * (Classical.choose (step (j + 1) (by omega) ih.1 ih.2)).2),
      Classical.choose_spec (step (j + 1) (by omega) ih.1 ih.2)⟩) j
  exact ⟨fun j => (F j).1.1, fun j => (F j).1.2, rfl, rfl, fun j => ⟨_, rfl⟩, fun j => ⟨_, rfl⟩,
    fun j β hβ => (F j).2 β hβ⟩

/-- **ℓ-adic second-order recurrence.** -/
theorem lift_padic_mem2 (s : ℕ) (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (k₀ k₁ : ℤ_[p]) (T : ℕ → M →ₗ[ℤ_[p]] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule ℤ_[p] M)
    (hreg : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c₀ c₁ : ℤ_[p], ∃ y : M,
      x = c₀ • L b + c₁ • L (b + s) + (p : ℤ_[p]) • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = (p : ℤ_[p]) • y → y ∈ A₂ b)
    (hL₂ : ∀ b, 1 ≤ b → L b ∈ A₂ b) (hL₂s : ∀ b, 1 ≤ b → L (b + s) ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd (p : ℤ_[p]) 1 (rec2 s L k₀ k₁ β)) :
    ∃ κ₀ κ₁ : ℤ_[p], (∃ d : ℤ_[p], κ₀ = k₀ + p * d) ∧ (∃ d : ℤ_[p], κ₁ = k₁ + p * d) ∧
      ∀ b, 1 ≤ b → ∃ g ∈ A₂ b, rec2 s L κ₀ κ₁ b = (p : ℤ_[p]) ^ b • g := by
  obtain ⟨K₀, K₁, h0, h1, hs0, hs1, hKd⟩ := lift_sequence_mem2 s (p : ℤ_[p]) k₀ k₁ T L A₁ A₂ hreg
    hTper hLT hA₁per hL hT hlead hdiv hbase
  obtain ⟨κ₀, hκ₀⟩ := exists_limit_padic p K₀ hs0
  obtain ⟨κ₁, hκ₁⟩ := exists_limit_padic p K₁ hs1
  refine ⟨κ₀, κ₁, ?_, ?_, fun b hb => ?_⟩
  · obtain ⟨d, hd⟩ := hκ₀ 0
    exact ⟨d, by rw [hd, h0, zero_add, pow_one]⟩
  · obtain ⟨d, hd⟩ := hκ₁ 0
    exact ⟨d, by rw [hd, h1, zero_add, pow_one]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
    obtain ⟨g, hgmem, hg⟩ := hKd j (j + 1) le_rfl
    obtain ⟨d₀, hd₀⟩ := hκ₀ j
    obtain ⟨d₁, hd₁⟩ := hκ₁ j
    refine ⟨g - d₁ • L (j + 1 + s) - d₀ • L (j + 1),
      (A₂ _).sub_mem ((A₂ _).sub_mem hgmem ((A₂ _).smul_mem d₁ (hL₂s _ (by omega))))
        ((A₂ _).smul_mem d₀ (hL₂ _ (by omega))), ?_⟩
    have hg' := hg
    simp only [rec2] at hg' ⊢
    rw [hd₀, hd₁, smul_sub, smul_sub, ← hg']
    simp only [add_smul, mul_smul]
    abel

end RamanujanTau.FiniteArithmetic
