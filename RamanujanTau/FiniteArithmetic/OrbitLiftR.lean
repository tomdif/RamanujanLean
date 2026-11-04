import RamanujanTau.FiniteArithmetic.OrbitLift2

/-! Hensel lifting for a recurrence of order `r`

`L(β+rs) − Σ_{j<r} k_j L(β+js) ≡ 0 (mod ϖ^b)`, with the precision increasing by one per
iteration when every divided error returns to the span of `L(b), L(b+s), …, L(b+(r−1)s)`
modulo `ϖ`. `lift_padic_mem2` is the case `r = 2`, stated separately.
-/

set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open AtkinOBrien BoylanWebb
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The order-`r` error `L(β+rs) − Σⱼ kⱼ L(β+js)`. -/
def recR (s : ℕ) {r : ℕ} (L : ℕ → M) (k : Fin r → R) (β : ℕ) : M :=
  L (β + r * s) - ∑ j, k j • L (β + j.val * s)

theorem lift_sequence_memR (s r : ℕ) (ϖ : R) (k : Fin r → R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M)
    (A₁ A₂ : ℕ → Submodule R M)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : Fin r → R, ∃ y : M,
      x = ∑ j, c j • L (b + j.val * s) + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd ϖ 1 (recR s L k β)) :
    ∃ K : ℕ → Fin r → R, K 0 = k ∧
      (∀ j i, ∃ d : R, K (j + 1) i = K j i + ϖ ^ (j + 1) * d) ∧
      ∀ j β, j + 1 ≤ β → ∃ g ∈ A₂ β, recR s L (K j) β = ϖ ^ (j + 1) • g := by
  let P : ℕ → (Fin r → R) → Prop := fun b k =>
    ∀ β, b ≤ β → ∃ g ∈ A₂ β, recR s L k β = ϖ ^ b • g
  have hLs : ∀ β, 1 ≤ β → ∀ i, L (β + i * s + 1) = T β (L (β + i * s)) := by
    intro β hβ i
    rw [hLT _ (by omega)]
    congr 1
    induction i with
    | zero => simp
    | succ i ih => rw [show β + (i + 1) * s = (β + i * s) + s by ring, hTper, ih]
  have he : ∀ k : Fin r → R, ∀ β, 1 ≤ β → recR s L k (β + 1) = T β (recR s L k β) := by
    intro k β hβ
    rw [recR, recR, map_sub, map_sum, show β + 1 + r * s = β + r * s + 1 by ring, hLs β hβ r]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, show β + 1 + j.val * s = β + j.val * s + 1 by ring, hLs β hβ j.val]
  have uniq : ∀ (b : ℕ) (g g' : M), ϖ ^ b • g = ϖ ^ b • g' → g = g' := by
    intro b g g' h
    exact sub_eq_zero.mp (cancel_pow ϖ hreg b _ (by rw [smul_sub, h, sub_self]))
  have hper : ∀ β i, A₁ (β + i * s) = A₁ β := by
    intro β i
    induction i with
    | zero => simp
    | succ i ih => rw [show β + (i + 1) * s = (β + i * s) + s by ring, hA₁per, ih]
  have hLA : ∀ β, 1 ≤ β → ∀ i, L (β + i * s) ∈ A₁ β := by
    intro β hβ i
    have := hL (β + i * s) (by omega)
    rwa [hper] at this
  have memA₁ : ∀ k : Fin r → R, ∀ β, 1 ≤ β → recR s L k β ∈ A₁ β := by
    intro k β hβ
    exact Submodule.sub_mem _ (hLA β hβ r)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLA β hβ j.val))
  have base : P 1 k := by
    intro β hβ
    obtain ⟨y, hy⟩ := hbase β hβ
    rw [pow_one] at hy
    exact ⟨y, hdiv β hβ _ (memA₁ k β hβ) y hy, by rw [pow_one]; exact hy⟩
  have step : ∀ b, 1 ≤ b → ∀ k : Fin r → R, P b k →
      ∃ d : Fin r → R, P (b + 1) (fun i => k i + ϖ ^ b * d i) := by
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
    have claim : ∀ i, ∃ h : M,
        G (b + 1 + i) = ∑ j, c j • L (b + 1 + i + j.val * s) + ϖ • h := by
      intro i
      induction i with
      | zero => exact ⟨h0, by simpa using hc⟩
      | succ i ih =>
        obtain ⟨h, hh⟩ := ih
        refine ⟨T (b + 1 + i) h, ?_⟩
        rw [show b + 1 + (i + 1) = b + 1 + i + 1 by ring, hrec (b + 1 + i) (by omega), hh, map_add,
          map_sum, map_smul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ← hLs _ (by omega) j.val, show b + 1 + i + 1 + j.val * s =
          b + 1 + i + j.val * s + 1 by ring]
    refine ⟨c, fun β hβ => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, β = b + 1 + i := ⟨β - (b + 1), by omega⟩
    obtain ⟨h, hh⟩ := claim i
    have hGA : G (b + 1 + i) ∈ A₁ (b + 1 + i) := by
      rw [show b + 1 + i = (b + i) + 1 by ring]; exact hA1 (b + i) (by omega)
    have hx : G (b + 1 + i) - ∑ j, c j • L (b + 1 + i + j.val * s) = ϖ • h := by
      rw [hh]; abel
    refine ⟨h, hdiv _ (by omega) _ (Submodule.sub_mem _ hGA
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLA _ (by omega) j.val))) h hx, ?_⟩
    have hG := hGeq (b + 1 + i) (by omega)
    have : recR s L (fun i' => k i' + ϖ ^ b * c i') (b + 1 + i) =
        recR s L k (b + 1 + i) - ϖ ^ b • ∑ j, c j • L (b + 1 + i + j.val * s) := by
      simp only [recR, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
      abel
    rw [this, hG, ← smul_sub, show G (b + 1 + i) - ∑ j, c j • L (b + 1 + i + j.val * s) =
      ϖ • h from hx, smul_smul, ← pow_succ]
  let F : ∀ j : ℕ, {k : Fin r → R // P (j + 1) k} := fun j => Nat.rec ⟨k, base⟩
    (fun j ih => ⟨fun i => ih.1 i + ϖ ^ (j + 1) * (Classical.choose (step (j + 1) (by omega) ih.1 ih.2)) i,
      Classical.choose_spec (step (j + 1) (by omega) ih.1 ih.2)⟩) j
  exact ⟨fun j => (F j).1, rfl, fun j i => ⟨_, rfl⟩, fun j β hβ => (F j).2 β hβ⟩

/-- **ℓ-adic recurrence of order `r`.** -/
theorem lift_padic_memR (s r : ℕ) (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module ℤ_[p] M] (k : Fin r → ℤ_[p]) (T : ℕ → M →ₗ[ℤ_[p]] M) (L : ℕ → M)
    (A₁ A₂ : ℕ → Submodule ℤ_[p] M)
    (hreg : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0)
    (hTper : ∀ b, T (b + s) = T b) (hLT : ∀ b, 1 ≤ b → L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + s) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : Fin r → ℤ_[p], ∃ y : M,
      x = ∑ j, c j • L (b + j.val * s) + (p : ℤ_[p]) • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = (p : ℤ_[p]) • y → y ∈ A₂ b)
    (hL₂ : ∀ b, 1 ≤ b → ∀ j : Fin r, L (b + j.val * s) ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd (p : ℤ_[p]) 1 (recR s L k β)) :
    ∃ κ : Fin r → ℤ_[p], (∀ i, ∃ d : ℤ_[p], κ i = k i + p * d) ∧
      ∀ b, 1 ≤ b → ∃ g ∈ A₂ b, recR s L κ b = (p : ℤ_[p]) ^ b • g := by
  obtain ⟨K, h0, hs, hKd⟩ := lift_sequence_memR s r (p : ℤ_[p]) k T L A₁ A₂ hreg
    hTper hLT hA₁per hL hT hlead hdiv hbase
  choose κ hκ using fun i => exists_limit_padic p (fun n => K n i) (fun j => hs j i)
  refine ⟨κ, fun i => ?_, fun b hb => ?_⟩
  · obtain ⟨d, hd⟩ := hκ i 0
    exact ⟨d, by rw [hd, h0, zero_add, pow_one]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
    obtain ⟨g, hgmem, hg⟩ := hKd j (j + 1) le_rfl
    choose d hd using fun i => hκ i j
    refine ⟨g - ∑ i, d i • L (j + 1 + i.val * s),
      (A₂ _).sub_mem hgmem ((A₂ _).sum_mem fun i _ => (A₂ _).smul_mem _ (hL₂ _ (by omega) i)), ?_⟩
    have hk : κ = fun i => K j i + (p : ℤ_[p]) ^ (j + 1) * d i := funext hd
    rw [hk, smul_sub, ← hg]
    simp only [recR, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    abel

end RamanujanTau.FiniteArithmetic
