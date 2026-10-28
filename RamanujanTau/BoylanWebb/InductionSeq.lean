import RamanujanTau.AtkinOBrien.Induction
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Step 3 of the Atkin–O'Brien argument without `hstab`, `hnz` or `hR`

`AtkinOBrien.induction` assumes Boylan–Webb stability at every level (`hstab`), `L b ≢ 0` (`hnz`) and
that every scalar is a unit or divisible by `ϖ` (`hR`). They are only used to show that the correction
`c` in the leading digit vanishes.

Here the correction is absorbed into the constant instead. **`induction_seq`**: from
* the mod-`ϖ` statement for *every* `β ≥ 1`, `L(β+2) ≡ κ L(β) (mod ϖ)` (`hbase`; this is
  `BoylanWebb.CertX.two_step`), and
* the envelope hypotheses `hL`, `hT`, `hlead`, `hdiv`,

one gets constants `K j` with
* `K 0 = κ`;
* `K (j+1) ≡ K j (mod ϖ^{j+1})`;
* `L(β+2) ≡ K j · L(β) (mod ϖ^{j+1})` for every `β ≥ j + 1`.

`K j` is Atkin–O'Brien's `K_{j+1}`. Over a complete ring (`ℤ_ℓ`) its limit `κ_∞` gives
`L(b+2) ≡ κ_∞ L(b) (mod ℓ^b)` for every `b ≥ 1` (`exists_limit_padic`, `induction_padic`).
-/

set_option autoImplicit false

namespace BoylanWebb
open AtkinOBrien

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem induction_seq (ϖ κ : R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule R M)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + 2) = T b) (hLT : ∀ b, L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + 2) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : R, ∃ y : M, x = c • L b + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd ϖ 1 (L (β + 2) - κ • L β)) :
    ∃ K : ℕ → R, K 0 = κ ∧ (∀ j, ∃ d : R, K (j + 1) = K j + ϖ ^ (j + 1) * d) ∧
      ∀ j β, j + 1 ≤ β → Dvd ϖ (j + 1) (L (β + 2) - K j • L β) := by
  -- `P b k`: for all `β ≥ b`, `L(β+2) − k L(β) = ϖ^b g` with `g ∈ A₂ β`
  let P : ℕ → R → Prop := fun b k => ∀ β, b ≤ β → ∃ g ∈ A₂ β, L (β + 2) - k • L β = ϖ ^ b • g
  have he : ∀ k : R, ∀ β, L (β + 1 + 2) - k • L (β + 1) = T β (L (β + 2) - k • L β) := by
    intro k β
    rw [map_sub, map_smul, show β + 1 + 2 = (β + 2) + 1 by ring, hLT (β + 2), hTper, hLT β]
  have uniq : ∀ (b : ℕ) (g g' : M), ϖ ^ b • g = ϖ ^ b • g' → g = g' := by
    intro b g g' h
    exact sub_eq_zero.mp (cancel_pow ϖ hreg b _ (by rw [smul_sub, h, sub_self]))
  have memA₁ : ∀ (k : R) β, 1 ≤ β → L (β + 2) - k • L β ∈ A₁ β := by
    intro k β hβ
    have h2 : L (β + 2) ∈ A₁ β := by rw [← hA₁per β]; exact hL (β + 2) (by omega)
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
      rw [← hGeq (β + 1) (by omega), he, hGeq β h, map_smul]
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
          map_smul, map_smul, ← hLT]
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
  refine ⟨fun j => (F j).1, rfl, fun j => ⟨_, rfl⟩, fun j β hβ => ?_⟩
  obtain ⟨g, -, hg⟩ := (F j).2 β hβ
  exact ⟨g, hg⟩

/-- **ℓ-adic limit of the Atkin–O'Brien constants.** -/
theorem exists_limit_padic (p : ℕ) [Fact p.Prime] (K : ℕ → ℤ_[p])
    (hK : ∀ j, ∃ d : ℤ_[p], K (j + 1) = K j + (p : ℤ_[p]) ^ (j + 1) * d) :
    ∃ κ : ℤ_[p], ∀ j, ∃ d : ℤ_[p], κ = K j + (p : ℤ_[p]) ^ (j + 1) * d := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : (0 : ℝ) < p := by linarith
  set r : ℕ → ℝ := fun n => (p : ℝ) ^ (-(n : ℤ)) with hr
  have hmono : ∀ m n, m ≤ n → r n ≤ r m := by
    intro m n h
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  have hbd : ∀ j i, ‖K (j + i) - K j‖ ≤ r (j + 1) := by
    intro j i
    induction i with
    | zero => simp only [add_zero, sub_self, norm_zero]; positivity
    | succ i ih =>
      obtain ⟨d, hd⟩ := hK (j + i)
      rw [show j + (i + 1) = j + i + 1 by ring, hd,
        show K (j + i) + (p : ℤ_[p]) ^ (j + i + 1) * d - K j = (K (j + i) - K j) + (p : ℤ_[p]) ^ (j + i + 1) * d
          by ring]
      refine le_trans (PadicInt.nonarchimedean _ _) (max_le ih ?_)
      rw [norm_mul, PadicInt.norm_p_pow]
      calc (p : ℝ) ^ (-((j + i + 1 : ℕ) : ℤ)) * ‖d‖ ≤ (p : ℝ) ^ (-((j + i + 1 : ℕ) : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one d) (by positivity)
        _ = r (j + i + 1) := by rw [mul_one]
        _ ≤ r (j + 1) := hmono _ _ (by omega)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
    refine this.congr (fun n => ?_)
    show (p : ℝ)⁻¹ ^ n = (p : ℝ) ^ (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hcau : CauchySeq K := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop'.mp hr0) (Metric.ball 0 ε) (Metric.ball_mem_nhds _ hε)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
    rw [dist_eq_norm]
    have h1 := hN (N + 1) (by omega)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    exact lt_of_le_of_lt (hbd N i) h1
  obtain ⟨κ, hκ⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨κ, fun j => ?_⟩
  have hle : ‖κ - K j‖ ≤ r (j + 1) := by
    have ht : Filter.Tendsto (fun n => ‖K n - K j‖) Filter.atTop (nhds ‖κ - K j‖) :=
      (hκ.sub_const (K j)).norm
    refine le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨j, fun n hn => ?_⟩)
    obtain ⟨i, rfl⟩ : ∃ i, n = j + i := ⟨n - j, by omega⟩
    exact hbd j i
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (κ - K j) (j + 1)).mp hle
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨d, by rw [mul_comm, hd]; ring⟩

/-- **Step 3 over `ℤ_ℓ`, with `hstab`/`hnz`/`hR` removed**: a single `κ_∞ ∈ ℤ_ℓ`, `κ_∞ ≡ κ (mod ℓ)`, with
`L(b+2) ≡ κ_∞ L(b) (mod ℓ^b)` for every `b ≥ 1`. -/
theorem induction_padic (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (κ : ℤ_[p]) (T : ℕ → M →ₗ[ℤ_[p]] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule ℤ_[p] M)
    (hreg : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0)
    (hTper : ∀ b, T (b + 2) = T b) (hLT : ∀ b, L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + 2) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : ℤ_[p], ∃ y : M, x = c • L b + (p : ℤ_[p]) • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = (p : ℤ_[p]) • y → y ∈ A₂ b)
    (hbase : ∀ β, 1 ≤ β → Dvd (p : ℤ_[p]) 1 (L (β + 2) - κ • L β)) :
    ∃ κlim : ℤ_[p], (∃ d : ℤ_[p], κlim = κ + p * d) ∧
      ∀ b, 1 ≤ b → Dvd (p : ℤ_[p]) b (L (b + 2) - κlim • L b) := by
  obtain ⟨K, hK0, hKs, hKd⟩ := induction_seq (p : ℤ_[p]) κ T L A₁ A₂ hreg hTper hLT hA₁per hL hT hlead hdiv
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

end BoylanWebb
