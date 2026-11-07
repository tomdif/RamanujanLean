/-
# The polarised sequences `g_σ = r(ι_k + σ ι_h)` are `GoodSeq`s

For `h, k ≥ 1`, `|σ| ≤ 1` and `r² S(h,k) ≤ 1` with `S(h,k) = 4(A + C + 1)(hk)^{24}`,
`gS h k σ r` satisfies the normalised Rankin and SCS bounds, with shift `c = log(hk)`.
-/
import RamanujanTau.TwistedMoment.TwCoef

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Finset

lemma iota_scs : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b ℓ N : ℕ), 1 ≤ a → 1 ≤ b → 1 ≤ ℓ →
    |∑ x ∈ Icc 1 N, iota a x * iota b (x + ℓ)| ≤
      C * ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.SCS2Coprime.scs2_general
  refine ⟨C, hC0, fun a b ℓ N ha hb hℓ => ?_⟩
  obtain ⟨Nt, hNt, he⟩ := prefix_eq ha hb hℓ N
  rw [he]
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  refine (hC b a (ℓ : ℤ) Nt hb ha hℓ0).trans ?_
  have e1 : |((ℓ : ℤ) : ℝ)| = (ℓ : ℝ) := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg _)
  rw [e1, show b * a = a * b from mul_comm b a]
  have hN : ((Nt : ℕ) : ℝ) ^ (1 - 1 / 21 : ℝ) ≤ ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
    exact_mod_cast hNt
  have h1 : 0 ≤ (ℓ : ℝ) ^ (1 / 21 : ℝ) := by positivity
  have h2 : 0 ≤ ((a * b : ℕ) : ℝ) ^ 12 := by positivity
  calc C * ((Nt : ℕ) : ℝ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12
      ≤ C * ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12 := by
        gcongr
    _ = _ := rfl

/-- Rankin constant for `ι`. -/
noncomputable def Arank : ℝ := Classical.choose iota_rankin
lemma Arank_nonneg : 0 ≤ Arank := (Classical.choose_spec iota_rankin).1
lemma Arank_spec (a N : ℕ) (ha : 1 ≤ a) : ∑ x ∈ Icc 1 N, iota a x ^ 2 ≤ Arank * N :=
  (Classical.choose_spec iota_rankin).2 a N ha

/-- SCS constant for `ι`. -/
noncomputable def Cscs : ℝ := Classical.choose iota_scs
lemma Cscs_nonneg : 0 ≤ Cscs := (Classical.choose_spec iota_scs).1
lemma Cscs_spec (a b ℓ N : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) :
    |∑ x ∈ Icc 1 N, iota a x * iota b (x + ℓ)| ≤
      Cscs * ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12 :=
  (Classical.choose_spec iota_scs).2 a b ℓ N ha hb hℓ

/-- The normalising size `S(h,k) = 4(A + C + 1)(hk)^{24}`. -/
noncomputable def Ssz (h k : ℕ) : ℝ := 4 * (Arank + Cscs + 1) * ((h * k : ℕ) : ℝ) ^ 24

lemma Ssz_pos {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) : 0 < Ssz h k := by
  unfold Ssz
  have := Arank_nonneg; have := Cscs_nonneg
  have : (1 : ℝ) ≤ ((h * k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  positivity

/-- `g_σ = r (ι_k + σ ι_h)`. -/
noncomputable def gS (h k : ℕ) (σ r : ℝ) (n : ℕ) : ℝ := r * (iota k n + σ * iota h n)

lemma pow12_le {h k a b : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (ha : a = h ∨ a = k) (hb : b = h ∨ b = k) :
    ((a * b : ℕ) : ℝ) ^ 12 ≤ ((h * k : ℕ) : ℝ) ^ 24 := by
  have hab : a * b ≤ (h * k) ^ 2 := by
    have h1 : a ≤ h * k := by
      rcases ha with rfl | rfl
      · exact Nat.le_mul_of_pos_right _ (by omega)
      · exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : b ≤ h * k := by
      rcases hb with rfl | rfl
      · exact Nat.le_mul_of_pos_right _ (by omega)
      · exact Nat.le_mul_of_pos_left _ (by omega)
    calc a * b ≤ (h * k) * (h * k) := Nat.mul_le_mul h1 h2
      _ = (h * k) ^ 2 := by ring
  have : ((a * b : ℕ) : ℝ) ≤ ((h * k : ℕ) : ℝ) ^ 2 := by exact_mod_cast hab
  calc ((a * b : ℕ) : ℝ) ^ 12 ≤ (((h * k : ℕ) : ℝ) ^ 2) ^ 12 := pow_le_pow_left₀ (by positivity) this 12
    _ = _ := by ring

/-- **The instance.** -/
noncomputable def goodSeq_gS {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {σ r : ℝ} (hσ : |σ| ≤ 1)
    (hr : r ^ 2 * Ssz h k ≤ 1) : GoodSeq (gS h k σ r) where
  c := Real.log ((h * k : ℕ) : ℝ)
  hc := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity))
  zero := by simp [gS, iota_zero]
  rankin := by
    intro N
    have hA := Arank_nonneg
    have e : ∀ n, gS h k σ r n ^ 2 ≤ r ^ 2 * (2 * iota k n ^ 2 + 2 * iota h n ^ 2) := by
      intro n
      unfold gS
      have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
      have : (iota k n + σ * iota h n) ^ 2 ≤ 2 * iota k n ^ 2 + 2 * iota h n ^ 2 := by
        nlinarith [sq_nonneg (iota k n - σ * iota h n), sq_nonneg (iota h n)]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left this (sq_nonneg r)
    calc ∑ n ∈ Icc 1 N, gS h k σ r n ^ 2 ≤ ∑ n ∈ Icc 1 N, r ^ 2 * (2 * iota k n ^ 2 + 2 * iota h n ^ 2) :=
          Finset.sum_le_sum fun n _ => e n
      _ = r ^ 2 * (2 * ∑ n ∈ Icc 1 N, iota k n ^ 2 + 2 * ∑ n ∈ Icc 1 N, iota h n ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ r ^ 2 * (2 * (Arank * N) + 2 * (Arank * N)) := by
          gcongr
          · exact Arank_spec k N hk
          · exact Arank_spec h N hh
      _ = (r ^ 2 * Ssz h k) * (Arank / (Arank + Cscs + 1) / ((h * k : ℕ) : ℝ) ^ 24 * N) := by
          unfold Ssz
          have := Cscs_nonneg
          have : (1 : ℝ) ≤ ((h * k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
          field_simp
          ring
      _ ≤ 1 * (1 * N) := by
          have := Cscs_nonneg
          have h1 : (1 : ℝ) ≤ ((h * k : ℕ) : ℝ) ^ 24 := by
            have : (1 : ℝ) ≤ ((h * k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
            exact one_le_pow₀ this
          have h2 : Arank / (Arank + Cscs + 1) / ((h * k : ℕ) : ℝ) ^ 24 ≤ 1 := by
            rw [div_div, div_le_one (by positivity)]
            nlinarith
          have h3 : 0 ≤ Arank / (Arank + Cscs + 1) / ((h * k : ℕ) : ℝ) ^ 24 := by positivity
          have h4 : 0 ≤ r ^ 2 * Ssz h k := by have := Ssz_pos hh hk; positivity
          gcongr
      _ = C1 * N := by rw [C1_eq]; ring
  scs := by
    intro ℓ N hℓ
    set P : ℕ → ℕ → ℝ := fun a b => ∑ x ∈ Icc 1 N, iota a x * iota b (x + ℓ) with hP
    have e : ∑ n ∈ Icc 1 N, gS h k σ r n * gS h k σ r (n + ℓ) =
        r ^ 2 * (P k k + σ * P k h + σ * P h k + σ ^ 2 * P h h) := by
      simp only [hP, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold gS; ring
    rw [e]
    set B : ℝ := ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) with hB
    have hB0 : 0 ≤ B := by positivity
    have hW : 0 ≤ ((h * k : ℕ) : ℝ) ^ 24 := by positivity
    have hb : ∀ a b, (a = h ∨ a = k) → (b = h ∨ b = k) → |P a b| ≤ Cscs * B * ((h * k : ℕ) : ℝ) ^ 24 := by
      intro a b ha hb'
      have h1 : 1 ≤ a := by rcases ha with rfl | rfl <;> assumption
      have h2 : 1 ≤ b := by rcases hb' with rfl | rfl <;> assumption
      refine (Cscs_spec a b ℓ N h1 h2 hℓ).trans ?_
      have := pow12_le hh hk ha hb'
      have := Cscs_nonneg
      calc Cscs * ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12
          = Cscs * B * ((a * b : ℕ) : ℝ) ^ 12 := by rw [hB]; ring
        _ ≤ _ := by gcongr
    have b1 := hb k k (Or.inr rfl) (Or.inr rfl)
    have b2 := hb k h (Or.inr rfl) (Or.inl rfl)
    have b3 := hb h k (Or.inl rfl) (Or.inr rfl)
    have b4 := hb h h (Or.inl rfl) (Or.inl rfl)
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
    set W := Cscs * B * ((h * k : ℕ) : ℝ) ^ 24 with hWdef
    have hsum : |P k k + σ * P k h + σ * P h k + σ ^ 2 * P h h| ≤ 4 * W := by
      have t2 : |σ * P k h| ≤ W := by
        rw [abs_mul]; calc |σ| * |P k h| ≤ 1 * W := mul_le_mul hσ b2 (abs_nonneg _) zero_le_one
          _ = W := one_mul _
      have t3 : |σ * P h k| ≤ W := by
        rw [abs_mul]; calc |σ| * |P h k| ≤ 1 * W := mul_le_mul hσ b3 (abs_nonneg _) zero_le_one
          _ = W := one_mul _
      have t4 : |σ ^ 2 * P h h| ≤ W := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg σ)]
        calc σ ^ 2 * |P h h| ≤ 1 * W := mul_le_mul hσ2 b4 (abs_nonneg _) zero_le_one
          _ = W := one_mul _
      calc |P k k + σ * P k h + σ * P h k + σ ^ 2 * P h h|
          ≤ |P k k| + |σ * P k h| + |σ * P h k| + |σ ^ 2 * P h h| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ 4 * W := by linarith
    rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
    have hS := Ssz_pos hh hk
    have hW4 : 4 * W ≤ Ssz h k * B := by
      rw [hWdef]; unfold Ssz
      have := Arank_nonneg; have := Cscs_nonneg
      have : 0 ≤ B * ((h * k : ℕ) : ℝ) ^ 24 := by positivity
      nlinarith
    calc r ^ 2 * |P k k + σ * P k h + σ * P h k + σ ^ 2 * P h h| ≤ r ^ 2 * (Ssz h k * B) := by
          gcongr; exact hsum.trans hW4
      _ = (r ^ 2 * Ssz h k) * B := by ring
      _ ≤ 1 * B := by gcongr
      _ = C1 * ((N : ℝ) + ℓ) ^ (1 - 1 / 21 : ℝ) * (ℓ : ℝ) ^ (1 / 21 : ℝ) := by rw [C1_eq, hB]; ring

end RamanujanTau.TwistedMoment
