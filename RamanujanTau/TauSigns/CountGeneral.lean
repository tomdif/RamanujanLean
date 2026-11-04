/-
# Counting sign changes of τ from any short-interval result / any RS power saving

* `card_signChanges_ge_of_window`: if every `(x, x+h]` with `x ≥ X₀`, `A x^θ ≤ h ≤ x` contains
  both signs (`0 ≤ θ < 1`), then `#signChanges X ≥ c·X^{1−θ}` for large `X`.
* `card_signChanges_ge_of_power_saving`: from `|S(N) − cN| ≤ C N^{1−δ}` and `3/4 < θ < 1`,
  `1 − δ ≤ θ`, get `≫ X^{1−θ}` sign changes.

Same proof as `Count.lean` with `83/84 ↦ θ`, `1/84 ↦ η := 1 − θ`, `(16A)^84 ↦ (16A)^{1/η}`.
-/
import RamanujanTau.TauSigns.Count
import RamanujanTau.TauSigns.WindowGeneral

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Finset Filter
open scoped Real

/-- **`≫ X^{1−θ}` sign changes of τ in `[1, X]`, from windows of length `x^θ`.** -/
theorem card_signChanges_ge_of_window {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hW : ∃ A X₀ : ℝ, 0 < A ∧ ∀ x h : ℕ, X₀ ≤ x → A * (x : ℝ) ^ θ ≤ h → h ≤ x →
      (∃ m ∈ Ioc x (x + h), 0 < tau m) ∧ (∃ n ∈ Ioc x (x + h), tau n < 0)) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ^ (1 - θ) ≤ (signChanges X).card := by
  set η : ℝ := 1 - θ with hηdef
  have hη : 0 < η := by simp only [η]; linarith
  obtain ⟨A₀, Xw, hA₀, hwin⟩ := hW
  set A := max A₀ 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := by linarith
  refine ⟨1 / (16 * A), by positivity, max (max 8 (4 * Xw)) ((16 * A) ^ (1 / η)), ?_⟩
  intro X hX
  have hX8 : (8 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXw : 4 * Xw ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXA : (16 * A) ^ (1 / η) ≤ (X : ℝ) := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  set u : ℝ := (X : ℝ) ^ η
  have hu : 16 * A ≤ u := by
    have h := Real.rpow_le_rpow (by positivity) hXA hη.le
    have e : ((16 * A) ^ (1 / η) : ℝ) ^ η = 16 * A := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one]
    rw [e] at h; exact h
  have hupos : 0 < u := by linarith
  have hXa : (X : ℝ) ^ θ = X / u := by
    rw [eq_div_iff hupos.ne', ← Real.rpow_add hXpos]; simp only [η]; norm_num
  set H : ℕ := ⌈A * (X : ℝ) ^ θ⌉₊
  set Y : ℕ := X / 2
  set J : ℕ := Y / H
  have hXu1 : 1 ≤ (X : ℝ) / u := by
    rw [← hXa]; exact Real.one_le_rpow (by linarith) hθ0
  have hH1 : A * (X : ℝ) ^ θ ≤ H := Nat.le_ceil _
  have hH2 : (H : ℝ) < A * (X / u) + 1 := by rw [← hXa]; exact Nat.ceil_lt_add_one (by positivity)
  have hHpos : 0 < H := by
    have : (0 : ℝ) < H := lt_of_lt_of_le (by rw [hXa]; nlinarith) hH1
    exact_mod_cast this
  have hY : (X : ℝ) / 4 ≤ Y := by
    have h1 : X ≤ 2 * Y + 1 := by omega
    have h2 : (X : ℝ) ≤ 2 * Y + 1 := by exact_mod_cast h1
    linarith
  have hY2 : (2 * Y : ℝ) ≤ X := by
    have : 2 * Y ≤ X := by omega
    exact_mod_cast this
  have hAXu : A * (X / u) ≤ X / 16 := by
    rw [mul_div_assoc', div_le_div_iff₀ hupos (by norm_num)]
    nlinarith
  have hHY : H ≤ Y := by
    have : (H : ℝ) ≤ Y := by linarith
    exact_mod_cast this
  -- windows
  have hwj : ∀ j, j < J → ∃ n, n ∈ signChanges X ∧ Y + j * H < n ∧ n < Y + (j + 1) * H := by
    intro j hj
    set xj := Y + j * H
    have hJH : J * H ≤ Y := Nat.div_mul_le_self Y H
    have hxj1 : xj + H ≤ X := by
      have : (j + 1) * H ≤ J * H := Nat.mul_le_mul_right H hj
      have : 2 * Y ≤ X := by omega
      have e : (j + 1) * H = j * H + H := by ring
      show Y + j * H + H ≤ X
      linarith
    have hxjY : Y ≤ xj := Nat.le_add_right _ _
    have hxjX : xj ≤ X := by omega
    have h1 : Xw ≤ (xj : ℝ) := by
      have : (Y : ℝ) ≤ xj := by exact_mod_cast hxjY
      linarith
    have h2 : A₀ * (xj : ℝ) ^ θ ≤ H := by
      refine le_trans ?_ hH1
      apply mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hxjX) hθ0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (by positivity)
    have h3 : H ≤ xj := le_trans hHY hxjY
    obtain ⟨hpos, hneg⟩ := hwin xj H h1 h2 h3
    obtain ⟨n, m, hn1, hm1, hsc⟩ := exists_signChange_window hpos hneg
    refine ⟨n, ?_, hn1, ?_⟩
    · simp only [signChanges, mem_filter, mem_range]
      exact ⟨by have := hsc.1; omega, m, by omega, hsc⟩
    · have := hsc.1
      have : (j + 1) * H = j * H + H := by ring
      have hxe : xj = Y + j * H := rfl
      show n < Y + (j + 1) * H
      linarith
  choose! f hf using hwj
  have hcard : J ≤ (signChanges X).card := by
    have := card_le_card_of_injOn f (s := range J) (t := signChanges X)
      (fun j hj => (hf j (mem_range.mp hj)).1) (by
        intro a ha b hb hab
        have ha' := hf a (mem_range.mp ha)
        have hb' := hf b (mem_range.mp hb)
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : (a + 1) * H ≤ b * H := Nat.mul_le_mul_right H h
          have := ha'.2.2; have := hb'.2.1
          have e : (a + 1) * H = a * H + H := by ring
          rw [hab] at *; linarith
        · have : (b + 1) * H ≤ a * H := Nat.mul_le_mul_right H h
          have := hb'.2.2; have := ha'.2.1
          have e : (b + 1) * H = b * H + H := by ring
          rw [hab] at *; linarith)
    simpa using this
  -- J ≥ u/(16A)
  have hJ : u / (16 * A) ≤ J := by
    have hlt : Y < J * H + H := Nat.lt_div_mul_add hHpos
    have hlt' : (Y : ℝ) < (J + 1) * H := by
      have : (Y : ℝ) < ((J * H + H : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at this; linarith
    have hH3 : (H : ℝ) ≤ 2 * A * (X / u) := by nlinarith
    have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
    have hk : (X : ℝ) / 4 < (J + 1) * (2 * A * (X / u)) := by
      calc (X : ℝ) / 4 ≤ Y := hY
        _ < (J + 1) * H := hlt'
        _ ≤ (J + 1) * (2 * A * (X / u)) := by
            apply mul_le_mul_of_nonneg_left hH3; positivity
    have hk2 : u / (8 * A) < J + 1 := by
      rw [div_lt_iff₀ (by positivity)]
      have e : (J + 1) * (2 * A * (X / u)) = ((J + 1) * (8 * A)) * (X / u) / 4 := by ring
      rw [e] at hk
      have hXu : (X : ℝ) / 4 = (u * (X / u)) / 4 := by field_simp
      rw [hXu] at hk
      have := (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mp hk
      have hXu0 : 0 < (X : ℝ) / u := by positivity
      nlinarith
    have : (1 : ℝ) ≤ u / (16 * A) := by rw [le_div_iff₀ (by positivity)]; linarith
    have e : u / (8 * A) = 2 * (u / (16 * A)) := by field_simp; ring
    linarith
  calc 1 / (16 * A) * (X : ℝ) ^ η = u / (16 * A) := by ring
    _ ≤ J := hJ
    _ ≤ (signChanges X).card := by exact_mod_cast hcard

/-- **`≫ X^{1−θ}` sign changes from any RS power saving `δ`** (`3/4 < θ < 1`, `1 − δ ≤ θ`). -/
theorem card_signChanges_ge_of_power_saving {δ θ : ℝ} (hθ : 3 / 4 < θ) (hθ1 : θ < 1)
    (hδθ : 1 - δ ≤ θ)
    (hRS : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ^ (1 - θ) ≤ (signChanges X).card :=
  card_signChanges_ge_of_window (by linarith) hθ1
    (tau_sign_change_short_interval_of_power_saving hθ hθ1.le hδθ hRS)

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.card_signChanges_ge_of_window
#print axioms RamanujanTau.TauSigns.card_signChanges_ge_of_power_saving
