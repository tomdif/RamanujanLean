/-
# Counting sign changes of τ: `≫ x^{1/84}` of them in `[1, x]`

A *sign change* is a pair `n < m` with `τ(n)τ(m) < 0` and `τ(k) = 0` for `n < k < m`
(the next nonzero value after `n` has the opposite sign).
`signChanges X` is the set of `n ≤ X` starting a sign change completed by some `m ≤ X`.

`card_signChanges_ge : ∃ c > 0, ∃ X₀, ∀ X ≥ X₀, c·X^{1/84} ≤ #signChanges X`.

Proof: cut `(X/2, X]` into `≍ X^{1/84}` disjoint windows of length `≍ X^{83/84}`; each contains
both signs (`tau_sign_change_short_interval`), hence a sign change (`exists_signChange_between`).
-/
import RamanujanTau.TauSigns.Window

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Finset Filter
open scoped Real

/-- `(n, m)` is a sign change of `τ`. -/
def IsSignChange (n m : ℕ) : Prop :=
  n < m ∧ tau n * tau m < 0 ∧ ∀ k, n < k → k < m → tau k = 0

open Classical in
/-- Starting points `n ≤ X` of sign changes `(n, m)` with `m ≤ X`. -/
noncomputable def signChanges (X : ℕ) : Finset ℕ :=
  (range (X + 1)).filter fun n => ∃ m, m ≤ X ∧ IsSignChange n m

/-- Between two values of opposite sign there is a sign change. -/
theorem exists_signChange_between : ∀ (d a b : ℕ), b - a = d → a < b → tau a * tau b < 0 →
    ∃ n m, a ≤ n ∧ m ≤ b ∧ IsSignChange n m := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b hd hab hneg
  have hex : ∃ k, a < k ∧ tau k ≠ 0 := ⟨b, hab, fun h => by simp [h] at hneg⟩
  classical
  set m := Nat.find hex
  have hm : a < m ∧ tau m ≠ 0 := Nat.find_spec hex
  have hmin : ∀ k, a < k → k < m → tau k = 0 := by
    intro k hk hkm
    by_contra hne
    exact Nat.find_min hex hkm ⟨hk, hne⟩
  have hmb : m ≤ b := Nat.find_min' hex ⟨hab, fun h => by simp [h] at hneg⟩
  have ha0 : tau a ≠ 0 := fun h => by simp [h] at hneg
  rcases lt_or_gt_of_ne (mul_ne_zero ha0 hm.2) with hlt | hgt
  · exact ⟨a, m, le_refl a, hmb, hm.1, hlt, hmin⟩
  · -- τ(a)τ(m) > 0, so τ(m)τ(b) < 0 and m < b
    have hmb' : m < b := by
      rcases lt_or_eq_of_le hmb with h | h
      · exact h
      · rw [h] at hgt; linarith
    have hmb2 : tau m * tau b < 0 := by
      rcases lt_or_gt_of_ne ha0 with ha | ha
      · have : tau m < 0 := by
          by_contra h; push Not at h
          have := mul_nonpos_of_nonpos_of_nonneg ha.le h; linarith
        have : 0 < tau b := by
          by_contra h; push Not at h
          have := mul_nonneg_of_nonpos_of_nonpos ha.le h; linarith
        nlinarith
      · have : 0 < tau m := by
          by_contra h; push Not at h
          have := mul_nonpos_of_nonneg_of_nonpos ha.le h; linarith
        have : tau b < 0 := by
          by_contra h; push Not at h
          have := mul_nonneg ha.le h; linarith
        nlinarith
    obtain ⟨n, m', h1, h2, h3⟩ := ih (b - m) (by omega) m b rfl hmb' hmb2
    exact ⟨n, m', by omega, h2, h3⟩

/-- A window containing both signs contains a sign change. -/
lemma exists_signChange_window {x H : ℕ} (hp : ∃ m ∈ Ioc x (x + H), 0 < tau m)
    (hn : ∃ n ∈ Ioc x (x + H), tau n < 0) :
    ∃ n m, x < n ∧ m ≤ x + H ∧ IsSignChange n m := by
  obtain ⟨p, hp1, hp2⟩ := hp
  obtain ⟨q, hq1, hq2⟩ := hn
  obtain ⟨hp1a, hp1b⟩ := mem_Ioc.mp hp1
  obtain ⟨hq1a, hq1b⟩ := mem_Ioc.mp hq1
  have hpq : tau p * tau q < 0 := mul_neg_of_pos_of_neg hp2 hq2
  rcases lt_trichotomy p q with h | h | h
  · obtain ⟨n, m, h1, h2, h3⟩ := exists_signChange_between (q - p) p q rfl h hpq
    exact ⟨n, m, by omega, by omega, h3⟩
  · subst h; linarith
  · obtain ⟨n, m, h1, h2, h3⟩ := exists_signChange_between (p - q) q p rfl h (by linarith [mul_comm (tau p) (tau q)])
    exact ⟨n, m, by omega, by omega, h3⟩

/-- **`≫ X^{1/84}` sign changes of τ in `[1, X]`.** -/
theorem card_signChanges_ge : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
    c * (X : ℝ) ^ (1 / 84 : ℝ) ≤ (signChanges X).card := by
  obtain ⟨A₀, Xw, hA₀, hwin⟩ := tau_sign_change_short_interval
  set A := max A₀ 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := by linarith
  refine ⟨1 / (16 * A), by positivity, max (max 8 (4 * Xw)) ((16 * A) ^ 84), ?_⟩
  intro X hX
  have hX8 : (8 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXw : 4 * Xw ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXA : (16 * A) ^ 84 ≤ (X : ℝ) := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  set u : ℝ := (X : ℝ) ^ (1 / 84 : ℝ)
  have hu : 16 * A ≤ u := by
    have h := Real.rpow_le_rpow (by positivity) hXA (show (0 : ℝ) ≤ 1 / 84 by norm_num)
    have e : ((16 * A) ^ 84 : ℝ) ^ (1 / 84 : ℝ) = 16 * A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [e] at h; exact h
  have hupos : 0 < u := by linarith
  have hXa : (X : ℝ) ^ (83 / 84 : ℝ) = X / u := by
    rw [eq_div_iff hupos.ne', ← Real.rpow_add hXpos]; norm_num
  set H : ℕ := ⌈A * (X : ℝ) ^ (83 / 84 : ℝ)⌉₊
  set Y : ℕ := X / 2
  set J : ℕ := Y / H
  have hXu1 : 1 ≤ (X : ℝ) / u := by
    rw [← hXa]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hH1 : A * (X : ℝ) ^ (83 / 84 : ℝ) ≤ H := Nat.le_ceil _
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
    have h2 : A₀ * (xj : ℝ) ^ (83 / 84 : ℝ) ≤ H := by
      refine le_trans ?_ hH1
      apply mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hxjX) (by norm_num)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
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
  calc 1 / (16 * A) * (X : ℝ) ^ (1 / 84 : ℝ) = u / (16 * A) := by ring
    _ ≤ J := hJ
    _ ≤ (signChanges X).card := by exact_mod_cast hcard

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.exists_signChange_between
#print axioms RamanujanTau.TauSigns.card_signChanges_ge
