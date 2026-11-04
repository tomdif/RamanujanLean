/-
# The Dedekind-sum congruence behind Andrews' sign and shift

For `h` coprime to `2k` (so `h` is odd):

  `2s(h,k) − 4s(h,2k) ≡ ⌊(k+1)/2⌋ − k + h(1+(−1)^k)/4  (mod 2)`          (`T_cong`)

stated as `2T − G ∈ 4ℤ` with `T = 2s(h,k) − 4s(h,2k)` (`Tq`) and the integer `G = (k mod 2) − k + [k even]·h`
(`Gq`, `= 2·RHS`).

Proof: strong induction on `k` (a Euclidean algorithm), using only Dedekind reciprocity
(`Rademacher.dsum_reciprocity`), periodicity (`dsum_mod`) and `s(−h,k) = −s(h,k)` (`dsum_neg`):
* `T(h,k) + U(k,h) = 1/2 − k/(2h)`, `U(k,h) = 2s(k,h) − 4s(2k,h)` (`TU`, two reciprocities);
* hence `T(h,k) = T(h, k mod h) − ⌊k/h⌋/2` (`T_step`);
* `T` depends on `h mod 2k`, and `T(2k−h,k) = −T(h,k)`;
* base `T(1,k) = (1−k)/2`; `G` obeys the same recursion mod 4 (`G_step`, a parity computation).
-/
import RamanujanTau.Andrews66.OmegaB

set_option autoImplicit false

namespace Andrews66
open Rademacher

noncomputable section

/-- `T(h,k) = 2s(h,k) − 4s(h,2k)`. -/
def Tq (h k : ℕ) : ℝ := 2 * dsum h k - 4 * dsum h (2 * k)
/-- `U(k,h) = 2s(k,h) − 4s(2k,h)`. -/
def Uq (k h : ℕ) : ℝ := 2 * dsum k h - 4 * dsum (2 * k) h
/-- `G(h,k) = (k mod 2) − k + [k even]·h`. -/
def Gq (h k : ℕ) : ℤ := ((k % 2 : ℕ) : ℤ) - k + (if k % 2 = 0 then (h : ℤ) else 0)

lemma TU {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h (2 * k)) :
    Tq h k + Uq k h = 1 / 2 - k / (2 * h) := by
  have r1 := dsum_reciprocity hh hk (coprime_half hc)
  have r2 := dsum_reciprocity hh (by omega : 0 < 2 * k) hc
  push_cast at r2
  unfold Tq Uq
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  linear_combination 2 * r1 - 4 * r2

lemma U_mod {k h : ℕ} (hh : 0 < h) : Uq k h = Uq (k % h) h := by
  unfold Uq
  have e : (2 * k) % h = (2 * (k % h)) % h := by rw [Nat.mul_mod, Nat.mul_mod 2 (k % h), Nat.mod_mod]
  rw [dsum_mod hh (h := k), dsum_mod hh (h := 2 * k), dsum_mod hh (h := 2 * (k % h)), e]

lemma T_mod {h k : ℕ} (hk : 0 < k) : Tq h k = Tq (h % (2 * k)) k := by
  unfold Tq
  rw [dsum_mod hk (h := h), dsum_mod hk (h := h % (2 * k)), Nat.mod_mod_of_dvd h (Dvd.intro_left 2 rfl),
    dsum_mod (by omega : 0 < 2 * k) (h := h)]

lemma T_flip {h k : ℕ} (hk : 0 < k) (hc : Nat.Coprime h (2 * k)) (hle : h ≤ 2 * k) :
    Tq (2 * k - h) k = -Tq h k := by
  unfold Tq
  rw [dsum_neg hk (coprime_half hc) (k := h) (by rw [Nat.sub_add_cancel hle]; exact Dvd.intro_left 2 rfl),
    dsum_neg (by omega) hc (k := h) (by rw [Nat.sub_add_cancel hle])]
  ring

lemma T_one {k : ℕ} (hk : 0 < k) : Tq 1 k = (1 - k) / 2 := by
  have r1 := dsum_reciprocity one_pos hk (Nat.coprime_one_left k)
  have r2 := dsum_reciprocity one_pos (by omega : 0 < 2 * k) (Nat.coprime_one_left (2 * k))
  have z1 : dsum k 1 = 0 := by simp [dsum, saw]
  have z2 : dsum (2 * k) 1 = 0 := by simp [dsum, saw]
  rw [z1] at r1; rw [z2] at r2
  push_cast at r1 r2
  unfold Tq
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  linear_combination 2 * r1 - 4 * r2

lemma T_step {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h (2 * k)) (ha : 0 < k % h) :
    Tq h k = Tq h (k % h) - (k / h : ℕ) / 2 := by
  have hc' : Nat.Coprime h (2 * (k % h)) := by
    have h2 : Nat.Coprime h 2 := Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hc
    have hk' : Nat.Coprime h (k % h) := by
      unfold Nat.Coprime; rw [Nat.gcd_comm, ← Nat.gcd_rec]; exact coprime_half hc
    exact Nat.Coprime.mul_right h2 hk'
  have e1 := TU hh hk hc
  have e2 := TU hh ha hc'
  rw [U_mod hh] at e1
  have hdiv : ((k : ℕ) : ℝ) = h * (k / h : ℕ) + (k % h : ℕ) := by exact_mod_cast (Nat.div_add_mod k h).symm
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [hdiv] at e1
  field_simp at e1 e2
  have key : (h : ℝ) * (2 * Tq h k - 2 * Tq h (k % h) + ((k / h : ℕ) : ℝ)) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hh0
  · linarith

lemma G_step {h q a : ℕ} (hh : h % 2 = 1) : ∃ j : ℤ, Gq h (q * h + a) - Gq h a + q = 4 * j := by
  obtain ⟨t, rfl⟩ : ∃ t, h = 2 * t + 1 := ⟨h / 2, by omega⟩
  unfold Gq
  rcases Nat.even_or_odd q with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;> rcases Nat.even_or_odd a with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · have e : (u + u) * (2 * t + 1) + (v + v) = 2 * (u * (2 * t + 1) + v) := by ring
    rw [e]; simp only [Nat.mul_mod_right, ↓reduceIte, show (v + v) % 2 = 0 by omega]
    exact ⟨-(u * t), by push_cast; ring⟩
  · have e : (u + u) * (2 * t + 1) + (2 * v + 1) = 2 * (u * (2 * t + 1) + v) + 1 := by ring
    rw [e]; simp only [show (2 * (u * (2 * t + 1) + v) + 1) % 2 = 1 by omega, show (2 * v + 1) % 2 = 1 by omega,
      one_ne_zero, ↓reduceIte]
    exact ⟨-(u * t), by push_cast; ring⟩
  · have e : (2 * u + 1) * (2 * t + 1) + (v + v) = 2 * (2 * u * t + u + t + v) + 1 := by ring
    rw [e]; simp only [show (2 * (2 * u * t + u + t + v) + 1) % 2 = 1 by omega, show (v + v) % 2 = 0 by omega,
      one_ne_zero, ↓reduceIte]
    exact ⟨-(t * (u + 1)), by push_cast; ring⟩
  · have e : (2 * u + 1) * (2 * t + 1) + (2 * v + 1) = 2 * (2 * u * t + u + t + v + 1) := by ring
    rw [e]; simp only [show (2 * (2 * u * t + u + t + v + 1)) % 2 = 0 by omega, show (2 * v + 1) % 2 = 1 by omega,
      one_ne_zero, ↓reduceIte]
    exact ⟨-(u * t), by push_cast; ring⟩

lemma odd_of_coprime {h k : ℕ} (hc : Nat.Coprime h (2 * k)) : h % 2 = 1 := by
  have h2 : Nat.Coprime h 2 := Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hc
  rcases Nat.mod_two_eq_zero_or_one h with h0 | h1
  · exfalso
    have : 2 ∣ Nat.gcd h 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
    rw [h2] at this; norm_num at this
  · exact h1

/-- the core case `h ≤ k`. -/
lemma T_cong_le (k : ℕ) (IH : ∀ a < k, 0 < a → ∀ h : ℕ, Nat.Coprime h (2 * a) →
      ∃ m : ℤ, 2 * Tq h a - Gq h a = 4 * m)
    (hk : 0 < k) {h : ℕ} (hc : Nat.Coprime h (2 * k)) (hle : h ≤ k) : ∃ m : ℤ, 2 * Tq h k - Gq h k = 4 * m := by
  have hodd := odd_of_coprime hc
  by_cases h1 : h = 1
  · subst h1
    refine ⟨0, ?_⟩
    rw [T_one hk]
    unfold Gq
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h0 <;> simp [h0] <;> ring
  have hh : 0 < h := by omega
  have ha : 0 < k % h := by
    rcases Nat.eq_zero_or_pos (k % h) with h0 | h0
    · exfalso
      have hd : h ∣ k := Nat.dvd_of_mod_eq_zero h0
      exact h1 (Nat.Coprime.eq_one_of_dvd (coprime_half hc) hd)
    · exact h0
  have hc' : Nat.Coprime h (2 * (k % h)) := by
    have h2 : Nat.Coprime h 2 := Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hc
    have hk' : Nat.Coprime h (k % h) := by
      unfold Nat.Coprime; rw [Nat.gcd_comm, ← Nat.gcd_rec]; exact coprime_half hc
    exact Nat.Coprime.mul_right h2 hk'
  have hlt : k % h < k := lt_of_lt_of_le (Nat.mod_lt k hh) hle
  obtain ⟨m, hm⟩ := IH (k % h) hlt ha h hc'
  obtain ⟨j, hj⟩ := G_step (q := k / h) (a := k % h) hodd
  rw [show k / h * h + k % h = k by rw [mul_comm]; exact Nat.div_add_mod k h] at hj
  refine ⟨m - j, ?_⟩
  rw [T_step hh hk hc ha]
  have hj' : (Gq h k : ℝ) - Gq h (k % h) + ((k / h : ℕ) : ℝ) = 4 * j := by
    have := congrArg (Int.cast : ℤ → ℝ) hj
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at this
    exact this
  push_cast
  linarith

/-- **the Dedekind-sum congruence**: `2T(h,k) − G(h,k) ∈ 4ℤ` for `h` coprime to `2k`. -/
theorem T_cong : ∀ k : ℕ, 0 < k → ∀ h : ℕ, Nat.Coprime h (2 * k) → ∃ m : ℤ, 2 * Tq h k - Gq h k = 4 * m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk h hc
  have IH : ∀ a < k, 0 < a → ∀ h : ℕ, Nat.Coprime h (2 * k) → True := fun _ _ _ _ _ => trivial
  clear IH
  set h₀ := h % (2 * k) with hh₀
  have hc₀ : Nat.Coprime h₀ (2 * k) := coprime_mod hc
  have hlt₀ : h₀ < 2 * k := Nat.mod_lt _ (by omega)
  -- `G(h) ≡ G(h₀)`
  have hG : ∃ j : ℤ, Gq h k - Gq h₀ k = 4 * j := by
    unfold Gq
    have hd : (h : ℤ) = h₀ + 2 * k * (h / (2 * k) : ℕ) := by
      have := Nat.mod_add_div h (2 * k); rw [← hh₀] at this; exact_mod_cast this.symm
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
    · obtain ⟨l, hl⟩ : ∃ l, k = 2 * l := ⟨k / 2, by omega⟩
      refine ⟨l * (h / (2 * k) : ℕ), ?_⟩
      simp only [h0, ↓reduceIte]; rw [hd]; push_cast; rw [hl]; push_cast; ring
    · exact ⟨0, by simp [h0]⟩
  obtain ⟨j, hj⟩ := hG
  have hT : Tq h k = Tq h₀ k := T_mod hk
  suffices H : ∃ m : ℤ, 2 * Tq h₀ k - Gq h₀ k = 4 * m by
    obtain ⟨m, hm⟩ := H
    refine ⟨m - j, ?_⟩
    have hj' : (Gq h k : ℝ) - Gq h₀ k = 4 * j := by
      have := congrArg (fun x : ℤ => (x : ℝ)) hj; push_cast at this; linarith
    rw [hT]; push_cast; linarith
  have IH : ∀ a < k, 0 < a → ∀ h : ℕ, Nat.Coprime h (2 * a) → ∃ m : ℤ, 2 * Tq h a - Gq h a = 4 * m :=
    fun a ha ha0 h hc => ih a ha ha0 h hc
  by_cases hle : h₀ ≤ k
  · exact T_cong_le k IH hk hc₀ hle
  · -- flip `h₀ ↦ 2k − h₀`
    have hc₁ : Nat.Coprime (2 * k - h₀) (2 * k) := by
      have := coprime_of_dvd_add (H := 2 * k - h₀) hc₀ (by rw [Nat.sub_add_cancel hlt₀.le])
      exact this
    obtain ⟨m, hm⟩ := T_cong_le k IH hk hc₁ (by omega)
    rw [T_flip hk hc₀ hlt₀.le] at hm
    -- `G(2k − h₀) + G(h₀) ∈ 4ℤ`
    have hsum : ∃ i : ℤ, Gq (2 * k - h₀) k + Gq h₀ k = 4 * i := by
      unfold Gq
      have hs : ((2 * k - h₀ : ℕ) : ℤ) = 2 * k - h₀ := by push_cast [Nat.cast_sub hlt₀.le]; ring
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
      · obtain ⟨l, hl⟩ : ∃ l, k = 2 * l := ⟨k / 2, by omega⟩
        refine ⟨0, ?_⟩
        simp only [h0, ↓reduceIte, hs]; ring
      · obtain ⟨l, hl⟩ : ∃ l, k = 2 * l + 1 := ⟨k / 2, by omega⟩
        refine ⟨-l, ?_⟩
        simp only [h0, one_ne_zero, ↓reduceIte]; rw [hl]; push_cast; ring
    obtain ⟨i, hi⟩ := hsum
    refine ⟨-i - m, ?_⟩
    have hi' : (Gq (2 * k - h₀) k : ℝ) + Gq h₀ k = 4 * i := by
      have := congrArg (fun x : ℤ => (x : ℝ)) hi; push_cast at this; linarith
    push_cast
    linarith

end

end Andrews66
