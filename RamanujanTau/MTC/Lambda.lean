/-
# Theta divided by one linear factor

`Λ₀(v) = j(v; q) / (1 − v)` is entire: its coefficients are the partial theta sums
`Θlo n = Σ_{i ≤ n} (−1)^i q^{C(i,2)}` (`lam0S`). We record

* `lam0S_ent` — entire;
* `lam0S_rel` — `(1 − v) Λ₀(v) = j(v)` at every monomial point;
* `kap` — the special value `Λ₀(1)` (= `(q;q)_∞³`, identified later).
-/
import RamanujanTau.MTC.Lambert
import RamanujanTau.ALExt

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

section Lam0
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- coefficients of `j(v)/(1 − v)`: the partial theta sums. -/
noncomputable def lam0S : ℤ → L := fun n => Θlo hN n

lemma vge_Θlo (n : ℤ) : vge (Θlo hN n) (N * min (c2 n) (c2 (n + 1))) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hz : ∀ e : ℤ, mono e (0 : ℂ) = 0 := fun e => by simp [mono]
  by_cases hn : n < 0
  · rw [Θlo]
    refine vge_hs _ fun i => ?_
    simp only [thInd, monoFam_apply]
    by_cases hi : i ≤ n
    · rw [if_pos hi]
      refine vge_mono (vge_single _ _) ?_
      unfold thE
      have e1 := two_c2 i; have e2 := two_c2 n
      have : c2 n ≤ c2 i := by nlinarith
      have : min (c2 n) (c2 (n + 1)) ≤ c2 i := le_trans (min_le_left _ _) this
      nlinarith
    · rw [if_neg hi, hz]; exact vge_zero _
  · rw [Θlo_upper]
    refine vge_neg (vge_hs _ fun i => ?_)
    simp only [thInd, monoFam_apply]
    by_cases hi : i ≤ n
    · rw [if_neg (not_not.mpr hi), hz]; exact vge_zero _
    · rw [if_pos hi]
      refine vge_mono (vge_single _ _) ?_
      unfold thE
      have e1 := two_c2 i; have e2 := two_c2 (n + 1)
      have : c2 (n + 1) ≤ c2 i := by nlinarith
      have : min (c2 n) (c2 (n + 1)) ≤ c2 i := le_trans (min_le_right _ _) this
      nlinarith

lemma lam0S_ent : Ent (lam0S hN) := by
  intro A
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨C, hC⟩ := quad_dom hN' (|A| + N)
  refine ⟨C + N + |A|, fun n => vge_mono (vge_Θlo hN n) ?_⟩
  have h1 := hC n
  have h2 := hC (n + 1)
  have e1 := c2_succ n
  have hA : A * |n| ≤ |A| * |n| := mul_le_mul_of_nonneg_right (le_abs_self A) (abs_nonneg n)
  have hn1 : |n| ≤ |n + 1| + 1 := by
    have := abs_sub_abs_le_abs_sub n (n + 1); simp at this; linarith
  have h3 := mul_le_mul_of_nonneg_left hn1 (abs_nonneg A)
  have h4 : |A| * |n + 1| ≤ (|A| + N) * |n + 1| := by nlinarith [abs_nonneg (n + 1)]
  have h5 : |A| * |n| ≤ (|A| + N) * |n| := by nlinarith [abs_nonneg n]
  have h3' : |A| * |n| ≤ |A| * |n + 1| + |A| := by rw [mul_add, mul_one] at h3; exact h3
  rcases min_cases (c2 n) (c2 (n + 1)) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
    linarith [abs_nonneg A]

/-- `Θlo n − Θlo (n − 1) = (−1)^n q^{C(n,2)}`. -/
lemma Θlo_diff (n : ℤ) : Θlo hN n - Θlo hN (n - 1) = mono (N * c2 n) ((-1) ^ n) := by
  rw [Θlo, Θlo, hs, hs, ← SummableFamily.hsum_sub]
  rw [show (thInd hN (· ≤ n) - thInd hN (· ≤ n - 1)) = SummableFamily.single n (mono (N * c2 n) ((-1) ^ n)) by
    ext i : 1
    simp only [SummableFamily.sub_apply, thInd, monoFam_apply, thE]
    show _ = (Pi.single n (mono (N * c2 n) ((-1) ^ n)) : ℤ → L) i
    rw [Pi.single_apply]
    by_cases h : i = n
    · subst h; rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; simp [mono]
    · rw [if_neg h]
      by_cases h2 : i ≤ n - 1
      · rw [if_pos h2, if_pos (by omega)]; simp
      · rw [if_neg h2, if_neg (by omega)]; simp [mono]]
  rw [SummableFamily.hsum_single]

/-- `(1 − v) Λ₀(v) = j(v)` at every monomial point `v = c tᵉ`, `c ≠ 0`. -/
theorem lam0S_rel (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    (1 - mono e c) * ev (lam0S hN) e c = θ hN e c := by
  have hE := lam0S_ent hN
  have hshift := MTC.ev_shift hE (-1) e hc
  have hdiff : (fun n => lam0S hN n - shiftS (lam0S hN) (-1) n) = thS (NQ := N) 0 1 := by
    funext n
    simp only [lam0S, shiftS, thS]
    rw [show n + -1 = n - 1 by ring, Θlo_diff]
    congr 1 <;> simp
  have hv := ev_sub hE (hE.shift (-1)) e c
  rw [show (lam0S hN - shiftS (lam0S hN) (-1)) = fun n => lam0S hN n - shiftS (lam0S hN) (-1) n from rfl,
    hdiff, thS_ev hN 0 one_ne_zero, sub_zero, div_one, hshift] at hv
  rw [hv]; simp only [neg_mul, neg_neg, mul_neg, zpow_one]; ring

/-- the special value `Λ₀(1)`. -/
noncomputable def kap : L := ev (lam0S hN) 0 1

end Lam0

end MTC
