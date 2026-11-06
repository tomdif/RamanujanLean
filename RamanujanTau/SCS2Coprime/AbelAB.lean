/-
# Item 4 (part 3): the weight `(nm)^{−11/2}`, `m = (bn+ℓ)/a`, and the two-sided sum as an Abel sum

* `wAB t = t^{−11/2} ((bt+ℓ)/a)^{−11/2}`, its derivative and `|wAB'(t)| ≤ 11 t^{−13/2} m(t)^{−11/2}`;
* **`shiftSum2_eq`**: for `ℓ ≥ 1`, `S(a,b;ℓ,N) = Σ_{n ≤ N₁} wAB(n) cR(n)` with
  `N₁ = min(N, ⌊(aN − ℓ)/b⌋)`.
-/
import RamanujanTau.SCS2Coprime.RankinAB
import RamanujanTau.HeckeAFE.Hyp

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.HeckeAFE
open scoped Real

variable (a b : ℕ+) (ℓ : ℕ)

/-- `m(t) = (bt + ℓ)/a`. -/
noncomputable def mfun (t : ℝ) : ℝ := ((b : ℝ) * t + ℓ) / a

lemma mfun_pos {t : ℝ} (ht : 0 < t) : 0 < mfun a b ℓ t := by
  unfold mfun; have : (0 : ℝ) < b := by exact_mod_cast b.pos
  positivity

/-- The weight. -/
noncomputable def wAB (t : ℝ) : ℝ := t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ))

/-- Its derivative. -/
noncomputable def wAB' (t : ℝ) : ℝ :=
  (-(11 / 2 : ℝ)) * t ^ (-(11 / 2 : ℝ) - 1) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) +
    t ^ (-(11 / 2 : ℝ)) * ((-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ) - 1) * ((b : ℝ) / a))

lemma hasDerivAt_mfun (t : ℝ) : HasDerivAt (mfun a b ℓ) ((b : ℝ) / a) t := by
  have := (((hasDerivAt_id t).const_mul (b : ℝ)).add_const (ℓ : ℝ)).div_const (a : ℝ)
  simpa [mfun] using this

lemma hasDerivAt_wAB {t : ℝ} (ht : 0 < t) : HasDerivAt (wAB a b ℓ) (wAB' a b ℓ t) t := by
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := -(11 / 2 : ℝ)) (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => mfun a b ℓ t ^ (-(11 / 2 : ℝ)))
      ((-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ) - 1) * ((b : ℝ) / a)) t := by
    have := (Real.hasDerivAt_rpow_const (x := mfun a b ℓ t) (p := -(11 / 2 : ℝ))
      (Or.inl (mfun_pos a b ℓ ht).ne')).comp t (hasDerivAt_mfun a b ℓ t)
    simpa [mul_assoc] using this
  exact h1.mul h2

lemma deriv_wAB {t : ℝ} (ht : 0 < t) : deriv (wAB a b ℓ) t = wAB' a b ℓ t :=
  (hasDerivAt_wAB a b ℓ ht).deriv

lemma continuous_mfun : Continuous (mfun a b ℓ) := by
  unfold mfun; fun_prop

lemma continuousOn_wAB' : ContinuousOn (wAB' a b ℓ) (Set.Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hm := mfun_pos a b ℓ ht0
  unfold wAB'
  refine ContinuousAt.continuousWithinAt ?_
  have c1 : ContinuousAt (fun t : ℝ => t ^ (-(11 / 2 : ℝ) - 1)) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c2 : ContinuousAt (fun t : ℝ => t ^ (-(11 / 2 : ℝ))) t :=
    Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  have c3 : ContinuousAt (fun t : ℝ => mfun a b ℓ t ^ (-(11 / 2 : ℝ))) t :=
    (Real.continuousAt_rpow_const _ _ (Or.inl hm.ne')).comp (f := mfun a b ℓ)
      (continuous_mfun a b ℓ).continuousAt
  have c4 : ContinuousAt (fun t : ℝ => mfun a b ℓ t ^ (-(11 / 2 : ℝ) - 1)) t :=
    (Real.continuousAt_rpow_const _ _ (Or.inl hm.ne')).comp (f := mfun a b ℓ)
      (continuous_mfun a b ℓ).continuousAt
  exact ((continuousAt_const.mul c1).mul c3).add
    (c2.mul ((continuousAt_const.mul c4).mul continuousAt_const))

/-- `|wAB'(t)| ≤ 11 t^{−13/2} m(t)^{−11/2}`. -/
lemma abs_wAB'_le {t : ℝ} (ht : 0 < t) :
    |wAB' a b ℓ t| ≤ 11 * t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) := by
  have hm := mfun_pos a b ℓ ht
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  have hb : (0 : ℝ) < b := by exact_mod_cast b.pos
  have hba : (b : ℝ) / a * t ≤ mfun a b ℓ t := by
    unfold mfun
    rw [div_mul_eq_mul_div]
    gcongr
    have := Nat.cast_nonneg (α := ℝ) ℓ; linarith
  unfold wAB'
  have e1 : (-(11 / 2 : ℝ)) - 1 = -(13 / 2 : ℝ) := by norm_num
  rw [e1]
  have p1 : 0 < t ^ (-(13 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have p2 : 0 < mfun a b ℓ t ^ (-(11 / 2 : ℝ)) := Real.rpow_pos_of_pos hm _
  have p3 : 0 < t ^ (-(11 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have p4 : 0 < mfun a b ℓ t ^ (-(13 / 2 : ℝ)) := Real.rpow_pos_of_pos hm _
  have hba0 : 0 < (b : ℝ) / a := by positivity
  have key : t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * ((b : ℝ) / a) ≤
      t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) := by
    have a1 : t ^ (-(11 / 2 : ℝ)) = t ^ (-(13 / 2 : ℝ)) * t := by
      rw [← Real.rpow_add_one ht.ne']; norm_num
    have a2 : mfun a b ℓ t ^ (-(11 / 2 : ℝ)) = mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t := by
      rw [← Real.rpow_add_one hm.ne']; norm_num
    rw [a1, a2]
    have : t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * ((b : ℝ) / a * t) ≤
        t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t := by gcongr
    nlinarith
  set X := t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ))
  set Y := t ^ (-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * ((b : ℝ) / a)
  have hY0 : 0 ≤ Y := by positivity
  have e : (-(11 / 2 : ℝ)) * t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) +
      t ^ (-(11 / 2 : ℝ)) * ((-(11 / 2 : ℝ)) * mfun a b ℓ t ^ (-(13 / 2 : ℝ)) * ((b : ℝ) / a)) =
      -(11 / 2) * X - (11 / 2) * Y := by simp only [X, Y]; ring
  rw [e, abs_le]
  have : 11 * t ^ (-(13 / 2 : ℝ)) * mfun a b ℓ t ^ (-(11 / 2 : ℝ)) = 11 * X := by
    simp only [X]; ring
  rw [this]
  constructor <;> nlinarith

lemma lam_mul_wAB (n : ℕ) (hn : 1 ≤ n) (hd : (a : ℕ) ∣ b * n + ℓ) :
    lam ((b * n + ℓ) / a) * lam n = wAB a b ℓ n * cR a b ℓ n := by
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  have hm : (((b * n + ℓ) / a : ℕ) : ℝ) = mfun a b ℓ n := by
    unfold mfun
    rw [Nat.cast_div hd (by exact_mod_cast a.ne_zero)]
    push_cast; ring
  rw [cR_natCast, cAR_natCast, if_pos hd]
  unfold lam wAB
  rw [hm]
  push_cast
  ring

lemma tsum_inner (n N : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Icc 1 N, if (a : ℤ) * m - b * n = ℓ then lam m * lam n else 0) =
      if b * n + ℓ ≤ a * N then wAB a b ℓ n * cR a b ℓ n else 0 := by
  by_cases hd : (a : ℕ) ∣ b * n + ℓ
  · obtain ⟨m₀, hm₀⟩ := hd
    have hm₀' : (b * n + ℓ) / (a : ℕ) = m₀ := by
      rw [hm₀]; exact Nat.mul_div_cancel_left _ a.pos
    have hc : ∀ m : ℕ, ((a : ℤ) * m - b * n = ℓ ↔ m = m₀) := by
      intro m
      constructor
      · intro h
        have : (a : ℤ) * m = a * m₀ := by
          have h2 : ((b * n + ℓ : ℕ) : ℤ) = ((a * m₀ : ℕ) : ℤ) := by rw [hm₀]
          push_cast at h2; linarith
        exact_mod_cast mul_left_cancel₀ (by exact_mod_cast a.ne_zero) this
      · rintro rfl
        have h2 : ((b * n + ℓ : ℕ) : ℤ) = ((a * m : ℕ) : ℤ) := by rw [hm₀]
        push_cast at h2; linarith
    simp_rw [hc]
    rw [sum_ite_eq']
    have hm1 : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h | h
      · rw [h] at hm₀; have : 1 ≤ b * n := Nat.one_le_iff_ne_zero.2
          (Nat.mul_ne_zero b.ne_zero (by omega))
        omega
      · exact h
    have hiff : m₀ ∈ Icc 1 N ↔ b * n + ℓ ≤ a * N := by
      rw [mem_Icc, hm₀]
      constructor
      · rintro ⟨-, h⟩; exact Nat.mul_le_mul_left _ h
      · intro h; exact ⟨hm1, Nat.le_of_mul_le_mul_left h a.pos⟩
    by_cases hN : b * n + ℓ ≤ a * N
    · rw [if_pos (hiff.2 hN), if_pos hN, ← hm₀', lam_mul_wAB a b ℓ n hn ⟨m₀, hm₀⟩]
    · rw [if_neg (fun h => hN (hiff.1 h)), if_neg hN]
  · have hz : ∀ m : ℕ, ¬ ((a : ℤ) * m - b * n = ℓ) := by
      intro m h
      apply hd
      refine ⟨m, ?_⟩
      have : ((b * n + ℓ : ℕ) : ℤ) = ((a * m : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    simp only [hz, if_false, sum_const_zero]
    have hcR : cR a b ℓ n = 0 := by rw [cR_natCast, cAR_natCast, if_neg hd, mul_zero]
    rw [hcR, mul_zero]; split_ifs <;> rfl

/-- The cut-off `N₁ = min(N, ⌊(aN − ℓ)/b⌋)`. -/
def N1 (N : ℕ) : ℕ := min N ((a * N - ℓ) / b)

lemma mem_N1_iff (N n : ℕ) (hn : 1 ≤ n) : (n ≤ N ∧ b * n + ℓ ≤ a * N) ↔ n ≤ N1 a b ℓ N := by
  unfold N1
  rw [le_min_iff, Nat.le_div_iff_mul_le b.pos]
  have : b * n = n * b := mul_comm _ _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : 1 ≤ n * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) b.ne_zero)
    omega

/-- **The two-sided sum as a weighted sum of `cR`.** -/
theorem shiftSum2_eq (N : ℕ) :
    shiftSum2 a b ℓ N = ∑ n ∈ Icc 0 (N1 a b ℓ N), wAB a b ℓ n * cR a b ℓ n := by
  unfold shiftSum2
  rw [sum_comm]
  rw [sum_congr rfl fun n hn => tsum_inner a b ℓ n N (mem_Icc.1 hn).1]
  rw [← sum_filter]
  have h0 : Icc 0 (N1 a b ℓ N) = insert 0 (Icc 1 (N1 a b ℓ N)) := by
    ext n; simp only [mem_Icc, mem_insert]; omega
  rw [h0, sum_insert (by simp), cR_zero, mul_zero, zero_add]
  refine sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, (mem_N1_iff a b ℓ N n h1).1 ⟨h2, h3⟩⟩
  · rintro ⟨h1, h2⟩
    have := (mem_N1_iff a b ℓ N n h1).2 h2
    exact ⟨⟨h1, this.1⟩, this.2⟩

lemma N1_le (N : ℕ) : N1 a b ℓ N ≤ N := min_le_left _ _

end RamanujanTau.SCS2Coprime
