/-
# Change of argument versus zeros of the real part

For `f : [a,b] → ℂ` differentiable and zero-free, if every zero of `Re f` in `[a,b]` lies in a
finite set `S`, then `|Im ∫ₐᵇ f'/f| ≤ π(|S| + 1)` (`abs_im_integral_logDeriv_le`).

Between consecutive zeros of `Re f`, `±f` has `Re ≥ 0`, so `log(±f)` is a primitive of `f'/f`
there and its imaginary part (an argument with `|arg| ≤ π/2`) changes by at most `π`.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set intervalIntegral MeasureTheory
open scoped Real Interval

section
variable {f f' : ℝ → ℂ}

lemma slit_of_re_nonneg {z : ℂ} (h0 : 0 ≤ z.re) (hz : z ≠ 0) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases h0.lt_or_eq with h | h
  · exact Or.inl h
  · right; intro him; apply hz; apply Complex.ext <;> simp [← h, him]

/-- No zero of `Re f` strictly inside: `|Im ∫ f'/f| ≤ π`. -/
lemma abs_im_integral_le_pi {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hc : ContinuousOn f' (Icc a b))
    (hne : ∀ x ∈ Icc a b, f x ≠ 0) (hz : ∀ x ∈ Ioo a b, (f x).re ≠ 0) :
    |(∫ x in a..b, f' x / f x).im| ≤ π := by
  rcases hab.lt_or_eq with hab' | rfl
  swap
  · simp [Real.pi_pos.le]
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hfm := hz m hm
  -- choose the sign
  obtain ⟨ε, hε0, hεm⟩ : ∃ ε : ℂ, ε ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ 0 < (ε * f m).re := by
    rcases hfm.lt_or_gt with h | h
    · exact ⟨-1, by norm_num, Or.inr rfl, by simp; linarith⟩
    · exact ⟨1, one_ne_zero, Or.inl rfl, by simp; linarith⟩
  have hreε : ∀ x, (ε * f x).re = (if ε = 1 then (f x).re else -(f x).re) := by
    intro x; rcases hεm.1 with h | h <;> subst h <;> norm_num
  have hgc : ContinuousOn (fun x => (ε * f x).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hfc)
  have hzε : ∀ x ∈ Ioo a b, (ε * f x).re ≠ 0 := by
    intro x hx h; rw [hreε] at h; split_ifs at h
    · exact hz x hx h
    · exact hz x hx (by linarith)
  have hnonneg : ∀ x ∈ Icc a b, 0 ≤ (ε * f x).re := by
    intro x hx
    by_contra hneg
    push Not at hneg
    rcases lt_or_ge x m with hxm | hxm
    · obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hxm.le
        (hgc.mono (Icc_subset_Icc hx.1 hm.2.le)) ⟨hneg.le, hεm.2.le⟩
      have hcx : c ≠ x := by rintro rfl; have h' : (ε * f c).re = 0 := hc2; linarith
      exact hzε c ⟨lt_of_le_of_lt hx.1 (lt_of_le_of_ne hc1.1 (Ne.symm hcx)),
        lt_of_le_of_lt hc1.2 hm.2⟩ hc2
    · obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hxm
        (hgc.mono (Icc_subset_Icc hm.1.le hx.2)) ⟨hneg.le, hεm.2.le⟩
      have hcx : c ≠ x := by rintro rfl; have h' : (ε * f c).re = 0 := hc2; linarith
      exact hzε c ⟨lt_of_lt_of_le hm.1 hc1.1, lt_of_lt_of_le (lt_of_le_of_ne hc1.2 hcx) hx.2⟩ hc2
  have hslit : ∀ x ∈ Icc a b, ε * f x ∈ slitPlane :=
    fun x hx => slit_of_re_nonneg (hnonneg x hx) (mul_ne_zero hε0 (hne x hx))
  have hFTC : ∫ x in a..b, f' x / f x = log (ε * f b) - log (ε * f a) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have := ((hf x hx).const_mul ε).clog_real (hslit x hx)
      convert this using 1
      rw [mul_div_mul_left _ _ hε0]
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact hc.div hfc hne
  rw [hFTC, sub_im, log_im, log_im]
  have h1 := abs_arg_le_pi_div_two_iff.mpr (hnonneg b ⟨hab, le_rfl⟩)
  have h2 := abs_arg_le_pi_div_two_iff.mpr (hnonneg a ⟨le_rfl, hab⟩)
  calc |arg (ε * f b) - arg (ε * f a)| ≤ |arg (ε * f b)| + |arg (ε * f a)| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring

lemma integrable_logDeriv {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hc : ContinuousOn f' (Icc a b))
    (hne : ∀ x ∈ Icc a b, f x ≠ 0) : IntervalIntegrable (fun x => f' x / f x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hc.div (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hne

/-- **Argument change versus zeros of `Re f`.** -/
theorem abs_im_integral_logDeriv_le (n : ℕ) : ∀ (a b : ℝ), a ≤ b →
    (∀ x ∈ Icc a b, HasDerivAt f (f' x) x) → ContinuousOn f' (Icc a b) →
    (∀ x ∈ Icc a b, f x ≠ 0) → ∀ S : Finset ℝ, S.card ≤ n →
    (∀ x ∈ Ioo a b, (f x).re = 0 → x ∈ S) →
    |(∫ x in a..b, f' x / f x).im| ≤ π * (S.card + 1) := by
  induction n with
  | zero =>
    intro a b hab hf hc hne S hS hSz
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    have := abs_im_integral_le_pi hab hf hc hne (fun x hx h => by
      have := hSz x hx h; rw [hS0] at this; simp at this)
    simpa [hS0] using this
  | succ n ih =>
    intro a b hab hf hc hne S hS hSz
    by_cases hex : ∃ c ∈ Ioo a b, (f c).re = 0
    · obtain ⟨c, hc_mem, hc0⟩ := hex
      have hcS : c ∈ S := hSz c hc_mem hc0
      classical
      set S₁ := S.filter (· < c)
      set S₂ := S.filter (c < ·)
      have hcard : S₁.card + S₂.card + 1 ≤ S.card := by
        have hdisj : Disjoint S₁ S₂ := by
          rw [Finset.disjoint_filter]; intro x _ h1 h2; linarith
        have hsub : S₁ ∪ S₂ ⊆ S.erase c := by
          intro x hx
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hx
          rw [Finset.mem_erase]
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨ne_of_lt h2, h1⟩
          · exact ⟨ne_of_gt h2, h1⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hcS] at this
        have := Finset.card_pos.mpr ⟨c, hcS⟩
        omega
      have hac : a ≤ c := hc_mem.1.le
      have hcb : c ≤ b := hc_mem.2.le
      have h1 := ih a c hac (fun x hx => hf x ⟨hx.1, hx.2.trans hcb⟩) (hc.mono (Icc_subset_Icc le_rfl hcb))
        (fun x hx => hne x ⟨hx.1, hx.2.trans hcb⟩) S₁ (by omega) (fun x hx h0 => by
          rw [Finset.mem_filter]
          exact ⟨hSz x ⟨hx.1, hx.2.trans hc_mem.2⟩ h0, hx.2⟩)
      have h2 := ih c b hcb (fun x hx => hf x ⟨hac.trans hx.1, hx.2⟩) (hc.mono (Icc_subset_Icc hac le_rfl))
        (fun x hx => hne x ⟨hac.trans hx.1, hx.2⟩) S₂ (by omega) (fun x hx h0 => by
          rw [Finset.mem_filter]
          exact ⟨hSz x ⟨hc_mem.1.trans hx.1, hx.2⟩ h0, hx.1⟩)
      rw [← integral_add_adjacent_intervals
        (integrable_logDeriv hac (fun x hx => hf x ⟨hx.1, hx.2.trans hcb⟩)
          (hc.mono (Icc_subset_Icc le_rfl hcb)) (fun x hx => hne x ⟨hx.1, hx.2.trans hcb⟩))
        (integrable_logDeriv hcb (fun x hx => hf x ⟨hac.trans hx.1, hx.2⟩)
          (hc.mono (Icc_subset_Icc hac le_rfl)) (fun x hx => hne x ⟨hac.trans hx.1, hx.2⟩)),
        add_im]
      have hcard' : ((S₁.card : ℝ) + 1) + ((S₂.card : ℝ) + 1) ≤ S.card + 1 := by
        have : ((S₁.card + S₂.card + 1 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hcard
        push_cast at this; linarith
      calc _ ≤ |(∫ x in a..c, f' x / f x).im| + |(∫ x in c..b, f' x / f x).im| := abs_add_le _ _
        _ ≤ π * (S₁.card + 1) + π * (S₂.card + 1) := add_le_add h1 h2
        _ ≤ π * (S.card + 1) := by nlinarith [Real.pi_pos]
    · push Not at hex
      have := abs_im_integral_le_pi hab hf hc hne hex
      have : π ≤ π * (S.card + 1) := by
        have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
        nlinarith [Real.pi_pos]
      linarith

end

end RamanujanTau.ZeroCountRvM
