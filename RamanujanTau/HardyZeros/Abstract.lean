/-
# Hardy's argument, abstract real-variable form

Let `Z : ℝ → ℝ` be continuous and even, with `Z(t) e^{at}` integrable for `0 ≤ a < π/2`, and
suppose that `H(a) = ∫ Z(t) e^{at} dt` vanishes to infinite order at `a = π/2`:
`|H(π/2 − β)| ≤ C_N β^N` for small `β > 0`.  Then `Z` has arbitrarily large zeros.

Proof (finite-difference form of Hardy's moment argument).  If `Z > 0` on `|t| ≥ T`, put
`α = π/2 − β`, `δ = β/(2m)` (`m` even) and `w(t) = e^{αt}(e^{δt} − 1)^m ≥ 0`.  Expanding,
`∫ Z w = Σ_j (−1)^{m−j} C(m,j) H(α + jδ)`, all nodes in `[π/2 − β, π/2 − β/2]`, so
`|∫ Z w| ≤ 2^m C β^{m+1}`.  On the other hand `∫ Z w ≥ c₀ (δ(T+1))^m − K (δT)^m` where
`c₀ = ∫_{T+1}^{T+2} Z > 0`.  Dividing by `δ^m` and letting `β → 0`:
`c₀ (T+1)^m ≤ K T^m` for every even `m`, impossible as `m → ∞`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.HardyZeros

open MeasureTheory Set Real Filter

lemma abs_exp_sub_one_le' (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hx]
    have h2 := Real.add_one_le_exp (-x)
    have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (Real.exp_pos x).le]
  · have h1 : Real.exp x < 1 := by simpa using Real.exp_lt_exp.mpr hx
    rw [abs_of_neg (by linarith), abs_of_neg hx]
    have h2 := Real.add_one_le_exp x
    have h3 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -x by linarith) (sub_nonneg.2 h3)]

lemma le_zero_of_forall_le_mul {x Y β₁ : ℝ} (hβ₁ : 0 < β₁)
    (h : ∀ β, 0 < β → β ≤ β₁ → x ≤ Y * β) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  set β := min β₁ (x / (2 * (|Y| + 1))) with hβ
  have hpos : 0 < β := lt_min hβ₁ (by positivity)
  have h1 := h β hpos (min_le_left _ _)
  have h2 : β ≤ x / (2 * (|Y| + 1)) := min_le_right _ _
  have h3 : Y * β ≤ |Y| * β := mul_le_mul_of_nonneg_right (le_abs_self Y) hpos.le
  have h4 : |Y| * β ≤ |Y| * (x / (2 * (|Y| + 1))) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h5 : |Y| * (x / (2 * (|Y| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg Y]
  linarith

/-- The finite-difference estimate: for even `m ≥ 1`, `c₀ (T+1)^m − K T^m ≤ Y β` for all small
`β`. -/
theorem core (Z : ℝ → ℝ) (hc : Continuous Z) (heven : ∀ t, Z (-t) = Z t)
    (hint : ∀ a, 0 ≤ a → a < π / 2 → Integrable (fun t => Z t * Real.exp (a * t)))
    (hdec : ∀ N : ℕ, ∃ C β₀ : ℝ, 0 < β₀ ∧ ∀ β, 0 < β → β ≤ β₀ →
      |∫ t, Z t * Real.exp ((π / 2 - β) * t)| ≤ C * β ^ N)
    {T : ℝ} (hT : 1 ≤ T) (hpos : ∀ t, T ≤ t → 0 < Z t) : False := by
  have hT0 : 0 < T := by linarith
  have hposAbs : ∀ t, T ≤ |t| → 0 < Z t := by
    intro t ht
    rcases le_or_gt 0 t with h | h
    · exact hpos t (by rwa [abs_of_nonneg h] at ht)
    · rw [← heven t]; exact hpos (-t) (by rwa [abs_of_neg h] at ht)
  set c₀ : ℝ := ∫ t in (T + 1)..(T + 2), Z t with hc₀
  have hc₀pos : 0 < c₀ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
      (fun x hx => hpos x (by linarith [hx.1])) (by linarith)
  set M : ℝ := ∫ t in (-T)..T, |Z t| with hM
  set K : ℝ := M * Real.exp (π / 2 * T) * Real.exp 1 with hK
  -- the key inequality for each even m ≥ 1
  have key : ∀ m : ℕ, 0 < m → Even m → c₀ * (T + 1) ^ m ≤ K * T ^ m := by
    intro m hm hme
    obtain ⟨C, β₀, hβ₀, hC⟩ := hdec (m + 1)
    have hC0 : 0 ≤ C := by
      have := (abs_nonneg _).trans (hC β₀ hβ₀ le_rfl)
      exact nonneg_of_mul_nonneg_left this (pow_pos hβ₀ _)
    set β₁ : ℝ := min β₀ (1 / T) with hβ₁
    have hβ₁pos : 0 < β₁ := lt_min hβ₀ (by positivity)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    suffices H : ∀ β, 0 < β → β ≤ β₁ →
        c₀ * (T + 1) ^ m - K * T ^ m ≤ (2 ^ m * C * (2 * m) ^ m) * β by
      have := le_zero_of_forall_le_mul hβ₁pos H
      linarith
    intro β hβ hββ₁
    have hββ₀ : β ≤ β₀ := hββ₁.trans (min_le_left _ _)
    have hβT : β * T ≤ 1 := by
      have : β ≤ 1 / T := hββ₁.trans (min_le_right _ _)
      rwa [le_div_iff₀ hT0] at this
    have hβ1 : β ≤ 1 := by nlinarith
    set α : ℝ := π / 2 - β with hα
    set δ : ℝ := β / (2 * m) with hδ
    have hδpos : 0 < δ := by positivity
    have hα0 : 0 ≤ α := by have := Real.pi_gt_three; linarith
    have hαle : α ≤ π / 2 := by linarith
    have hmδ : (m : ℝ) * δ = β / 2 := by rw [hδ]; field_simp
    have hδle : δ ≤ β := by
      rw [hδ, div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    -- the weight
    set w : ℝ → ℝ := fun t => Real.exp (α * t) * (Real.exp (δ * t) - 1) ^ m with hw
    set f : ℝ → ℝ := fun t => Z t * w t with hf
    set cj : ℕ → ℝ := fun j => (-1) ^ (m - j) * (m.choose j : ℝ) with hcj
    have hnode : ∀ j ∈ Finset.range (m + 1), 0 ≤ α + j * δ ∧ α + j * δ < π / 2 := by
      intro j hj
      have hjm : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      refine ⟨by positivity, ?_⟩
      have : (j : ℝ) * δ ≤ m * δ := mul_le_mul_of_nonneg_right hjm hδpos.le
      rw [hmδ] at this
      linarith
    have hexpand : f = fun t => ∑ j ∈ Finset.range (m + 1),
        cj j * (Z t * Real.exp ((α + j * δ) * t)) := by
      funext t
      simp only [hf, hw, hcj]
      rw [sub_eq_add_neg, add_pow, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Real.exp_nat_mul,
        show (α + j * δ) * t = α * t + j * (δ * t) by ring, Real.exp_add]
      ring
    have hfint : Integrable f := by
      rw [hexpand]
      exact integrable_finsetSum _ fun j hj =>
        (hint _ (hnode j hj).1 (hnode j hj).2).const_mul _
    have hfcont : Continuous f := by
      simp only [hf, hw]; fun_prop
    -- (i)+(ii): upper bound via the decay of H
    have hupper : |∫ t, f t| ≤ 2 ^ m * C * β ^ (m + 1) := by
      have hint_eq : ∫ t, f t = ∑ j ∈ Finset.range (m + 1),
          cj j * ∫ t, Z t * Real.exp ((α + j * δ) * t) := by
        rw [hexpand, integral_finsetSum _ fun j hj =>
          (hint _ (hnode j hj).1 (hnode j hj).2).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_const_mul _ _
      rw [hint_eq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hbound : ∀ j ∈ Finset.range (m + 1),
          |cj j * ∫ t, Z t * Real.exp ((α + j * δ) * t)| ≤
            (m.choose j : ℝ) * (C * β ^ (m + 1)) := by
        intro j hj
        have hjm : (j : ℝ) ≤ m := by
          exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [abs_mul]
        have hcabs : |cj j| = (m.choose j : ℝ) := by
          simp [hcj, abs_mul, abs_pow]
        rw [hcabs]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        set βj : ℝ := β - j * δ with hβj
        have hjδ : (j : ℝ) * δ ≤ β / 2 := by
          rw [← hmδ]; exact mul_le_mul_of_nonneg_right hjm hδpos.le
        have hβjpos : 0 < βj := by
          have : 0 ≤ (j : ℝ) * δ := by positivity
          linarith
        have hβjle : βj ≤ β := by
          have : 0 ≤ (j : ℝ) * δ := by positivity
          linarith
        have he : α + j * δ = π / 2 - βj := by rw [hα, hβj]; ring
        rw [he]
        refine (hC βj hβjpos (hβjle.trans hββ₀)).trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβjpos.le hβjle _) hC0
      refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
      rw [← Finset.sum_mul]
      have hs : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = 2 ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [hs]; ring
    -- (iii) split off A = (−T, T]
    set A : Set ℝ := Ioc (-T) T with hA
    have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioc : MeasurableSet A) hfint
    have hwnn : ∀ t, 0 ≤ w t := fun t =>
      mul_nonneg (Real.exp_pos _).le (hme.pow_nonneg _)
    have hcompl : ∫ t in (T + 1)..(T + 2), f t ≤ ∫ t in Aᶜ, f t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      refine setIntegral_mono_set hfint.integrableOn ?_ ?_
      · refine ae_restrict_of_forall_mem (measurableSet_Ioc.compl) fun t ht => ?_
        have hTt : T ≤ |t| := by
          simp only [hA, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
          rcases ht with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        exact mul_nonneg (hposAbs t hTt).le (hwnn t)
      · refine Eventually.of_forall fun t ht => ?_
        have h1 : T + 1 < t := ht.1
        show t ∉ Ioc (-T) T
        rintro ⟨_, h2⟩
        linarith
    -- (iv) lower bound on (T+1, T+2]
    have hB : c₀ * (δ * (T + 1)) ^ m ≤ ∫ t in (T + 1)..(T + 2), f t := by
      rw [hc₀, ← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((hc.mul continuous_const).intervalIntegrable _ _)
        (hfcont.intervalIntegrable _ _) fun x hx => ?_
      have hx0 : 0 ≤ x := by linarith [hx.1]
      simp only [hf, hw]
      refine mul_le_mul_of_nonneg_left ?_ (hpos x (by linarith [hx.1])).le
      have h1 : δ * (T + 1) ≤ Real.exp (δ * x) - 1 := by
        have := Real.add_one_le_exp (δ * x)
        have : δ * (T + 1) ≤ δ * x := mul_le_mul_of_nonneg_left hx.1 hδpos.le
        linarith
      have h2 : (δ * (T + 1)) ^ m ≤ (Real.exp (δ * x) - 1) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 _
      have h3 : 1 ≤ Real.exp (α * x) := Real.one_le_exp (mul_nonneg hα0 hx0)
      have h4 : 0 ≤ (Real.exp (δ * x) - 1) ^ m := le_trans (by positivity) h2
      nlinarith
    -- (v) the bounded part
    set Bw : ℝ := Real.exp (π / 2 * T) * Real.exp 1 * (δ * T) ^ m with hBw
    have hAbound : |∫ t in A, f t| ≤ M * Bw := by
      rw [hA, ← intervalIntegral.integral_of_le (by linarith)]
      refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
      rw [hM, ← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_mono_on (by linarith)
        (hfcont.abs.intervalIntegrable _ _)
        ((hc.abs.mul continuous_const).intervalIntegrable _ _) fun x hx => ?_
      simp only [hf, hw, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hxT : |x| ≤ T := abs_le.mpr ⟨hx.1, hx.2⟩
      have e1 : Real.exp (α * x) ≤ Real.exp (π / 2 * T) := by
        apply Real.exp_le_exp.mpr
        have : α * x ≤ α * T := mul_le_mul_of_nonneg_left hx.2 hα0
        have : α * T ≤ π / 2 * T := mul_le_mul_of_nonneg_right hαle hT0.le
        linarith
      have e2 : |Real.exp (δ * x) - 1| ≤ δ * T * Real.exp (δ * T) := by
        refine (abs_exp_sub_one_le' _).trans ?_
        have : |δ * x| ≤ δ * T := by
          rw [abs_mul, abs_of_pos hδpos]; exact mul_le_mul_of_nonneg_left hxT hδpos.le
        exact mul_le_mul this (Real.exp_le_exp.mpr this) (Real.exp_pos _).le (by positivity)
      have e3 : |Real.exp (δ * x) - 1| ^ m ≤ (δ * T) ^ m * Real.exp 1 := by
        refine (pow_le_pow_left₀ (abs_nonneg _) e2 _).trans ?_
        rw [mul_pow, ← Real.exp_nat_mul]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have : (m : ℝ) * (δ * T) = β / 2 * T := by rw [← mul_assoc, hmδ]
        rw [this]; nlinarith
      calc Real.exp (α * x) * |Real.exp (δ * x) - 1| ^ m
          ≤ Real.exp (π / 2 * T) * ((δ * T) ^ m * Real.exp 1) :=
            mul_le_mul e1 e3 (by positivity) (Real.exp_pos _).le
        _ = Bw := by rw [hBw]; ring
    -- (vi) combine
    have hlow : c₀ * (δ * (T + 1)) ^ m - M * Bw ≤ ∫ t, f t := by
      have := neg_abs_le (∫ t in A, f t)
      linarith
    have hchain : δ ^ m * (c₀ * (T + 1) ^ m - K * T ^ m) ≤
        δ ^ m * ((2 ^ m * C * (2 * m) ^ m) * β) := by
      have e1 : δ ^ m * (c₀ * (T + 1) ^ m - K * T ^ m) = c₀ * (δ * (T + 1)) ^ m - M * Bw := by
        rw [hBw, hK, mul_pow, mul_pow]; ring
      have hβeq : β = 2 * m * δ := by rw [hδ]; field_simp
      have e2 : 2 ^ m * C * β ^ (m + 1) = δ ^ m * ((2 ^ m * C * (2 * m) ^ m) * β) := by
        rw [pow_succ, hβeq, mul_pow]; ring
      rw [e1, ← e2]
      exact hlow.trans ((le_abs_self _).trans hupper)
    exact le_of_mul_le_mul_left hchain (pow_pos hδpos _)
  -- contradiction as m → ∞
  obtain ⟨n, hn⟩ := exists_nat_gt (K * T / c₀)
  have hk := key (2 * (n + 1)) (by omega) (even_two_mul _)
  set m := 2 * (n + 1) with hmdef
  have hbern : 1 + (m : ℝ) * (1 / T) ≤ (1 + 1 / T) ^ m :=
    one_add_mul_le_pow (by have : 0 < 1 / T := (by positivity); linarith) m
  have hTm : 0 < T ^ m := pow_pos hT0 _
  have hfac : (T + 1) ^ m = T ^ m * (1 + 1 / T) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac] at hk
  have h1 : c₀ * (1 + 1 / T) ^ m ≤ K := by
    have : T ^ m * (c₀ * (1 + 1 / T) ^ m) ≤ T ^ m * K := by nlinarith
    exact le_of_mul_le_mul_left this hTm
  have h2 : c₀ * (1 + (m : ℝ) * (1 / T)) ≤ K := (mul_le_mul_of_nonneg_left hbern hc₀pos.le).trans h1
  have hmn : (n : ℝ) < m := by rw [hmdef]; push_cast; linarith
  have h3 : K * T / c₀ < m := hn.trans hmn
  rw [div_lt_iff₀ hc₀pos] at h3
  have h4 : c₀ * ((m : ℝ) * (1 / T)) * T = c₀ * m := by field_simp
  have h5 : c₀ * ((m : ℝ) * (1 / T)) ≤ K := by nlinarith
  have h6 : c₀ * m ≤ K * T := by
    rw [← h4]; exact mul_le_mul_of_nonneg_right h5 hT0.le
  linarith

/-- **Hardy's argument, abstract form**: an even continuous real `Z` whose exponential moments
`H(a) = ∫ Z(t) e^{at} dt` vanish to infinite order at `a = π/2` has arbitrarily large zeros. -/
theorem hardy_abstract (Z : ℝ → ℝ) (hc : Continuous Z) (heven : ∀ t, Z (-t) = Z t)
    (hint : ∀ a, 0 ≤ a → a < π / 2 → Integrable (fun t => Z t * Real.exp (a * t)))
    (hdec : ∀ N : ℕ, ∃ C β₀ : ℝ, 0 < β₀ ∧ ∀ β, 0 < β → β ≤ β₀ →
      |∫ t, Z t * Real.exp ((π / 2 - β) * t)| ≤ C * β ^ N) :
    ∀ T : ℝ, ∃ t > T, Z t = 0 := by
  intro T
  by_contra hno
  push Not at hno
  set T' : ℝ := max T 0 + 1 with hT'
  have hT'1 : 1 ≤ T' := by have := le_max_right T 0; linarith
  have hne : ∀ t, T' ≤ t → Z t ≠ 0 := fun t ht =>
    hno t (by have := le_max_left T 0; linarith)
  -- constant sign on [T', ∞)
  have hsign : (∀ t, T' ≤ t → 0 < Z t) ∨ (∀ t, T' ≤ t → Z t < 0) := by
    by_contra hmix
    push Not at hmix
    obtain ⟨⟨a, ha, hZa⟩, ⟨b, hb, hZb⟩⟩ := hmix
    have hZa' : Z a < 0 := lt_of_le_of_ne hZa (hne a ha)
    have hZb' : 0 < Z b := lt_of_le_of_ne hZb (Ne.symm (hne b hb))
    have hpc : IsPreconnected (Ici T') := isPreconnected_Ici
    obtain ⟨c, hc', hZc⟩ := hpc.intermediate_value (mem_Ici.mpr ha) (mem_Ici.mpr hb)
      hc.continuousOn ⟨hZa'.le, hZb'.le⟩
    exact hne c hc' hZc
  rcases hsign with hp | hn
  · exact core Z hc heven hint hdec hT'1 hp
  · refine core (fun t => -Z t) hc.neg (fun t => by simp [heven t]) ?_ ?_ hT'1
      (fun t ht => neg_pos.mpr (hn t ht))
    · intro a ha0 ha
      simpa [neg_mul] using (hint a ha0 ha).neg
    · intro N
      obtain ⟨C, β₀, hβ₀, hC⟩ := hdec N
      refine ⟨C, β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
      have := hC β hβ hββ₀
      simpa [neg_mul, integral_neg, abs_neg] using this

end RamanujanTau.HardyZeros
