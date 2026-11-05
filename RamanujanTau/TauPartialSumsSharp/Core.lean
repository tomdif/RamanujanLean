/-
# Landau's differencing for complex coefficients and complex kernels

`DkC h r` is the `r`-th forward difference `Δ_h^r` of a function `ℝ → ℂ`.

* `bracket_signed`: for complex `aₙ` (any signs/phases),
  `‖r!h^r A(x) − Δ_h^r W_r(x)‖ ≤ r!h^r ∑_{x<n≤x+rh} ‖aₙ‖`. It is reduced to the real
  bracket `RankinError.bracket` applied to a single coefficient `δ_n`, for each `n`.
* `DkC_family_bound`: for a family with `G_{j+1}(y+h) − G_{j+1}(y) = (j+1)∫₀^h G_j(y+s) ds`,
  `‖Δ_h^j G_j(x)‖ ≤ j! h^j sup‖G_0‖` — all the way down to the bottom kernel `G_0`.
* `landau_ineq`: from an exact dual expansion `W_r(y) = c ∑ aₙ n^{−k−r} J_r(ny)` with kernels
  linked by `J_{j+1}' = (j+1)J_j`, `‖J_0(y)‖ ≤ A y^{β₀}` and `‖J_r(y)‖ ≤ A y^{β_r}`, and any
  cut `M ≥ 1`:

      ‖A(x)‖ ≤ ‖c‖ L A ((x+rh)^{β₀} M^{β₀−k+γ} + 2^r/(r!h^r) (x+rh)^{β_r} M^{β_r−k−r+γ})
                + ∑_{x<n≤x+rh} ‖aₙ‖,

  `L = ∑ ‖aₙ‖ n^{−γ}` (Rankin's trick `n^{β₀−k} ≤ M^{β₀−k+γ} n^{−γ}` for `n ≤ M`, and
  `n^{β_r−k−r} ≤ M^{β_r−k−r+γ} n^{−γ}` for `n > M`).
-/
import RamanujanTau.TauPartialSumsSharp.Dual
import RamanujanTau.TauPartialSums.Differencing
import RamanujanTau.RankinError.RieszK

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinError

/-! ### The complex difference operator -/

/-- `DkC h r f = Δ_h^r f` for `f : ℝ → ℂ`. -/
noncomputable def DkC (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | r + 1, f => DkC h r (fun x => f (x + h) - f x)

lemma DkC_congr_on (h : ℝ) (hh : 0 ≤ h) (r : ℕ) : ∀ (f g : ℝ → ℂ) (x : ℝ),
    (∀ y ∈ Icc x (x + r * h), f y = g y) → DkC h r f x = DkC h r g x := by
  induction r with
  | zero => intro f g x hfg; simpa [DkC] using hfg x ⟨le_rfl, by simp⟩
  | succ r ih =>
    intro f g x hfg
    simp only [DkC]
    apply ih
    intro y hy
    have h1 := hfg (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
    have h2 := hfg y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
    rw [h1, h2]

lemma DkC_const_mul (h : ℝ) (r : ℕ) : ∀ (c : ℂ) (f : ℝ → ℂ) (x : ℝ),
    DkC h r (fun y => c * f y) x = c * DkC h r f x := by
  induction r with
  | zero => intro c f x; rfl
  | succ r ih =>
    intro c f x
    simp only [DkC]
    rw [← ih]
    congr 1; funext y; ring

lemma DkC_tsum_on (h : ℝ) (hh : 0 ≤ h) (r : ℕ) : ∀ (f : ℕ → ℝ → ℂ) (x : ℝ),
    (∀ y ∈ Icc x (x + r * h), Summable fun n => f n y) →
    DkC h r (fun y => ∑' n, f n y) x = ∑' n, DkC h r (f n) x := by
  induction r with
  | zero => intro f x _; rfl
  | succ r ih =>
    intro f x hs
    simp only [DkC]
    have hc : ∀ y ∈ Icc x (x + r * h),
        (∑' n, f n (y + h)) - ∑' n, f n y = ∑' n, (f n (y + h) - f n y) := by
      intro y hy
      have h1 := hs (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
      have h2 := hs y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
      exact (h1.tsum_sub h2).symm
    rw [DkC_congr_on h hh r _ _ x hc]
    refine ih (fun n y => f n (y + h) - f n y) x (fun y hy => ?_)
    have h1 := hs (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
    have h2 := hs y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
    exact h1.sub h2

lemma intervalIntegrable_shift_of_continuousOn {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    {h : ℝ} (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun s => g (y + s)) volume 0 h := by
  apply ContinuousOn.intervalIntegrable
  refine hg.comp (continuous_const.add continuous_id).continuousOn (fun s hs => ?_)
  rw [uIcc_of_le hh] at hs
  simp only [Set.mem_Ioi]; linarith [hs.1]

lemma DkC_integral_on (h : ℝ) (hh : 0 ≤ h) (r : ℕ) : ∀ (g : ℝ → ℂ), ContinuousOn g (Ioi 0) →
    ∀ x : ℝ, 0 < x →
    DkC h r (fun y => ∫ s in (0 : ℝ)..h, g (y + s)) x = ∫ s in (0 : ℝ)..h, DkC h r g (x + s) := by
  induction r with
  | zero => intro g _ x _; rfl
  | succ r ih =>
    intro g hg x hx
    simp only [DkC]
    have hc : ∀ y ∈ Icc x (x + r * h),
        (∫ s in (0 : ℝ)..h, g (y + h + s)) - (∫ s in (0 : ℝ)..h, g (y + s)) =
          ∫ s in (0 : ℝ)..h, (fun z => g (z + h) - g z) (y + s) := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_shift_of_continuousOn hg hh (by linarith : 0 < y + h))
        (intervalIntegrable_shift_of_continuousOn hg hh hy0)]
      congr 1; funext s; simp only; ring_nf
    rw [DkC_congr_on h hh r _ _ x hc]
    have hg' : ContinuousOn (fun z => g (z + h) - g z) (Ioi 0) := by
      refine (hg.comp (continuous_add_right h).continuousOn (fun z hz => ?_)).sub hg
      simp only [Set.mem_Ioi] at hz ⊢; linarith
    exact ih (fun z => g (z + h) - g z) hg' x hx

lemma norm_DkC_le (h : ℝ) (hh : 0 ≤ h) (r : ℕ) : ∀ (f : ℝ → ℂ) (x B : ℝ),
    (∀ y ∈ Icc x (x + r * h), ‖f y‖ ≤ B) → ‖DkC h r f x‖ ≤ 2 ^ r * B := by
  induction r with
  | zero =>
    intro f x B hB
    simpa using hB x ⟨le_rfl, by simp⟩
  | succ r ih =>
    intro f x B hB
    simp only [DkC]
    have := ih (fun y => f (y + h) - f y) x (2 * B) (fun y hy => by
      have h1 := hB (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
      have h2 := hB y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
      calc ‖f (y + h) - f y‖ ≤ ‖f (y + h)‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith)
    rw [pow_succ]; linarith

/-- **All the way down to the bottom kernel.** -/
lemma DkC_family_bound (G : ℕ → ℝ → ℂ) (R : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hcont : ∀ j, ContinuousOn (G j) (Ioi 0))
    (hrel : ∀ j, j < R → ∀ y, 0 < y →
      G (j + 1) (y + h) - G (j + 1) y = ((j : ℂ) + 1) * ∫ s in (0 : ℝ)..h, G j (y + s))
    {B : ℝ} :
    ∀ j, j ≤ R → ∀ x, 0 < x → (∀ y ∈ Icc x (x + (j : ℝ) * h), ‖G 0 y‖ ≤ B) →
      ‖DkC h j (G j) x‖ ≤ (Nat.factorial j : ℝ) * h ^ j * B := by
  intro j
  induction j with
  | zero =>
    intro _ x _ hB
    simpa [DkC] using hB x ⟨le_rfl, by simp⟩
  | succ j ih =>
    intro hjR x hx hB
    simp only [DkC]
    have hc : ∀ y ∈ Icc x (x + (j : ℝ) * h),
        G (j + 1) (y + h) - G (j + 1) y = ((j : ℂ) + 1) * ∫ s in (0 : ℝ)..h, G j (y + s) := by
      intro y hy
      exact hrel j (by omega) y (by linarith [hy.1])
    rw [DkC_congr_on h hh j _ _ x hc, DkC_const_mul,
      DkC_integral_on h hh j _ (hcont _) x hx]
    set C : ℝ := (Nat.factorial j : ℝ) * h ^ j * B with hC
    have hI : ‖∫ s in (0 : ℝ)..h, DkC h j (G j) (x + s)‖ ≤ C * |h - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
      rw [uIoc_of_le hh] at hs
      refine ih (by omega) (x + s) (by linarith [hs.1]) (fun y hy => hB y ⟨?_, ?_⟩)
      · linarith [hy.1, hs.1]
      · have := hy.2; push_cast at this ⊢; nlinarith [hs.2]
    rw [sub_zero, abs_of_nonneg hh] at hI
    rw [norm_mul]
    have hj1 : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by
      rw [show (j : ℂ) + 1 = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hj1]
    calc ((j : ℝ) + 1) * ‖∫ s in (0 : ℝ)..h, DkC h j (G j) (x + s)‖
        ≤ ((j : ℝ) + 1) * (C * h) := by gcongr
      _ = (Nat.factorial (j + 1) : ℝ) * h ^ (j + 1) * B := by
          rw [hC, Nat.factorial_succ]; push_cast; ring

/-! ### The signed bracket -/

/-- The single coefficient `δ_n`. -/
noncomputable def delta (n : ℕ) (m : ℕ) : ℝ := if m = n then 1 else 0

lemma delta_nonneg (n m : ℕ) : 0 ≤ delta n m := by unfold delta; split_ifs <;> norm_num

lemma W_delta (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (y : ℝ) :
    W (delta n) j y = if (n : ℝ) ≤ y then (y - n) ^ j else 0 := by
  unfold W delta
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  have hiff : n ∈ Finset.Icc 1 ⌊y⌋₊ ↔ (n : ℝ) ≤ y := by
    rw [Finset.mem_Icc]
    constructor
    · rintro ⟨-, h2⟩
      have hy0 : 0 ≤ y := by
        by_contra h; push Not at h
        have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
        omega
      exact (Nat.cast_le.2 h2).trans (Nat.floor_le hy0)
    · intro h; exact ⟨hn, Nat.le_floor h⟩
  by_cases h : (n : ℝ) ≤ y
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-- `W_r(y) = ∑_{n ≤ M} aₙ W(δ_n)_r(y)` once `⌊y⌋ ≤ M`. -/
lemma WC_eq_sum_delta (a : ℕ → ℂ) (r : ℕ) {M : ℕ} {y : ℝ} (hy : ⌊y⌋₊ ≤ M) :
    WC a r y = ∑ n ∈ Finset.Icc 1 M, a n * ((W (delta n) r y : ℝ) : ℂ) := by
  unfold WC
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl hy
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.1 hn).1
    have h1 := (Finset.mem_Icc.1 hn).2
    have hy0 : 0 ≤ y := by
      by_contra h; push Not at h
      have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      omega
    have : (n : ℝ) ≤ y := (Nat.cast_le.2 h1).trans (Nat.floor_le hy0)
    rw [W_delta n hn1, if_pos this]
    push_cast; ring
  · intro n hn hn'
    have hn1 := (Finset.mem_Icc.1 hn).1
    rw [W_delta n hn1, if_neg, Complex.ofReal_zero, mul_zero]
    intro h0
    exact hn' (Finset.mem_Icc.2 ⟨hn1, Nat.le_floor h0⟩)

lemma DkC_sum_real (h : ℝ) (r : ℕ) : ∀ (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℝ → ℝ) (x : ℝ),
    DkC h r (fun y => ∑ n ∈ S, a n * ((g n y : ℝ) : ℂ)) x =
      ∑ n ∈ S, a n * ((Dk h r (g n) x : ℝ) : ℂ) := by
  induction r with
  | zero => intro S a g x; rfl
  | succ r ih =>
    intro S a g x
    simp only [DkC, Dk]
    rw [← ih S a (fun n y => g n (y + h) - g n y) x]
    congr 1; funext y
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring

/-- **The signed bracket**:
`‖r! h^r A(x) − Δ_h^r W_r(x)‖ ≤ r! h^r ∑_{x<n≤x+rh} ‖aₙ‖`. -/
theorem bracket_signed (a : ℕ → ℂ) (r : ℕ) {h : ℝ} (hh : 0 ≤ h) {x : ℝ} (hx : 0 ≤ x) :
    ‖((Nat.factorial r : ℝ) * h ^ r : ℂ) * TauPartialSums.A a x - DkC h r (WC a r) x‖ ≤
      (Nat.factorial r : ℝ) * h ^ r *
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + r * h⌋₊, ‖a n‖ := by
  set M : ℕ := ⌊x + r * h⌋₊ with hM
  set N : ℕ := ⌊x⌋₊ with hN
  have hrh : 0 ≤ (r : ℝ) * h := by positivity
  have hNM : N ≤ M := Nat.floor_le_floor (by linarith)
  -- the representation on `[x, x + rh]`
  have hrep : ∀ y ∈ Icc x (x + r * h), WC a r y =
      ∑ n ∈ Finset.Icc 1 M, a n * ((W (delta n) r y : ℝ) : ℂ) :=
    fun y hy => WC_eq_sum_delta a r (Nat.floor_le_floor hy.2)
  rw [DkC_congr_on h hh r _ _ x hrep, DkC_sum_real]
  set F : ℝ := (Nat.factorial r : ℝ) * h ^ r with hF
  have hF0 : 0 ≤ F := by positivity
  -- each term
  have hb : ∀ n, 1 ≤ n →
      F * W (delta n) 0 x ≤ Dk h r (W (delta n) r) x ∧
        Dk h r (W (delta n) r) x ≤ F * W (delta n) 0 (x + r * h) := fun n _ =>
    bracket (W (delta n)) (fun j u v => (W_mono _ (delta_nonneg n) j).intervalIntegrable)
      (W_mono _ (delta_nonneg n) 0) hh (fun j y => W_rel (delta n) j hh y) r x
  have hlow : ∀ n ∈ Finset.Icc 1 N, Dk h r (W (delta n) r) x = F := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2).trans (Nat.floor_le hx)
    have h1 := hb n hn1
    rw [W_delta n hn1, if_pos hnx, W_delta n hn1, if_pos (by linarith)] at h1
    simp only [pow_zero, mul_one] at h1
    exact le_antisymm h1.2 h1.1
  have hmid : ∀ n ∈ Finset.Ioc N M, |Dk h r (W (delta n) r) x| ≤ F := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.1 hn).1; omega
    have h1 := hb n hn1
    have w0 : ∀ y, 0 ≤ W (delta n) 0 y ∧ W (delta n) 0 y ≤ 1 := by
      intro y; rw [W_delta n hn1]; split_ifs <;> norm_num
    have l1 : 0 ≤ F * W (delta n) 0 x := mul_nonneg hF0 (w0 x).1
    have l2 : F * W (delta n) 0 (x + r * h) ≤ F := by
      have := (w0 (x + r * h)).2; nlinarith
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
  -- split the sum
  have hsplit : ∑ n ∈ Finset.Icc 1 M, a n * ((Dk h r (W (delta n) r) x : ℝ) : ℂ) =
      (F : ℂ) * TauPartialSums.A a x +
        ∑ n ∈ Finset.Ioc N M, a n * ((Dk h r (W (delta n) r) x : ℝ) : ℂ) := by
    rw [TauPartialSums.Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNM]
    congr 1
    unfold TauPartialSums.A
    rw [← hN, TauPartialSums.Icc_one_eq_Ioc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← TauPartialSums.Icc_one_eq_Ioc] at hn
    rw [hlow n hn]; ring
  rw [hsplit]
  have hFc : ((Nat.factorial r : ℝ) * h ^ r : ℂ) = (F : ℂ) := by rw [hF]; push_cast; ring
  rw [hFc, sub_add_cancel_left, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hmid n hn) (norm_nonneg _)

/-! ### Landau's inequality -/

/-- The scaled kernel family `y ↦ J_j(n y)/n^j`. -/
lemma scaled_rel (J : ℕ → ℝ → ℂ) (r : ℕ)
    (hrel : ∀ j, j < r → ∀ u, 0 < u → ∀ v, 0 ≤ v →
      J (j + 1) (u + v) - J (j + 1) u = ((j : ℂ) + 1) * ∫ w in (0 : ℝ)..v, J j (u + w))
    {n : ℕ} (hn : 1 ≤ n) {h : ℝ} (hh : 0 ≤ h) :
    ∀ j, j < r → ∀ y, 0 < y →
      (fun j (y : ℝ) => J j (n * y) / (n : ℂ) ^ j) (j + 1) (y + h) -
        (fun j (y : ℝ) => J j (n * y) / (n : ℂ) ^ j) (j + 1) y =
      ((j : ℂ) + 1) * ∫ s in (0 : ℝ)..h, (fun j (y : ℝ) => J j (n * y) / (n : ℂ) ^ j) j (y + s) := by
  intro j hj y hy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  simp only
  have h1 := hrel j hj (n * y) (by positivity) (n * h) (by positivity)
  rw [show (n : ℝ) * (y + h) = n * y + n * h by ring, ← sub_div, h1]
  have hsub : ∫ w in (0 : ℝ)..((n : ℝ) * h), J j (n * y + w) =
      (n : ℂ) * ∫ s in (0 : ℝ)..h, J j (n * (y + s)) := by
    have := intervalIntegral.integral_comp_mul_left (fun w => J j (n * y + w)) (a := 0) (b := h)
      hn0.ne'
    simp only [mul_zero] at this
    rw [show (fun s => J j (n * (y + s))) = fun s => J j (n * y + n * s) by
      funext s; ring_nf]
    rw [this, Complex.real_smul]
    push_cast
    field_simp
  rw [hsub, intervalIntegral.integral_div, pow_succ]
  field_simp

/-- **Landau's inequality** (abstract, complex). -/
theorem landau_ineq (a : ℕ → ℂ) (ha0 : a 0 = 0) (r k : ℕ) (J : ℕ → ℝ → ℂ) (cst : ℂ)
    (hcont : ∀ j, ContinuousOn (J j) (Ioi 0))
    (hrel : ∀ j, j < r → ∀ u, 0 < u → ∀ v, 0 ≤ v →
      J (j + 1) (u + v) - J (j + 1) u = ((j : ℂ) + 1) * ∫ w in (0 : ℝ)..v, J j (u + w))
    (hrep : ∀ y, 1 ≤ y → WC a r y = cst * ∑' n : ℕ, a n / (n : ℂ) ^ (k + r) * J r (n * y))
    {A₀ β₀ βr γ : ℝ} (hA0 : 0 ≤ A₀) (hβ0 : 0 ≤ β₀) (hβr : 0 ≤ βr)
    (hbot : ∀ y, 1 ≤ y → ‖J 0 y‖ ≤ A₀ * y ^ β₀)
    (htop : ∀ y, 1 ≤ y → ‖J r y‖ ≤ A₀ * y ^ βr)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-γ))
    (hγ0 : 0 ≤ β₀ - k + γ) (hγr : βr - k - r + γ ≤ 0)
    {x h M : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hM : 1 ≤ M) :
    ‖TauPartialSums.A a x‖ ≤
      ‖cst‖ * (∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-γ)) * A₀ *
        ((x + r * h) ^ β₀ * M ^ (β₀ - k + γ) +
          2 ^ r / ((Nat.factorial r : ℝ) * h ^ r) * (x + r * h) ^ βr * M ^ (βr - k - r + γ)) +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + r * h⌋₊, ‖a n‖ := by
  set L : ℝ := ∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-γ) with hL
  set F : ℝ := (Nat.factorial r : ℝ) * h ^ r with hF
  have hF0 : 0 < F := by positivity
  have hx0 : 0 < x := by linarith
  have hrh : 0 ≤ (r : ℝ) * h := by positivity
  set X : ℝ := x + r * h with hX
  have hX1 : 1 ≤ X := by linarith
  set T1 : ℝ := F * A₀ * X ^ β₀ * M ^ (β₀ - k + γ) with hT1
  set T2 : ℝ := 2 ^ r * A₀ * X ^ βr * M ^ (βr - k - r + γ) with hT2
  have hT1n : 0 ≤ T1 := by positivity
  have hT2n : 0 ≤ T2 := by positivity
  -- the dual side of `Δ^r W_r`
  have hsumJ : ∀ y, 1 ≤ y → Summable fun n : ℕ => a n / (n : ℂ) ^ (k + r) * J r (n * y) := by
    intro y hy
    refine Summable.of_norm_bounded ((hsum.mul_right (A₀ * y ^ βr))) (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hJ := htop (n * y) (by nlinarith)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast,
        Real.mul_rpow hn0.le (by linarith)] at *
      have hpow : (n : ℝ) ^ βr / (n : ℝ) ^ (k + r) ≤ (n : ℝ) ^ (-γ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hn0]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
      calc ‖a n‖ / (n : ℝ) ^ (k + r) * ‖J r (n * y)‖ ≤
          ‖a n‖ / (n : ℝ) ^ (k + r) * (A₀ * ((n : ℝ) ^ βr * y ^ βr)) := by gcongr
        _ = ‖a n‖ * ((n : ℝ) ^ βr / (n : ℝ) ^ (k + r)) * (A₀ * y ^ βr) := by ring
        _ ≤ ‖a n‖ * (n : ℝ) ^ (-γ) * (A₀ * y ^ βr) := by gcongr
  have hDW : DkC h r (WC a r) x =
      cst * ∑' n : ℕ, a n / (n : ℂ) ^ (k + r) * DkC h r (fun y => J r (n * y)) x := by
    have hc : ∀ y ∈ Icc x (x + r * h), WC a r y =
        cst * ∑' n : ℕ, a n / (n : ℂ) ^ (k + r) * J r (n * y) :=
      fun y hy => hrep y (by linarith [hy.1])
    rw [DkC_congr_on h hh.le r _ _ x hc, DkC_const_mul,
      DkC_tsum_on h hh.le r _ x (fun y hy => hsumJ y (by linarith [hy.1]))]
    congr 1
    refine tsum_congr fun n => ?_
    exact DkC_const_mul h r _ _ x
  -- termwise bound
  have hterm : ∀ n : ℕ, ‖a n / (n : ℂ) ^ (k + r) * DkC h r (fun y => J r (n * y)) x‖ ≤
      ‖a n‖ * (n : ℝ) ^ (-γ) * (T1 + T2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hγn : 0 ≤ ‖a n‖ * (n : ℝ) ^ (-γ) := by positivity
    rcases le_or_gt (n : ℝ) M with hnM | hnM
    · -- head: down to `J_0`
      set G : ℕ → ℝ → ℂ := fun j y => J j (n * y) / (n : ℂ) ^ j with hG
      have hGc : ∀ j, ContinuousOn (G j) (Ioi 0) := by
        intro j
        refine ((hcont j).comp (continuous_const.mul continuous_id).continuousOn
          (fun y hy => ?_)).div_const _
        simp only [Set.mem_Ioi] at hy ⊢; exact mul_pos hn0 hy
      have hb := DkC_family_bound G r hh.le hGc (scaled_rel J r hrel hn hh.le)
        (B := A₀ * ((n : ℝ) * X) ^ β₀) r le_rfl x hx0 (fun y hy => by
          simp only [hG, pow_zero, div_one]
          refine (hbot (n * y) (by nlinarith [hy.1])).trans ?_
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hn0.le (by linarith [hy.1]))
            (mul_le_mul_of_nonneg_left hy.2 hn0.le) hβ0) hA0)
      have hGr : DkC h r (fun y => J r (n * y)) x = (n : ℂ) ^ r * DkC h r (G r) x := by
        rw [← DkC_const_mul]
        congr 1; funext y; simp only [hG]; field_simp
      rw [hGr, norm_mul, norm_pow, Complex.norm_natCast]
      have hpow : (n : ℝ) ^ r * (n : ℝ) ^ β₀ / (n : ℝ) ^ (k + r) ≤
          (n : ℝ) ^ (-γ) * M ^ (β₀ - k + γ) := by
        have e : (n : ℝ) ^ r * (n : ℝ) ^ β₀ / (n : ℝ) ^ (k + r) =
            (n : ℝ) ^ (-γ) * (n : ℝ) ^ (β₀ - k + γ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hn0,
            ← Real.rpow_sub hn0, ← Real.rpow_add hn0]
          congr 1; push_cast; ring
        rw [e]
        gcongr
      calc ‖a n‖ / (n : ℝ) ^ (k + r) * ((n : ℝ) ^ r * ‖DkC h r (G r) x‖)
          ≤ ‖a n‖ / (n : ℝ) ^ (k + r) * ((n : ℝ) ^ r * (F * (A₀ * ((n : ℝ) * X) ^ β₀))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity))
              (by positivity)
        _ = ‖a n‖ * ((n : ℝ) ^ r * (n : ℝ) ^ β₀ / (n : ℝ) ^ (k + r)) * (F * A₀ * X ^ β₀) := by
            rw [Real.mul_rpow hn0.le (by linarith)]; ring
        _ ≤ ‖a n‖ * ((n : ℝ) ^ (-γ) * M ^ (β₀ - k + γ)) * (F * A₀ * X ^ β₀) := by
            gcongr
        _ = ‖a n‖ * (n : ℝ) ^ (-γ) * T1 := by rw [hT1]; ring
        _ ≤ ‖a n‖ * (n : ℝ) ^ (-γ) * (T1 + T2) := by gcongr; linarith
    · -- tail: the top kernel
      have hb := norm_DkC_le h hh.le r (fun y => J r (n * y)) x (A₀ * ((n : ℝ) * X) ^ βr)
        (fun y hy => by
          refine (htop (n * y) (by nlinarith [hy.1])).trans ?_
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hn0.le (by linarith [hy.1]))
            (mul_le_mul_of_nonneg_left hy.2 hn0.le) hβr) hA0)
      have hpow : (n : ℝ) ^ βr / (n : ℝ) ^ (k + r) ≤ (n : ℝ) ^ (-γ) * M ^ (βr - k - r + γ) := by
        have e : (n : ℝ) ^ βr / (n : ℝ) ^ (k + r) =
            (n : ℝ) ^ (-γ) * (n : ℝ) ^ (βr - k - r + γ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_sub hn0, ← Real.rpow_add hn0]
          congr 1; push_cast; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hnM.le hγr)
          (by positivity)
      calc ‖a n‖ / (n : ℝ) ^ (k + r) * ‖DkC h r (fun y => J r (n * y)) x‖
          ≤ ‖a n‖ / (n : ℝ) ^ (k + r) * (2 ^ r * (A₀ * ((n : ℝ) * X) ^ βr)) := by gcongr
        _ = ‖a n‖ * ((n : ℝ) ^ βr / (n : ℝ) ^ (k + r)) * (2 ^ r * A₀ * X ^ βr) := by
            rw [Real.mul_rpow hn0.le (by linarith)]; ring
        _ ≤ ‖a n‖ * ((n : ℝ) ^ (-γ) * M ^ (βr - k - r + γ)) * (2 ^ r * A₀ * X ^ βr) := by
            gcongr
        _ = ‖a n‖ * (n : ℝ) ^ (-γ) * T2 := by rw [hT2]; ring
        _ ≤ ‖a n‖ * (n : ℝ) ^ (-γ) * (T1 + T2) := by gcongr; linarith
  have hS : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-γ) * (T1 + T2) := hsum.mul_right _
  have hdual : ‖DkC h r (WC a r) x‖ ≤ ‖cst‖ * (L * (T1 + T2)) := by
    rw [hDW, norm_mul]
    gcongr
    refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded hS hterm |>.norm)).trans ?_
    rw [hL, ← tsum_mul_right]
    exact (Summable.of_norm_bounded hS hterm).norm.tsum_le_tsum hterm hS
  have hbr := bracket_signed a r hh.le hx0.le
  set S : ℝ := ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + r * h⌋₊, ‖a n‖ with hSdef
  have hFA : F * ‖TauPartialSums.A a x‖ ≤ ‖cst‖ * (L * (T1 + T2)) + F * S := by
    have e : ‖((Nat.factorial r : ℝ) * h ^ r : ℂ) * TauPartialSums.A a x‖ =
        F * ‖TauPartialSums.A a x‖ := by
      rw [norm_mul, hF]; congr 1
      rw [show ((Nat.factorial r : ℝ) * h ^ r : ℂ) = (((Nat.factorial r : ℝ) * h ^ r : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have := norm_le_insert' (((Nat.factorial r : ℝ) * h ^ r : ℂ) * TauPartialSums.A a x)
      (DkC h r (WC a r) x)
    rw [e] at this
    linarith
  have hL0 : 0 ≤ L := tsum_nonneg fun n => by positivity
  have hfin : ‖TauPartialSums.A a x‖ ≤ ‖cst‖ * (L * (T1 + T2)) / F + S := by
    rw [div_add' _ _ _ hF0.ne', le_div_iff₀ hF0]; linarith
  refine hfin.trans (le_of_eq ?_)
  rw [hT1, hT2]
  field_simp

end RamanujanTau.TauPartialSumsSharp
