/-
# The Andrews–Dragonette series: convergence from a named Kloosterman-cancellation hypothesis

Andrews–Dragonette (conjectured by Andrews 1966; proved by Bringmann–Ono 2006):

  `α(n) = Σ_{k ≥ 1} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4) M_{2k}(n)`,
  `M_{2k}(n) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k`  (`Andrews66.MK_two`).

The partial sums are `adPartial n N`; Andrews' printed sum is `adPartial n ⌊√n⌋` (`andrewsPrinted_eq_adPartial`).

Since `I_{1/2}(x) ≍ √x` as `x → 0`, the `k`-th term is `≍ A_{2k}(·)/k^{3/2}`. The trivial bound `|A_{2k}| ≤ 2k`
gives terms `O(k^{−1/2})`, and even Weil's bound gives only `O(k^{−1+ε})`: the series is **not** absolutely
convergent (Ahlgren–Dunn 2019, Thm 1.2), and its convergence is a statement about cancellation in sums of
Kloosterman sums over the modulus. The precise input is the named hypothesis

  `HKS n θ C :  ‖Σ_{k ≤ X} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)/k‖ ≤ C X^θ`  for all `X ≥ 1`,

and we prove (`adPartial_converges_of_HKS`): **`HKS n θ C` with `θ < 1/2` ⇒ the partial sums converge.**
`HKS n 1 2` holds trivially (`HKS_trivial`); Weil would give every `θ > 1/2`; the needed `θ < 1/2` is
beyond square-root cancellation in the modulus aspect (Kuznetsov / Goldfeld–Sarnak type; Ahlgren–Dunn Thm 7.1
gives `X^{1/2−δ+ε}` for their normalization of these sums).

What this file does NOT prove: that the limit equals `α(n)` (see `docs/ANDREWS_DRAGONETTE_EXACT.md`).
-/
import RamanujanTau.Andrews66.Printed
import RamanujanTau.AndrewsDragonette.Abel
import RamanujanTau.AndrewsDragonette.Weight

set_option autoImplicit false

namespace AndrewsDragonette
open Filter Topology Finset Andrews66 Complex
open scoped Real

noncomputable section

/-- The Kloosterman coefficient `(−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)`. -/
def adCoef (n k : ℕ) : ℂ := (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n)

/-- The `k`-th term of the Andrews–Dragonette series. -/
def adTerm (n k : ℕ) : ℂ := adCoef n k * (MK (2 * k) n : ℂ)

/-- Partial sums `Σ_{k=1}^{N}` of the Andrews–Dragonette series. -/
def adPartial (n N : ℕ) : ℂ := ∑ k ∈ Icc 1 N, adTerm n k

theorem andrewsPrinted_eq_adPartial (n : ℕ) : andrewsPrinted n = adPartial n (Nat.sqrt n) := rfl

/-- The normalized Kloosterman partial sum `Σ_{k ≤ X} adCoef n k / k`. -/
def KSum (n X : ℕ) : ℂ := ∑ k ∈ Icc 1 X, adCoef n k / k

/-- **Named hypothesis (Kloosterman cancellation in the modulus aspect).** -/
def HKS (n : ℕ) (θ C : ℝ) : Prop := ∀ X : ℕ, 1 ≤ X → ‖KSum n X‖ ≤ C * (X : ℝ) ^ θ

lemma norm_adCoef_le (n k : ℕ) : ‖adCoef n k‖ ≤ 2 * k := by
  unfold adCoef
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := norm_AAnd_le (2 * k) (shiftA k n)
  push_cast at this
  exact this

theorem KSum_trivial (n X : ℕ) : ‖KSum n X‖ ≤ 2 * X := by
  unfold KSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Icc 1 X, ‖adCoef n k / k‖ ≤ ∑ _k ∈ Icc 1 X, (2 : ℝ) := by
        refine sum_le_sum (fun k hk => ?_)
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
        exact norm_adCoef_le n k
    _ = 2 * X := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

/-- The trivial instance: `HKS n 1 2`. The convergence theorem needs exponent `< 1/2`. -/
theorem HKS_trivial (n : ℕ) : HKS n 1 2 := fun X _ => by simpa using KSum_trivial n X

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- `A = √24/√(24n−1)`, `B = π√(24n−1)/12`. -/
def wA (n : ℕ) : ℝ := √24 / √(24 * (n : ℝ) - 1)
def wB (n : ℕ) : ℝ := π * √(24 * (n : ℝ) - 1) / 12

lemma k_MK (n k : ℕ) (hk : 0 < k) : (k : ℝ) * MK (2 * k) n = wt (wA n) (wB n) k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk'
  have e : (k : ℝ) = √k * √k := (Real.mul_self_sqrt hk'.le).symm
  rw [MK_two, wt, wA, wB, div_div]
  have h2 : (k : ℝ) * (√24 / (√k * √(24 * (n : ℝ) - 1))) = √24 / √(24 * (n : ℝ) - 1) * √k := by
    nth_rewrite 1 [e]
    field_simp
  rw [← mul_assoc, h2]

/-- **Convergence of the Andrews–Dragonette series under `HKS` with `θ < 1/2`** (fixed `n`, `N → ∞`). -/
theorem adPartial_converges_of_HKS {n : ℕ} (hn : 1 ≤ n) {θ C : ℝ} (hθ : θ < 1 / 2)
    (hK : HKS n θ C) : ∃ L : ℂ, Tendsto (fun N => adPartial n N) atTop (𝓝 L) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 0 ≤ wA n := by unfold wA; positivity
  have hB : 0 ≤ wB n := by unfold wB; positivity
  have hC : 0 ≤ C := by
    have := hK 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set G := wA n * wB n * Real.cosh (wB n) with hG
  have hG0 : 0 ≤ G := by have := Real.cosh_pos (wB n); positivity
  set c : ℕ → ℂ := fun j => adCoef n (j + 1) / ((j + 1 : ℕ) : ℂ) with hc
  set g : ℕ → ℝ := fun j => wt (wA n) (wB n) ((j : ℝ) + 1) with hg
  have hS : ∀ N, ∑ j ∈ range N, c j = KSum n N := fun N => by
    rw [KSum, sum_Icc_eq_range]
  have hT : ∀ N, ∑ j ∈ range N, c j * g j = adPartial n N := fun N => by
    rw [adPartial, sum_Icc_eq_range]
    refine sum_congr rfl (fun j _ => ?_)
    have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have := k_MK n (j + 1) (Nat.succ_pos j)
    simp only [hc, hg, adTerm]
    rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, ← this]
    push_cast
    have hj' : ((j : ℂ) + 1) ≠ 0 := by
      have : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      simpa using this
    field_simp
  -- summability of the Abel remainder
  have h1 : Summable (fun k => ‖∑ j ∈ range (k + 1), c j‖ * |g (k + 1) - g k|) := by
    have hsum : Summable (fun k : ℕ => C * (2 * G) * ((k : ℝ) + 1) ^ (θ - 3 / 2)) := by
      have h0 : Summable (fun k : ℕ => ((k : ℝ)) ^ (θ - 3 / 2)) :=
        Real.summable_nat_rpow.mpr (by linarith)
      have h1 := (summable_nat_add_iff 1).mpr h0
      refine (h1.congr (fun k => ?_)).mul_left _
      push_cast; rfl
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hx0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    rw [hS]
    have e1 := hK (k + 1) (by omega)
    have e2 := w_sub_le hA hB hx
    have hgk : g (k + 1) = wt (wA n) (wB n) (((k : ℝ) + 1) + 1) := by
      simp only [hg]; push_cast; ring_nf
    rw [hgk]
    have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [this] at e1
    calc ‖KSum n (k + 1)‖ * |wt (wA n) (wB n) ((k : ℝ) + 1 + 1) - g k|
        ≤ (C * ((k : ℝ) + 1) ^ θ) * (2 * G * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = C * (2 * G) * ((k : ℝ) + 1) ^ (θ - 3 / 2) := by
          rw [show θ - 3 / 2 = θ + (-(3 / 2 : ℝ)) by ring, Real.rpow_add hx0]; ring
  -- the boundary term
  have h2 : Tendsto (fun N => (∑ k ∈ range N, c k) * (g N : ℂ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => C * G * (N : ℝ) ^ (θ - 1 / 2)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < 1 / 2 - θ by linarith)).comp
        tendsto_natCast_atTop_atTop
      have := this.const_mul (C * G)
      rw [mul_zero] at this
      refine this.congr (fun N => ?_)
      simp only [Function.comp, neg_sub]
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    rw [hS, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e1 := hK N hN
    have e2 := w_le hA hB (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith)
    have e3 : ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by norm_num)
    calc ‖KSum n N‖ * |g N| ≤ (C * (N : ℝ) ^ θ) * (G * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
          refine mul_le_mul e1 (e2.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left e3 hG0
      _ = C * G * (N : ℝ) ^ (θ - 1 / 2) := by
          rw [show θ - 1 / 2 = θ + (-(1 / 2 : ℝ)) by ring, Real.rpow_add hN0]; ring
  obtain ⟨L, hL⟩ := tendsto_of_abel c g h1 h2
  exact ⟨L, hL.congr hT⟩

end

end AndrewsDragonette
