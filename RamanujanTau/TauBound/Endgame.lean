/-
# Sub-Hecke bound for τ: the conditional endgame

Two named analytic/arithmetic inputs:

* `KloostermanBound α`: `|S(1,n;c)| ≤ A c^α` uniformly in `n` (trivial for `α = 1`; Kloosterman 1927:
  any `α > 3/4`; Weil: any `α > 1/2`);
* `PoincareFormula`: the unfolded Fourier expansion of the weight-12 Poincaré series `P₁`,
  together with `P₁ = λ Δ`, `λ ≠ 0`:
  `λ τ(n) = [n = 1] + ∑_{c ≥ 1} c^{-12} S(1,n;c) K(n,c;1/n)`.

Conclusion (`tau_bound_of_kloosterman`): if `0 ≤ r`, `0 ≤ α`, `α + 2r < 11`, then `τ(n) = O(n^{11-r})`.
With `α = 3/4 + δ` this is `τ(n) = O(n^{47/8 + ε})` (Kloosterman's exponent `6 - 1/8`).
-/
import RamanujanTau.TauBound.Basic
import RamanujanTau.Basic
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex Filter Asymptotics
open scoped Real

/-- Kloosterman-type bound `|S(1,n;c)| ≤ A c^α`, uniform in `n`. -/
def KloostermanBound (α : ℝ) : Prop :=
  ∃ A : ℝ, ∀ (n : ℤ) (c : ℕ), 1 ≤ c → ‖kloosterman 1 n c‖ ≤ A * (c : ℝ) ^ α

/-- The Petersson/Poincaré exact formula for `τ`:
`P₁ = λ Δ` with `λ ≠ 0`, and the `n`-th coefficient of `P₁` is
`[n = 1] + ∑_{c ≥ 1} c^{-12} S(1,n;c) K(n,c;1/n)`. -/
def PoincareFormula : Prop :=
  ∃ lam : ℂ, lam ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n →
    HasSum (fun c : ℕ => ((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 n (c + 1) *
        kInt n (c + 1) (1 / n))
      (lam * (tau n : ℂ) - if n = 1 then 1 else 0)

/-- The trivial Kloosterman bound. -/
theorem kloostermanBound_one : KloostermanBound 1 :=
  ⟨1, fun n c _ => by simpa using norm_kloosterman_le 1 n c⟩

/-- `B_r = M_r e^{2π} (2π)^{-r} J_r`. -/
noncomputable def kConst (r : ℝ) : ℝ :=
  expConst r * Real.exp (2 * π) * (2 * π) ^ (-r) * jConst r

lemma kConst_nonneg (r : ℝ) : 0 ≤ kConst r := by
  unfold kConst
  have := expConst_pos r
  have := jConst_nonneg r
  positivity

lemma rpow_algebra (r N C : ℝ) (hN : 0 < N) (hC : 0 < C) :
    (2 * π * (1 / N) / C ^ 2) ^ (-r) * (((1 / N) ^ 2) ^ (r - 6) * (1 / N)) =
      (2 * π) ^ (-r) * (N ^ (11 - r) * C ^ (2 * r)) := by
  have h2 : 0 < 2 * π := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.rpow_def_of_pos h2, Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hC,
    show (1 / N) = Real.exp (-Real.log N) by rw [Real.exp_neg, Real.exp_log hN, one_div]]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp]
  push_cast
  ring

/-- `‖K(n,c;1/n)‖ ≤ B_r n^{11-r} c^{2r}`. -/
theorem norm_kInt_inv_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 11 / 2) (n c : ℕ) (hn : 1 ≤ n)
    (hc : c ≠ 0) :
    ‖kInt n c (1 / n)‖ ≤ kConst r * ((n : ℝ) ^ (11 - r) * (c : ℝ) ^ (2 * r)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  refine (norm_kInt_le hr0 hr n c hc (y := 1 / n) (by positivity)).trans (le_of_eq ?_)
  have he : Real.exp (2 * π * n * (1 / n)) = Real.exp (2 * π) := by
    congr 1; field_simp
  rw [he, kConst]
  have := rpow_algebra r n c hN hC
  calc expConst r * Real.exp (2 * π) * (2 * π * (1 / ↑n) / ↑c ^ 2) ^ (-r) *
        (((1 / ↑n) ^ 2) ^ (r - 6) * (1 / ↑n) * jConst r)
      = expConst r * Real.exp (2 * π) * jConst r * ((2 * π * (1 / ↑n) / ↑c ^ 2) ^ (-r) *
        (((1 / ↑n) ^ 2) ^ (r - 6) * (1 / ↑n))) := by ring
    _ = _ := by rw [this]; ring

/-- **Conditional sub-Hecke bound.** Under `KloostermanBound α` and `PoincareFormula`, for every
`0 ≤ r` with `α + 2r < 11` (and `0 ≤ α`): `|τ(n)| ≤ C n^{11-r}` for all `n ≥ 1`. -/
theorem tau_bound_of_kloosterman {α r : ℝ} (hα : 0 ≤ α) (hr0 : 0 ≤ r) (hαr : α + 2 * r < 11)
    (hK : KloostermanBound α) (hP : PoincareFormula) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(tau n : ℝ)| ≤ C * (n : ℝ) ^ (11 - r) := by
  have hr : r < 11 / 2 := by linarith
  obtain ⟨lam, hlam, hform⟩ := hP
  obtain ⟨A, hA⟩ := hK
  set A' := |A|
  set β := α + 2 * r - 12 with hβ
  have hβ1 : β < -1 := by rw [hβ]; linarith
  have hsum : Summable (fun c : ℕ => ((c + 1 : ℕ) : ℝ) ^ β) := by
    have := (Real.summable_nat_rpow.mpr hβ1)
    exact (summable_nat_add_iff 1).mpr this |>.congr fun c => by push_cast; rfl
  set Z := ∑' c : ℕ, ((c + 1 : ℕ) : ℝ) ^ β
  have hZ : 0 ≤ Z := tsum_nonneg fun c => Real.rpow_nonneg (by positivity) _
  have hlam' : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  refine ⟨(1 + A' * kConst r * Z) / ‖lam‖, fun n hn => ?_⟩
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by linarith
  have hpow : 1 ≤ (n : ℝ) ^ (11 - r) := Real.one_le_rpow hN (by linarith)
  -- termwise bound
  have hterm : ∀ c : ℕ, ‖((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 n (c + 1) *
      kInt n (c + 1) (1 / n)‖ ≤
      (A' * kConst r * (n : ℝ) ^ (11 - r)) * ((c + 1 : ℕ) : ℝ) ^ β := by
    intro c
    have hC : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
    have h1 : ‖((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ)‖ = ((c + 1 : ℕ) : ℝ) ^ (-12 : ℝ) := by
      rw [norm_zpow, Complex.norm_natCast, ← Real.rpow_intCast]; norm_num
    have h2 : ‖kloosterman 1 n (c + 1)‖ ≤ A' * ((c + 1 : ℕ) : ℝ) ^ α :=
      (hA n (c + 1) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg hC.le _))
    have h3 := norm_kInt_inv_le hr0 hr n (c + 1) hn (by omega)
    rw [norm_mul, norm_mul, h1]
    have hk : 0 ≤ kConst r := kConst_nonneg r
    calc ((c + 1 : ℕ) : ℝ) ^ (-12 : ℝ) * ‖kloosterman 1 n (c + 1)‖ * ‖kInt n (c + 1) (1 / n)‖
        ≤ ((c + 1 : ℕ) : ℝ) ^ (-12 : ℝ) * (A' * ((c + 1 : ℕ) : ℝ) ^ α) *
            (kConst r * ((n : ℝ) ^ (11 - r) * ((c + 1 : ℕ) : ℝ) ^ (2 * r))) := by
          gcongr
      _ = (A' * kConst r * (n : ℝ) ^ (11 - r)) * (((c + 1 : ℕ) : ℝ) ^ (-12 : ℝ) *
            ((c + 1 : ℕ) : ℝ) ^ α * ((c + 1 : ℕ) : ℝ) ^ (2 * r)) := by ring
      _ = _ := by
          rw [← Real.rpow_add hC, ← Real.rpow_add hC, hβ]; ring_nf
  have hle := (hform n hn).norm_le_of_bounded (hsum.hasSum.mul_left
    (A' * kConst r * (n : ℝ) ^ (11 - r))) hterm
  -- |λ| |τ n| ≤ 1 + A' B n^{11-r} Z
  have hδ : ‖(if n = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have hmain : ‖lam * (tau n : ℂ)‖ ≤ 1 + A' * kConst r * (n : ℝ) ^ (11 - r) * Z := by
    have := norm_add_le (lam * (tau n : ℂ) - if n = 1 then 1 else 0) (if n = 1 then 1 else 0)
    rw [sub_add_cancel] at this
    linarith
  rw [norm_mul] at hmain
  have htau : ‖(tau n : ℂ)‖ = |(tau n : ℝ)| := by
    rw [← Complex.norm_intCast]
  rw [htau] at hmain
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam']
  have hA'0 : 0 ≤ A' * kConst r * Z := by
    have := kConst_nonneg r; positivity
  nlinarith [abs_nonneg ((tau n : ℝ))]

/-- `IsBigO` form of the conditional bound. -/
theorem tau_isBigO_of_kloosterman {α r : ℝ} (hα : 0 ≤ α) (hr0 : 0 ≤ r) (hαr : α + 2 * r < 11)
    (hK : KloostermanBound α) (hP : PoincareFormula) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (11 - r) := by
  obtain ⟨C, hC⟩ := tau_bound_of_kloosterman hα hr0 hαr hK hP
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact hC n hn

/-- **Kloosterman's exponent, conditionally.** If `KloostermanBound (3/4 + δ)` holds for every
`δ > 0`, then `τ(n) = O(n^{47/8 + ε})` for every `ε > 0`. -/
theorem tau_isBigO_47_8 (hK : ∀ δ : ℝ, 0 < δ → KloostermanBound (3 / 4 + δ))
    (hP : PoincareFormula) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) := by
  -- take δ = ε, r = 41/8 - ε (if ε < 41/8), so α + 2r = 3/4 + ε + 41/4 - 2ε < 11
  rcases lt_or_ge ε (41 / 8) with h | h
  · have := tau_isBigO_of_kloosterman (α := 3 / 4 + ε) (r := 41 / 8 - ε) (by linarith)
      (by linarith) (by linarith) (hK ε hε) hP
    refine this.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · have := tau_isBigO_of_kloosterman (α := 1) (r := 0) (by norm_num) le_rfl (by norm_num)
      kloostermanBound_one hP
    refine this.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end RamanujanTau.TauBound
