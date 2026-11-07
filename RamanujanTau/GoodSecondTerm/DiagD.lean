/-
# The Δ diagonal: `Σ_n a(n)²/n · V(2 log n − L) = c₀ L + 2γ_Δ + O((1+|L|) e^{−L/10})`

`a(n)² = τ(n)²/n¹¹`. From Rankin's `S(N) = Σ_{n≤N} a(n)² = c₀N + E(N)`, `|E(N)| ≤ C N^{3/5}`
(`CriticalMeanSquareAsymp.rankin_normalization`), summation by parts gives

    A(N) = Σ_{n≤N} a(n)²/n = c₀ H_N + E(N)/N + Σ_{n<N} E(n)/(n(n+1)),

so `A(N) = c₀ log N + γ_Δ + O(N^{−1/5})` with `γ_Δ = c₀γ + Σ_{n≥1} E(n)/(n(n+1))` (`gammaD`).
Numerically `γ_Δ = 0.796028…` equals the Laurent constant of `Σ a(n)²n^{−s}` at `s = 1`
(`scripts/good_second_term/constants.gp`). Then the `V`-smoothed diagonal follows as in `ZetaAFE.Diag`.
-/
import RamanujanTau.GoodSecondTerm.SplitD
import RamanujanTau.CriticalMeanSquareAsymp.Main

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE

/-- Rankin's constant `c₀ = L(sym²Δ,1)/ζ(2) ≈ 0.384084`. -/
noncomputable def c0 : ℝ := CriticalMeanSquareAsymp.rankinC

/-- `b(n) = τ(n)²/n¹¹` (`b 0 = 0`). -/
noncomputable def bb (n : ℕ) : ℝ := ((tau n : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 11

noncomputable def SS (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, bb n
noncomputable def EE (N : ℕ) : ℝ := SS N - c0 * N
noncomputable def AA (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, bb n / n

lemma bb_nonneg (n : ℕ) : 0 ≤ bb n := by unfold bb; positivity

lemma exists_EE_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |EE N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC⟩ := CriticalMeanSquareAsymp.rankin_normalization
  refine ⟨max C 0, le_max_right _ _, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [EE, SS]
  · have := hC N h
    unfold EE SS bb c0
    rw [show CriticalMeanSquareAsymp.rankinC = CriticalMeanSquareAsymp.cDelta / 2 by
      unfold CriticalMeanSquareAsymp.cDelta; ring]
    refine this.trans ?_
    gcongr; exact le_max_left _ _

lemma SS_succ (N : ℕ) : SS (N + 1) = SS N + bb (N + 1) := by
  unfold SS; rw [Finset.sum_Icc_succ_top (by omega)]

lemma AA_succ (N : ℕ) : AA (N + 1) = AA N + bb (N + 1) / (N + 1 : ℕ) := by
  unfold AA; rw [Finset.sum_Icc_succ_top (by omega)]

/-- Summation by parts: `A(N) = S(N)/N + Σ_{n<N} S(n)/(n(n+1))`. -/
lemma AA_eq (N : ℕ) : AA N = SS N / N + ∑ n ∈ range N, SS n / ((n : ℝ) * (n + 1)) := by
  induction N with
  | zero => simp [AA, SS]
  | succ N ih =>
    rw [AA_succ, ih, Finset.sum_range_succ, SS_succ]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [SS]
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      push_cast
      field_simp
      ring

lemma tsumE_term_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ N : ℕ, |EE N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5))
    (n : ℕ) : |EE n / ((n : ℝ) * (n + 1))| ≤ C * (n : ℝ) ^ (-(7 / 5 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
    have hn0 : (0 : ℝ) < n := by linarith
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < n * (n + 1)), div_le_iff₀ (by positivity)]
    refine (hC n).trans ?_
    have e : (n : ℝ) ^ (-(7 / 5 : ℝ)) * (n * n) = (n : ℝ) ^ ((3 : ℝ) / 5) := by
      rw [show (n : ℝ) * n = (n : ℝ) ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_add hn0]
      norm_num
    have : (n : ℝ) * n ≤ n * (n + 1) := by nlinarith
    calc C * (n : ℝ) ^ ((3 : ℝ) / 5) = C * ((n : ℝ) ^ (-(7 / 5 : ℝ)) * (n * n)) := by rw [e]
      _ ≤ C * ((n : ℝ) ^ (-(7 / 5 : ℝ)) * (n * (n + 1))) := by gcongr
      _ = _ := by ring

lemma summable_rpow_nat {p : ℝ} (hp : 1 < p) : Summable fun n : ℕ => (n : ℝ) ^ (-p) := by
  have := Real.summable_nat_rpow_inv.mpr hp
  refine this.congr fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]

/-- `γ_Δ = c₀γ + Σ_{n≥1} E(n)/(n(n+1))`. -/
noncomputable def gammaD : ℝ :=
  c0 * Real.eulerMascheroniConstant + ∑' n : ℕ, EE n / ((n : ℝ) * (n + 1))

/-- `|A(N) − c₀ log N − γ_Δ| ≤ C N^{−1/5}` for `N ≥ 1`. -/
theorem AA_asymp : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |AA N - c0 * Real.log N - gammaD| ≤ C * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_EE_le
  set f : ℕ → ℝ := fun n => EE n / ((n : ℝ) * (n + 1)) with hf
  have hfs : Summable f := Summable.of_norm_bounded ((summable_rpow_nat (p := 7 / 5) (by norm_num)).mul_left C)
    (fun n => by rw [Real.norm_eq_abs]; exact tsumE_term_le hC0 hC n)
  set Z : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ (-(6 / 5 : ℝ)) with hZ
  have hZs := summable_rpow_neg (σ := 6 / 5) (by norm_num)
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun k => by positivity)
  refine ⟨|c0| + C + C * Z, by positivity, fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNp : (N : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num)
  have hNp0 : 0 < (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
  -- A(N) = c₀ H_N + E(N)/N + Σ_{n<N} f n
  have hA : AA N = c0 * (harmonic N : ℝ) + EE N / N + ∑ n ∈ range N, f n := by
    rw [AA_eq]
    have hH : ∑ n ∈ range N, c0 * (n : ℝ) / ((n : ℝ) * (n + 1)) = c0 * ((harmonic N : ℝ) - 1) := by
      have : ∀ n ∈ range N, c0 * (n : ℝ) / ((n : ℝ) * (n + 1)) =
          (if n = 0 then 0 else c0 * (1 / ((n : ℝ) + 1))) := by
        intro n _
        split_ifs with h
        · subst h; simp
        · have : (n : ℝ) ≠ 0 := by exact_mod_cast h
          field_simp
      rw [Finset.sum_congr rfl this]
      have hh : (harmonic N : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
        unfold harmonic; push_cast; congr 1; funext n; rw [one_div]
      rw [hh]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp [Finset.mul_sum]
    have hsplit : ∑ n ∈ range N, SS n / ((n : ℝ) * (n + 1)) =
        ∑ n ∈ range N, c0 * (n : ℝ) / ((n : ℝ) * (n + 1)) + ∑ n ∈ range N, f n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hf, EE]; ring
    rw [hsplit, hH]
    have : SS N / N = c0 + EE N / N := by unfold EE; field_simp; ring
    rw [this]; ring
  -- tail
  have htail : ∑ n ∈ range N, f n = (∑' n, f n) - ∑' k, f (k + N) := by
    rw [← hfs.sum_add_tsum_nat_add N]; ring
  have htail_le : |∑' k, f (k + N)| ≤ C * Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
    have hb : ∀ k : ℕ, ‖f (k + N)‖ ≤ C * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((k : ℝ) + 1) ^ (-(6 / 5 : ℝ)) := by
      intro k
      rw [Real.norm_eq_abs]
      refine (tsumE_term_le hC0 hC (k + N)).trans ?_
      have hkN : (0 : ℝ) < (k + N : ℕ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      have h1 : ((k + N : ℕ) : ℝ) ^ (-(7 / 5 : ℝ)) =
          ((k + N : ℕ) : ℝ) ^ (-(1 / 5 : ℝ)) * ((k + N : ℕ) : ℝ) ^ (-(6 / 5 : ℝ)) := by
        rw [← Real.rpow_add hkN]; norm_num
      rw [h1, ← mul_assoc]
      have hA : ((k + N : ℕ) : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hN0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
          (by norm_num)
      have hB : ((k + N : ℕ) : ℝ) ^ (-(6 / 5 : ℝ)) ≤ ((k : ℝ) + 1) ^ (-(6 / 5 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by norm_num)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA hC0) hB (by positivity) (by positivity)
    have := tsum_of_norm_bounded (hZs.hasSum.mul_left (C * (N : ℝ) ^ (-(1 / 5 : ℝ)))) hb
    rw [← Real.norm_eq_abs]; refine this.trans (le_of_eq ?_); rw [hZ]; ring
  have hharm : |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| ≤ 1 / N := by
    have hs1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
    have hs2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
    unfold Real.eulerMascheroniSeq at hs1
    unfold Real.eulerMascheroniSeq' at hs2
    rw [if_neg (by omega)] at hs2
    have hl : Real.log (N + 1) - Real.log N ≤ 1 / N := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1) / N) (by positivity)
      have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    rw [abs_le]; constructor <;> linarith
  have hEN : |EE N / N| ≤ C * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    have e : (N : ℝ) ^ ((3 : ℝ) / 5) = (N : ℝ) ^ (-(2 / 5 : ℝ)) * N := by
      rw [← Real.rpow_add_one hN0.ne']; norm_num
    have h25 : (N : ℝ) ^ (-(2 / 5 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
    calc |EE N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := hC N
      _ = C * ((N : ℝ) ^ (-(2 / 5 : ℝ)) * N) := by rw [e]
      _ ≤ C * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * N) := by gcongr
      _ = _ := by ring
  have hinv : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hdecomp : AA N - c0 * Real.log N - gammaD =
      c0 * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) + EE N / N -
        ∑' k, f (k + N) := by
    rw [hA, htail]; unfold gammaD; rw [← hf]; ring
  rw [hdecomp]
  have t1 : |c0 * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)| =
      |c0| * |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| := abs_mul _ _
  calc |c0 * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) + EE N / N -
        ∑' k, f (k + N)|
      ≤ |c0 * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) + EE N / N| +
        |∑' k, f (k + N)| := abs_sub _ _
    _ ≤ |c0| * |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| + |EE N / N| +
        |∑' k, f (k + N)| := by rw [← t1]; gcongr; exact abs_add_le _ _
    _ ≤ |c0| * (N : ℝ) ^ (-(1 / 5 : ℝ)) + C * (N : ℝ) ^ (-(1 / 5 : ℝ)) +
        C * Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
        gcongr
        exact hharm.trans hinv
    _ = _ := by ring

end RamanujanTau.GoodSecondTerm
