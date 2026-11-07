/-
# Generic off-diagonal / mean-value bounds (any real coefficient sequence `l`)

Verbatim generalizations of `SubconvexityCond.offS_eq`, `offS_bound`, `sum_offS_bound`,
`mean_value_bound`, with the fixed sequence `λ = τ(n)n^{−11/2}` replaced by an arbitrary
`l : ℕ → ℝ` and `shiftSum` by `shS l`.  Nothing in these proofs used anything about `τ`.
-/
import RamanujanTau.SubconvexGeneral.Defs

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Real Finset MeasureTheory
open RamanujanTau.SubconvexityCond

/-- `S_h` written as a sum of `λ(n)λ(n+h) G_h(n)`. -/
lemma offS_eqG (l : ℕ → ℝ) (g : ℕ → ℝ) (H T : ℝ) (N h : ℕ) :
    offS (fun n => l n * g n) H T N h = ∑ n ∈ Icc 1 N, (l n * l (n + h)) * Gw g H T h n := by
  unfold offS Gw
  refine sum_congr rfl fun n _ => ?_
  rw [kw_shift]; ring

set_option maxHeartbeats 800000 in
/-- **The off-diagonal bound for one shift `h`.** -/
theorem offS_boundG (l : ℕ → ℝ) {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hC0 : 0 ≤ C)
    (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N h : ℕ} (hg : GBound g K N) (hh : 1 ≤ h)
    (hhN : h ≤ N) (hA : ∀ n : ℕ, |shS l h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    |offS (fun n => l n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        (if (h : ℝ) * H ≤ N * ρ then
          2 * C * (h : ℝ) ^ B * ((h : ℝ) * H / ρ) ^ (-η) *
            ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) else 0)) := by
  have hH0 : 0 < H := by linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hh.trans hhN)
  have hhNr : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hK := hg.nonneg
  set ε0 := Real.exp (-ρ ^ 2 / 64)
  have hε0 : 0 < ε0 := Real.exp_pos _
  -- Abel summation
  rw [offS_eqG l, abel_Icc]
  have hG : Gw g H T h (N + 1) = 0 := by simp [Gw, hg.vanish (N + 1) (by omega)]
  rw [hG, mul_zero, zero_add]
  set α : ℕ → ℝ := fun n => C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B with hα
  have hα0 : ∀ n : ℕ, 0 ≤ α n := fun n => by simp only [hα]; positivity
  have step1 : |∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, l k * l (k + h)) *
      (Gw g H T h n - Gw g H T h (n + 1))| ≤ K ^ 2 * ∑ n ∈ Icc 1 N, α n * phiB H T h n := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    rw [abs_mul]
    have h1 : |∑ k ∈ Icc 1 n, l k * l (k + h)| ≤ α n := hA n
    have h2 := Gw_diff hg hH0.le T h hn1
    have := phiB_nonneg hH0.le T h hn1
    calc |∑ k ∈ Icc 1 n, l k * l (k + h)| * |Gw g H T h n - Gw g H T h (n + 1)|
        ≤ α n * (K ^ 2 * phiB H T h n) := mul_le_mul h1 h2 (abs_nonneg _) (hα0 n)
      _ = K ^ 2 * (α n * phiB H T h n) := by ring
  refine step1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg K))
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n : ℕ => (n : ℝ) * ρ < h * H)]
  refine add_le_add ?_ ?_
  · -- region 1: the Gaussian factor is tiny
    have hterm : ∀ n ∈ (Icc 1 N).filter (fun n : ℕ => (n : ℝ) * ρ < h * H),
        α n * phiB H T h n ≤ 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hnρ⟩ := hn
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
      have hsm := Ef_small hρ hρH hh hn1 hnρ
      have hE0 := Ef_pos H h n
      have hEm := Ef_mono hH0.le (h := h) hn1
      have ha : α n ≤ C * (2 * N) * (N : ℝ) ^ B := by
        simp only [hα]
        have h1 : ((n : ℝ) + h) ^ (1 - η) ≤ 2 * N := by
          calc ((n : ℝ) + h) ^ (1 - η) ≤ ((n : ℝ) + h) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ ≤ 2 * N := by rw [Real.rpow_one]; linarith
        have h2 : (h : ℝ) ^ B ≤ (N : ℝ) ^ B := Real.rpow_le_rpow (by linarith) hhNr hB
        gcongr
      have hp : phiB H T h n ≤ (3 + |T| * N) * ε0 := by
        unfold phiB
        have a1 : 2 * Ef H h (n + 1) / (n : ℝ) ^ 2 ≤ 2 * ε0 := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          nlinarith
        have a2 : (Ef H h (n + 1) - Ef H h n) / n ≤ ε0 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        have a3 : Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3 ≤ ε0 * |T| * N := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1r
          have hT := abs_nonneg T
          have b1 : Ef H h (n + 1) * |T| * h ≤ ε0 * |T| * N := by
            have := mul_le_mul hsm hhNr (by linarith) hε0.le
            nlinarith
          have : 0 ≤ ε0 * |T| * N := by positivity
          nlinarith
        nlinarith
      have hp0 := phiB_nonneg hH0.le T h hn1
      calc α n * phiB H T h n ≤ (C * (2 * N) * (N : ℝ) ^ B) * ((3 + |T| * N) * ε0) :=
            mul_le_mul ha hp hp0 (by positivity)
        _ = 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by ring
    refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
    have hc : (((Icc 1 N).filter (fun n : ℕ => (n : ℝ) * ρ < h * H)).card : ℝ) ≤ N := by
      have := card_filter_le (Icc 1 N) (fun n : ℕ => (n : ℝ) * ρ < h * H)
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : _ ≤ N)
    have : 0 ≤ 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by positivity
    calc _ ≤ (N : ℝ) * (2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0) :=
          mul_le_mul_of_nonneg_right hc this
      _ = 2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by ring
  · -- region 2: the band `n ≥ hH/ρ`
    split_ifs with hband
    · set n0 : ℝ := (h : ℝ) * H / ρ with hn0def
      have hn0pos : 0 < n0 := by positivity
      set Q : ℝ := 2 + |T| * ρ / H
      have hterm : ∀ n ∈ (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H),
          α n * phiB H T h n ≤ 2 * C * (h : ℝ) ^ B * n0 ^ (-η) *
            (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) := by
        intro n hn
        rw [mem_filter, mem_Icc, not_lt] at hn
        obtain ⟨⟨hn1, _⟩, hnρ⟩ := hn
        have hn0r : (0 : ℝ) < n := by exact_mod_cast hn1
        have hnn0 : n0 ≤ n := by rw [hn0def, div_le_iff₀ (by linarith)]; linarith
        have hhn : (h : ℝ) ≤ n := by
          have : (h : ℝ) * ρ ≤ h * H := mul_le_mul_of_nonneg_left hρH (by linarith)
          nlinarith
        have hE0 := Ef_pos H h n
        have hEm := Ef_mono hH0.le (h := h) hn1
        have hE1 := Ef_le_one H h (n + 1)
        -- `(n+h)^{1−η} ≤ 2 n · n^{−η}`
        have ha : ((n : ℝ) + h) ^ (1 - η) ≤ 2 * (n : ℝ) * (n : ℝ) ^ (-η) := by
          calc ((n : ℝ) + h) ^ (1 - η) ≤ (2 * (n : ℝ)) ^ (1 - η) :=
                Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
            _ = (2 : ℝ) ^ (1 - η) * ((n : ℝ) * (n : ℝ) ^ (-η)) := by
                rw [Real.mul_rpow (by norm_num) hn0r.le, sub_eq_add_neg, Real.rpow_add hn0r,
                  Real.rpow_one]
            _ ≤ 2 * ((n : ℝ) * (n : ℝ) ^ (-η)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                calc (2 : ℝ) ^ (1 - η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  _ = 2 := Real.rpow_one 2
            _ = 2 * (n : ℝ) * (n : ℝ) ^ (-η) := by ring
        have hpow : (n : ℝ) ^ (-η) ≤ n0 ^ (-η) :=
          Real.rpow_le_rpow_of_nonpos hn0pos hnn0 (by linarith)
        have hnphi : (n : ℝ) * phiB H T h n ≤ Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n) := by
          unfold phiB
          have hT := abs_nonneg T
          have b1 : (n : ℝ) * (2 * Ef H h (n + 1) / (n : ℝ) ^ 2) ≤ 2 * (1 / (n : ℝ)) := by
            rw [show (n : ℝ) * (2 * Ef H h (n + 1) / (n : ℝ) ^ 2) = 2 * Ef H h (n + 1) / n by
              field_simp]
            rw [div_le_iff₀ hn0r]; field_simp; linarith
          have b2 : (n : ℝ) * ((Ef H h (n + 1) - Ef H h n) / n) = Ef H h (n + 1) - Ef H h n := by
            field_simp
          have b3 : (n : ℝ) * (Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3) ≤
              |T| * ρ / H * (1 / (n : ℝ)) := by
            rw [show (n : ℝ) * (Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3) =
              Ef H h (n + 1) * (|T| * h / (n : ℝ) ^ 2) by field_simp]
            have c1 : |T| * h / (n : ℝ) ^ 2 ≤ |T| * ρ / H * (1 / (n : ℝ)) := by
              rw [div_le_iff₀ (by positivity)]
              have : (h : ℝ) * H ≤ n * ρ := hnρ
              have e5 : |T| * ρ / H * (1 / (n : ℝ)) * (n : ℝ) ^ 2 = |T| * (n * ρ) / H := by
                field_simp
              rw [e5, le_div_iff₀ hH0]
              have := mul_le_mul_of_nonneg_left hnρ (abs_nonneg T)
              linarith
            have : 0 ≤ |T| * h / (n : ℝ) ^ 2 := by positivity
            calc Ef H h (n + 1) * (|T| * h / (n : ℝ) ^ 2) ≤ 1 * (|T| * h / (n : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_right hE1 this
              _ ≤ _ := by linarith
          have : Q * (1 / (n : ℝ)) = 2 * (1 / (n : ℝ)) + |T| * ρ / H * (1 / (n : ℝ)) := by ring
          rw [mul_add, mul_add, b2, this]
          linarith
        have hp0 := phiB_nonneg hH0.le T h hn1
        have hbr : 0 ≤ Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n) := by
          have : 0 ≤ Q := by positivity
          have : 0 ≤ Ef H h (n + 1) - Ef H h n := by linarith
          positivity
        calc α n * phiB H T h n = C * (h : ℝ) ^ B * (((n : ℝ) + h) ^ (1 - η) * phiB H T h n) := by
              simp only [hα]; ring
          _ ≤ C * (h : ℝ) ^ B * (2 * (n : ℝ) ^ (-η) * ((n : ℝ) * phiB H T h n)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have := mul_le_mul_of_nonneg_right ha hp0
              nlinarith
          _ ≤ C * (h : ℝ) ^ B * (2 * n0 ^ (-η) *
                (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : 0 ≤ (n : ℝ) * phiB H T h n := by positivity
              have := mul_le_mul hpow hnphi this (by positivity)
              nlinarith
          _ = _ := by ring
      refine (sum_le_sum hterm).trans ?_
      have hsub : ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H),
          2 * C * (h : ℝ) ^ B * n0 ^ (-η) * (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) ≤
          ∑ n ∈ Icc 1 N,
          2 * C * (h : ℝ) ^ B * n0 ^ (-η) * (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => ?_
        have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
        have := Ef_mono hH0.le (h := h) hn1
        have : 0 ≤ Q := by positivity
        have : 0 ≤ Ef H h (n + 1) - Ef H h n := by linarith
        positivity
      refine hsub.trans ?_
      rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_telescope]
      have hHN : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
        have := RamanujanTau.MeanSquare.H_le_one_add_log N
        unfold RamanujanTau.MeanSquare.H at this; exact this
      have hQ : 0 ≤ Q := by positivity
      have hE1 := Ef_le_one H h (N + 1)
      have hE0 := Ef_pos H h 1
      have : 0 ≤ 2 * C * (h : ℝ) ^ B * n0 ^ (-η) := by positivity
      refine mul_le_mul_of_nonneg_left ?_ this
      have := mul_le_mul_of_nonneg_left hHN hQ
      linarith
    · -- empty band
      have hempty : (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H) = ∅ := by
        refine filter_eq_empty_iff.2 fun n hn => ?_
        rw [not_not]
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.1 hn).2
        have : (n : ℝ) * ρ ≤ N * ρ := mul_le_mul_of_nonneg_right hnN (by linarith)
        push Not at hband
        linarith
      rw [hempty, sum_empty]

/-- Summing the per-shift bound over `1 ≤ h ≤ N`. -/
theorem sum_offS_boundG (l : ℕ → ℝ) {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N : ℕ} (hg : GBound g K N)
    (hA : ∀ h n : ℕ, 1 ≤ h → |shS l h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    ∑ h ∈ Icc 1 N, |offS (fun n => l n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        2 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by
  have hH0 : 0 < H := by linarith
  have hK := hg.nonneg
  set Qf : ℝ := (2 + |T| * ρ / H) * (1 + Real.log N) + 1 with hQf
  set ε0 := Real.exp (-ρ ^ 2 / 64)
  have hε0 : 0 < ε0 := Real.exp_pos _
  have h1 : ∀ h ∈ Icc 1 N, |offS (fun n => l n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * ε0 +
        (if (h : ℝ) * H ≤ N * ρ then 2 * C * (h : ℝ) ^ B * ((h : ℝ) * H / ρ) ^ (-η) * Qf
          else 0)) := by
    intro h hh
    obtain ⟨hh1, hhN⟩ := mem_Icc.1 hh
    exact offS_boundG l hη0 hη1 hB hC0 hρ hρH hg hh1 hhN (fun n => hA h n hh1)
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum, sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hQ0 : 0 ≤ Qf := by
    rw [hQf]
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0]; positivity
    · have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h0)
      positivity
  set Y : ℝ := (N : ℝ) * ρ / H
  have hY0 : 0 ≤ Y := by positivity
  set Z : ℝ := 2 * C * Y ^ B * (H / ρ) ^ (-η) * Qf
  have hZ0 : 0 ≤ Z := by positivity
  have h2 : ∀ h ∈ Icc 1 N, (if (h : ℝ) * H ≤ N * ρ then
      2 * C * (h : ℝ) ^ B * ((h : ℝ) * H / ρ) ^ (-η) * Qf else 0) ≤
      (if (h : ℝ) * H ≤ N * ρ then Z else 0) := by
    intro h hh
    split_ifs with hc
    · have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (mem_Icc.1 hh).1
      have hhY : (h : ℝ) ≤ Y := by rw [le_div_iff₀ hH0]; linarith
      have hb1 : (h : ℝ) ^ B ≤ Y ^ B := Real.rpow_le_rpow (by linarith) hhY hB
      have hb2 : ((h : ℝ) * H / ρ) ^ (-η) ≤ (H / ρ) ^ (-η) := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
        rw [mul_div_assoc]; nlinarith [show 0 < H / ρ by positivity]
      simp only [Z]
      have : 0 ≤ ((h : ℝ) * H / ρ) ^ (-η) := by positivity
      have : 0 ≤ (h : ℝ) ^ B := by positivity
      gcongr
    · exact le_rfl
  refine add_le_add (le_of_eq (by simp only [Nat.add_sub_cancel]; ring)) ((sum_le_sum h2).trans ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hc : ((((Icc 1 N).filter (fun h : ℕ => (h : ℝ) * H ≤ N * ρ)).card : ℕ) : ℝ) ≤ Y := by
    have hsub : (Icc 1 N).filter (fun h : ℕ => (h : ℝ) * H ≤ N * ρ) ⊆ Icc 1 ⌊Y⌋₊ := by
      intro h hh
      rw [mem_filter, mem_Icc] at hh
      rw [mem_Icc]
      refine ⟨hh.1.1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ hH0]; linarith [hh.2]
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    calc ((((Icc 1 N).filter (fun h : ℕ => (h : ℝ) * H ≤ N * ρ)).card : ℕ) : ℝ)
        ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast (by omega : _ ≤ ⌊Y⌋₊)
      _ ≤ Y := Nat.floor_le hY0
  calc _ ≤ Y * Z := mul_le_mul_of_nonneg_right hc hZ0
    _ = _ := by simp only [Z]; ring

/-- **Gaussian-window mean value under `SCS(η, B)`.** -/
theorem mean_value_boundG (l : ℕ → ℝ) {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N : ℕ} (hg : GBound g K N)
    (hA : ∀ h n : ℕ, 1 ≤ h → |shS l h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    ∫ t : ℝ, gw H T t * ‖rpoly (fun n => l n * g n) N t‖ ^ 2 ≤
      H * Real.sqrt π * K ^ 2 * (∑ n ∈ Icc 1 N, l n ^ 2 / n +
        4 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by
  have hH0 : 0 < H := by linarith
  have hva : ∀ m, N < m → l m * g m = 0 := fun m hm => by rw [hg.vanish m hm, mul_zero]
  refine (integral_gw_normSq_le hH0 T _ N hva).trans ?_
  have hdiag : ∑ n ∈ Icc 1 N, (l n * g n) ^ 2 ≤ K ^ 2 * ∑ n ∈ Icc 1 N, l n ^ 2 / n := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hgs := hg.size n hn1
    have hg2 : g n ^ 2 ≤ K ^ 2 / n := by
      have := sq_le_sq' (abs_le.1 hgs).1 (abs_le.1 hgs).2
      rwa [div_pow, Real.sq_sqrt hn0.le] at this
    rw [mul_pow]
    calc l n ^ 2 * g n ^ 2 ≤ l n ^ 2 * (K ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hg2 (sq_nonneg _)
      _ = K ^ 2 * (l n ^ 2 / n) := by ring
  have hoff := sum_offS_boundG l (T := T) hη0 hη1 hB hC0 hρ hρH hg hA
  have : 0 ≤ H * Real.sqrt π := by positivity
  calc H * Real.sqrt π * (∑ n ∈ Icc 1 N, (l n * g n) ^ 2 +
        2 * ∑ h ∈ Icc 1 N, |offS (fun n => l n * g n) H T N h|)
      ≤ H * Real.sqrt π * (K ^ 2 * ∑ n ∈ Icc 1 N, l n ^ 2 / n +
        2 * (K ^ 2 * (2 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) *
          Real.exp (-ρ ^ 2 / 64) + 2 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B *
          (H / ρ) ^ (-η) * ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)))) := by
        gcongr
    _ = _ := by ring

end RamanujanTau.SubconvexGeneral
