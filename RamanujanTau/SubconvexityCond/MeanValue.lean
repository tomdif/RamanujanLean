/-
# The short-interval (Gaussian-window) mean value of `∑ λ(n) g(n) n^{−it}` under `SCS(η,B)`

    ∫ e^{−((t−T)/H)²} |∑_{n≤N} λ(n) g(n) n^{−it}|² dt
      ≤ H√π K² ( ∑_{n≤N} λ(n)²/n + 4C N³ N^B (3+|T|N) e^{−ρ²/64}
                 + 4C (Nρ/H)^{1+B} (H/ρ)^{−η} ((2+|T|ρ/H)(1+log N)+1) )

for `1 ≤ ρ ≤ H` (`mean_value_bound`).  The diagonal is `H·∑λ²/n ≈ H log N`; the off-diagonal is
controlled by `SCS(η,B)` and is `o(H)` as soon as `(N/H)^{1+B} H^{−η} T/H` is small.
-/
import RamanujanTau.SubconvexityCond.OffDiag

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset MeasureTheory

/-- Summing the per-shift bound over `1 ≤ h ≤ N`. -/
theorem sum_offS_bound {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N : ℕ} (hg : GBound g K N)
    (hA : ∀ h n : ℕ, 1 ≤ h → |shiftSum h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    ∑ h ∈ Icc 1 N, |offS (fun n => lam n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        2 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by
  have hH0 : 0 < H := by linarith
  have hK := hg.nonneg
  set Qf : ℝ := (2 + |T| * ρ / H) * (1 + Real.log N) + 1 with hQf
  set ε0 := Real.exp (-ρ ^ 2 / 64)
  have hε0 : 0 < ε0 := Real.exp_pos _
  have h1 : ∀ h ∈ Icc 1 N, |offS (fun n => lam n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * ε0 +
        (if (h : ℝ) * H ≤ N * ρ then 2 * C * (h : ℝ) ^ B * ((h : ℝ) * H / ρ) ^ (-η) * Qf
          else 0)) := by
    intro h hh
    obtain ⟨hh1, hhN⟩ := mem_Icc.1 hh
    exact offS_bound hη0 hη1 hB hC0 hρ hρH hg hh1 hhN (fun n => hA h n hh1)
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
theorem mean_value_bound {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    (hC0 : 0 ≤ C) (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N : ℕ} (hg : GBound g K N)
    (hA : ∀ h n : ℕ, 1 ≤ h → |shiftSum h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    ∫ t : ℝ, gw H T t * ‖rpoly (fun n => lam n * g n) N t‖ ^ 2 ≤
      H * Real.sqrt π * K ^ 2 * (∑ n ∈ Icc 1 N, lam n ^ 2 / n +
        4 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        4 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B * (H / ρ) ^ (-η) *
          ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)) := by
  have hH0 : 0 < H := by linarith
  have hva : ∀ m, N < m → lam m * g m = 0 := fun m hm => by rw [hg.vanish m hm, mul_zero]
  refine (integral_gw_normSq_le hH0 T _ N hva).trans ?_
  have hdiag : ∑ n ∈ Icc 1 N, (lam n * g n) ^ 2 ≤ K ^ 2 * ∑ n ∈ Icc 1 N, lam n ^ 2 / n := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hgs := hg.size n hn1
    have hg2 : g n ^ 2 ≤ K ^ 2 / n := by
      have := sq_le_sq' (abs_le.1 hgs).1 (abs_le.1 hgs).2
      rwa [div_pow, Real.sq_sqrt hn0.le] at this
    rw [mul_pow]
    calc lam n ^ 2 * g n ^ 2 ≤ lam n ^ 2 * (K ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hg2 (sq_nonneg _)
      _ = K ^ 2 * (lam n ^ 2 / n) := by ring
  have hoff := sum_offS_bound (T := T) hη0 hη1 hB hC0 hρ hρH hg hA
  have : 0 ≤ H * Real.sqrt π := by positivity
  calc H * Real.sqrt π * (∑ n ∈ Icc 1 N, (lam n * g n) ^ 2 +
        2 * ∑ h ∈ Icc 1 N, |offS (fun n => lam n * g n) H T N h|)
      ≤ H * Real.sqrt π * (K ^ 2 * ∑ n ∈ Icc 1 N, lam n ^ 2 / n +
        2 * (K ^ 2 * (2 * C * (N : ℝ) ^ 3 * (N : ℝ) ^ B * (3 + |T| * N) *
          Real.exp (-ρ ^ 2 / 64) + 2 * C * ((N : ℝ) * ρ / H) * ((N : ℝ) * ρ / H) ^ B *
          (H / ρ) ^ (-η) * ((2 + |T| * ρ / H) * (1 + Real.log N) + 1)))) := by
        gcongr
    _ = _ := by ring

end RamanujanTau.SubconvexityCond
