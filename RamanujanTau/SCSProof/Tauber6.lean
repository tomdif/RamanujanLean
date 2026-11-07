/-
# Tauberian step 6: the bound for `A(N)` when `N ≥ h`
-/
import RamanujanTau.SCSProof.Tauber5

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError
open scoped Real

lemma phi1_of_ge {u : ℝ} (hu : 1 ≤ u) : phi 1 u = 0 := by
  unfold phi; rw [max_eq_right (by linarith)]; simp

lemma phi1_of_le {u : ℝ} (hu : u ≤ 1) : phi 1 u = 1 - u := by
  rw [phi_of_le hu, pow_one]

/-- `Rmean` as a finite sum. -/
lemma Rmean_eq (h N : ℕ) {L : ℝ} (hL : 0 < L) :
    Rmean h ((N : ℝ) + 1) L = ∑ n ∈ range (N + 1), aR h n *
      (1 - Real.exp ((n - ((N : ℝ) + 1)) / L)) := by
  unfold Rmean
  rw [tsum_eq_sum (s := range (N + 1)) (fun n hn => ?_)]
  · refine sum_congr rfl fun n hn => ?_
    have : (n : ℝ) < N + 1 := by exact_mod_cast mem_range.1 hn
    rw [phi1_of_le (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le))]
  · have : (N : ℝ) + 1 ≤ n := by
      have := not_lt.1 (fun h => hn (mem_range.2 h)); exact_mod_cast this
    rw [phi1_of_ge (Real.one_le_exp (div_nonneg (by linarith) hL.le)), mul_zero]

set_option maxHeartbeats 2000000 in
theorem Asum_bound_large : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ N : ℕ, h ≤ N →
    |Asum h N| ≤ C * h * ((N : ℝ) + h) ^ (12 - ρ) := by
  obtain ⟨C₁, hC₁, hR⟩ := Rmean_bound
  obtain ⟨A, hA0, hA⟩ := sum_aabs_le
  obtain ⟨c, C, hc0, hC0, hRS⟩ := rankin_short
  refine ⟨C₁ + 2 * A + 2 * c + 2 * C, by positivity, fun h hh N hN => ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hNR : (h : ℝ) ≤ N := by exact_mod_cast hN
  set x : ℝ := (N : ℝ) + 1 with hxdef
  set M : ℝ := (N : ℝ) + h with hMdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hxM : x ≤ M := by linarith
  have hMx : M ≤ 2 * x := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hρ := ρ_pos; have hρ8 := ρ_le
  set L := x * x ^ (-(1 / 4000 : ℝ)) with hLdef
  have hL : 0 < L := by positivity
  have hRb := hR h hh x hx1 (by linarith)
  rw [← hLdef, hxdef, Rmean_eq h N hL, ← hxdef] at hRb
  -- decomposition
  have hdec : Asum h N = (∑ n ∈ range (N + 1), aR h n * (1 - Real.exp ((n - x) / L))) +
      ∑ n ∈ range (N + 1), aR h n * Real.exp ((n - x) / L) := by
    unfold Asum; rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => by ring
  set s := x ^ (1 / 8000 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  set D : ℕ := ⌈x ^ (1 - 1 / 8000 : ℝ)⌉₊
  have hD1 : x ^ (1 - 1 / 8000 : ℝ) ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ x ^ (1 - 1 / 8000 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- the far part
  have hfar : ∀ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N),
      Real.exp ((n - x) / L) ≤ 1 / s := by
    intro n hn
    obtain ⟨-, hnD⟩ := mem_filter.1 hn
    have hnD' : (n : ℝ) + D ≤ N := by exact_mod_cast hnD
    have hkey : s ≤ (x - n) / L := by
      rw [le_div_iff₀ hL, hLdef, hs, mul_comm x, ← mul_assoc, ← Real.rpow_add hx0,
        ← Real.rpow_add_one hx0.ne']
      have : (1 / 8000 : ℝ) + -(1 / 4000) + 1 = 1 - 1 / 8000 := by norm_num
      rw [this]; linarith
    calc Real.exp ((n - x) / L) = Real.exp (-((x - n) / L)) := by ring_nf
      _ ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 1 / s := by
          rw [Real.exp_neg, ← one_div]
          gcongr
          have := Real.add_one_le_exp s; linarith
  have hfar_sum : ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n *
      Real.exp ((n - x) / L) ≤ 1 / s * (A * M ^ 12) := by
    calc ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n * Real.exp ((n - x) / L)
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n * (1 / s) :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hfar n hn) (aabs_nonneg _ _)
      _ ≤ ∑ n ∈ range (N + 1), aabs h n * (1 / s) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun n _ _ => mul_nonneg (aabs_nonneg _ _) (by positivity))
      _ = 1 / s * ∑ n ∈ range (N + 1), aabs h n := by rw [← sum_mul]; ring
      _ ≤ 1 / s * (A * M ^ 12) := by gcongr; exact hA h N
  -- the near part
  have hnear_sub : (range (N + 1)).filter (fun n => ¬ n + D ≤ N) ⊆ insert 0 (Ioc (N - D) N) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_filter.1 hn
    rw [mem_range] at h1
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_Ioc.2 ⟨by omega, by omega⟩)
  have hnear_sum : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n *
      Real.exp ((n - x) / L) ≤ M ^ 11 * (c * D + 2 * C * M ^ (1 - ρ)) := by
    have ha0 : aabs h 0 = 0 := by simp [aabs, RamanujanTau.tau_zero]
    calc ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n * Real.exp ((n - x) / L)
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n := by
          refine sum_le_sum fun n hn => ?_
          have hn' : (n : ℝ) < x := by
            have := mem_range.1 (mem_filter.1 hn).1; rw [hxdef]; exact_mod_cast this
          have : Real.exp ((n - x) / L) ≤ 1 :=
            Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
          have := aabs_nonneg h n
          nlinarith
      _ ≤ ∑ n ∈ insert 0 (Ioc (N - D) N), aabs h n :=
          sum_le_sum_of_subset_of_nonneg hnear_sub (fun n _ _ => aabs_nonneg _ _)
      _ = aabs h 0 + ∑ n ∈ Ioc (N - D) N, aabs h n := by
          rw [sum_insert (by simp)]
      _ = ∑ n ∈ Ioc (N - D) N, aabs h n := by rw [ha0, zero_add]
      _ ≤ ∑ n ∈ Ioc (N - D) N, (lam n ^ 2 + lam (n + h) ^ 2) / 2 * M ^ 11 := by
          refine sum_le_sum fun n hn => (aabs_le_lam h n).trans ?_
          have : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.1 hn).2
          gcongr
          rw [hMdef]; linarith
      _ = ((Slam N - Slam (N - D)) + (Slam (N + h) - Slam (N - D + h))) / 2 * M ^ 11 := by
          have hS1 : ∑ n ∈ Ioc (N - D) N, lam n ^ 2 = Slam N - Slam (N - D) := by
            unfold Slam; rw [sum_Icc_eq_Slam_sub _ _ _ (Nat.sub_le N D)]
          have hS2 : ∑ n ∈ Ioc (N - D) N, lam (n + h) ^ 2 = Slam (N + h) - Slam (N - D + h) := by
            have : ∑ n ∈ Ioc (N - D) N, lam (n + h) ^ 2 =
                ∑ m ∈ Ioc (N - D + h) (N + h), lam m ^ 2 := by
              have hset : Ioc (N - D + h) (N + h) = (Ioc (N - D) N).map (addRightEmbedding h) := by
                ext m; simp only [mem_map, mem_Ioc, addRightEmbedding_apply]
                constructor
                · intro hm; exact ⟨m - h, by omega, by omega⟩
                · rintro ⟨n, ⟨h1, h2⟩, rfl⟩; omega
              rw [hset, sum_map]; rfl
            rw [this]; unfold Slam; rw [sum_Icc_eq_Slam_sub _ _ _ (by omega)]
          rw [← sum_mul, ← sum_div, sum_add_distrib, hS1, hS2]
      _ ≤ ((c * ((N : ℝ) - ((N - D : ℕ) : ℝ)) + 2 * C * (N : ℝ) ^ (1 - ρ)) +
            (c * (((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ)) + 2 * C * ((N + h : ℕ) : ℝ) ^ (1 - ρ))) /
            2 * M ^ 11 := by
          gcongr
          · exact hRS _ _ (Nat.sub_le N D)
          · exact hRS _ _ (by omega)
      _ ≤ (2 * (c * D) + 2 * (2 * C * M ^ (1 - ρ))) / 2 * M ^ 11 := by
          have hsub : (N : ℝ) - ((N - D : ℕ) : ℝ) ≤ D := by
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hsub2 : ((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ) ≤ D := by
            push_cast
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hpN : (N : ℝ) ^ (1 - ρ) ≤ M ^ (1 - ρ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
          have hpNh : ((N + h : ℕ) : ℝ) ^ (1 - ρ) = M ^ (1 - ρ) := by push_cast; rfl
          rw [hpNh]
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num))
            (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hsub hc0, mul_le_mul_of_nonneg_left hsub2 hc0,
            mul_le_mul_of_nonneg_left hpN (by positivity : (0 : ℝ) ≤ 2 * C)]
      _ = M ^ 11 * (c * D + 2 * C * M ^ (1 - ρ)) := by ring
  -- combine
  have herr : |∑ n ∈ range (N + 1), aR h n * Real.exp ((n - x) / L)| ≤
      1 / s * (A * M ^ 12) + M ^ 11 * (c * D + 2 * C * M ^ (1 - ρ)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e : ∀ n, |aR h n * Real.exp ((n - x) / L)| = aabs h n * Real.exp ((n - x) / L) := by
      intro n; rw [abs_mul, abs_aR, abs_of_pos (Real.exp_pos _)]
    simp_rw [e]
    rw [← sum_filter_add_sum_filter_not (range (N + 1)) (fun n => n + D ≤ N)]
    exact add_le_add hfar_sum hnear_sum
  -- numerics
  have hxρ : x ^ (12 - 1 / 8000 : ℝ) ≤ M ^ (12 - ρ) := by
    calc x ^ (12 - 1 / 8000 : ℝ) ≤ x ^ (12 - ρ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ ≤ M ^ (12 - ρ) := Real.rpow_le_rpow hx0.le hxM (by linarith)
  have hsinv : 1 / s ≤ 2 * M ^ (-ρ) := by
    have h1 : x ^ ρ ≤ s := Real.rpow_le_rpow_of_exponent_le hx1 hρ8
    have h2 : (M / 2) ^ ρ ≤ x ^ ρ := Real.rpow_le_rpow (by positivity) (by linarith) hρ.le
    have h3 : (M / 2) ^ ρ = M ^ ρ / 2 ^ ρ := Real.div_rpow hM0.le (by norm_num) _
    have h4 : (2 : ℝ) ^ ρ ≤ 2 := by
      calc (2 : ℝ) ^ ρ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by simp
    have hMρ : 0 < M ^ ρ := Real.rpow_pos_of_pos hM0 _
    rw [Real.rpow_neg hM0.le]
    rw [div_le_iff₀ hs0]
    have : M ^ ρ ≤ 2 * s := by
      have := h2.trans h1; rw [h3, div_le_iff₀ (by positivity)] at this; nlinarith
    calc (1 : ℝ) = (M ^ ρ)⁻¹ * M ^ ρ := by field_simp
      _ ≤ (M ^ ρ)⁻¹ * (2 * s) := by gcongr
      _ = 2 * (M ^ ρ)⁻¹ * s := by ring
  have hDM : (D : ℝ) ≤ 2 * M ^ (1 - ρ) := by
    have h1 : x ^ (1 - 1 / 8000 : ℝ) ≤ M ^ (1 - ρ) := by
      calc x ^ (1 - 1 / 8000 : ℝ) ≤ x ^ (1 - ρ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ ≤ M ^ (1 - ρ) := Real.rpow_le_rpow hx0.le hxM (by linarith)
    have h2 : 1 ≤ M ^ (1 - ρ) := Real.one_le_rpow hM1 (by linarith)
    linarith
  have hM12 : M ^ 12 * M ^ (-ρ) = M ^ (12 - ρ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0]; norm_num; ring_nf
  have hM11 : M ^ 11 * M ^ (1 - ρ) = M ^ (12 - ρ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0]; norm_num; ring_nf
  have hMp : 0 ≤ M ^ (12 - ρ) := (Real.rpow_pos_of_pos hM0 _).le
  rw [hdec]
  calc |(∑ n ∈ range (N + 1), aR h n * (1 - Real.exp ((n - x) / L))) +
        ∑ n ∈ range (N + 1), aR h n * Real.exp ((n - x) / L)|
      ≤ |∑ n ∈ range (N + 1), aR h n * (1 - Real.exp ((n - x) / L))| +
          |∑ n ∈ range (N + 1), aR h n * Real.exp ((n - x) / L)| := abs_add_le _ _
    _ ≤ C₁ * h * M ^ (12 - ρ) + ((2 * M ^ (-ρ)) * (A * M ^ 12) +
          M ^ 11 * (c * (2 * M ^ (1 - ρ)) + 2 * C * M ^ (1 - ρ))) := by
        gcongr
        · exact hRb.trans (by gcongr)
        · refine herr.trans ?_
          gcongr
    _ = (C₁ * h + 2 * A + 2 * c + 2 * C) * M ^ (12 - ρ) := by
        have e1 : (2 * M ^ (-ρ)) * (A * M ^ 12) = 2 * A * (M ^ 12 * M ^ (-ρ)) := by ring
        have e2 : M ^ 11 * (c * (2 * M ^ (1 - ρ)) + 2 * C * M ^ (1 - ρ)) =
            (2 * c + 2 * C) * (M ^ 11 * M ^ (1 - ρ)) := by ring
        rw [e1, e2, hM12, hM11]; ring
    _ ≤ (C₁ + 2 * A + 2 * c + 2 * C) * h * M ^ (12 - ρ) := by
        have : C₁ * h + 2 * A + 2 * c + 2 * C ≤ (C₁ + 2 * A + 2 * c + 2 * C) * h := by
          nlinarith
        nlinarith

end RamanujanTau.SCSProof
