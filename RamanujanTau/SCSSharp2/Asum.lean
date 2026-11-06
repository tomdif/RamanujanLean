/-
# Sharp sums with `h`-exponent `1/22`: `|Σ_{n≤N} τ(n)τ(n+h)| ≤ C h^{1/22} (N+h)^{12 − 1/22}` (`N ≥ h`)

Copy of `SCSSharp.Asum_bound_large'` with `√h` replaced by `h^{1/22}` (input `Rmean2_boundG`).
-/
import RamanujanTau.SCSSharp.Asum
import RamanujanTau.SCSSharp2.Rmean

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError RamanujanTau.EisensteinReal
open RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped Real

set_option maxHeartbeats 4000000 in
theorem Asum_bound_largeG : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ N : ℕ, h ≤ N →
    |Asum h N| ≤ C * (h : ℝ) ^ (1 / 22 : ℝ) * ((N : ℝ) + h) ^ (12 - ηs) := by
  obtain ⟨C₁, hC₁, hR⟩ := Rmean2_boundG
  obtain ⟨A, hA0, hA⟩ := sum_aabs_le
  obtain ⟨c, C, hc0, hC0, hRS⟩ := rankin_short'
  set F : ℝ := (Nat.factorial 10 : ℝ)
  have hF : 0 < F := by positivity
  refine ⟨C₁ + 8 * F * A + 4 * c + 4 * C, by positivity, fun h hh N hN => ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hNR : (h : ℝ) ≤ N := by exact_mod_cast hN
  have hsh : (1 : ℝ) ≤ (h : ℝ) ^ (1 / 22 : ℝ) := Real.one_le_rpow hhR (by norm_num)
  set x : ℝ := (N : ℝ) + 1 with hxdef
  set M : ℝ := (N : ℝ) + h with hMdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hxM : x ≤ M := by linarith
  have hMx : M ≤ 2 * x := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hη := ηs_pos; have hη2 := ηs_le
  set L := x * x ^ (-(1 / 20 : ℝ)) with hLdef
  have hL : 0 < L := by positivity
  have hRb := hR h hh x hx1 (by linarith)
  rw [← hLdef, hxdef, Rmean2_eq h N hL, ← hxdef] at hRb
  set u : ℕ → ℝ := fun n => Real.exp ((n - x) / L) with hu
  -- decomposition
  have hdec : Asum h N = (∑ n ∈ range (N + 1), aR h n * (1 - u n) ^ 2) +
      ∑ n ∈ range (N + 1), aR h n * (u n * (2 - u n)) := by
    unfold Asum; rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => by ring
  set s := x ^ (1 / 220 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  set D : ℕ := ⌈x ^ (1 - ηs)⌉₊
  have hD1 : x ^ (1 - ηs) ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ x ^ (1 - ηs) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- the far part
  have hfar : ∀ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), u n ≤ F / s ^ 10 := by
    intro n hn
    obtain ⟨-, hnD⟩ := mem_filter.1 hn
    have hnD' : (n : ℝ) + D ≤ N := by exact_mod_cast hnD
    have hkey : s ≤ (x - n) / L := by
      rw [le_div_iff₀ hL, hLdef, hs, mul_comm x, ← mul_assoc, ← Real.rpow_add hx0,
        ← Real.rpow_add_one hx0.ne']
      have : (1 / 220 : ℝ) + -(1 / 20) + 1 = 1 - ηs := by unfold ηs; norm_num
      rw [this]; linarith
    have hexp : s ^ 10 / F ≤ Real.exp ((x - n) / L) :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0.le hkey 10) hF.le).trans
        (Real.pow_div_factorial_le_exp _ (le_trans hs0.le hkey) 10)
    calc u n = (Real.exp ((x - n) / L))⁻¹ := by
          simp only [hu]; rw [← Real.exp_neg]; ring_nf
      _ ≤ (s ^ 10 / F)⁻¹ := by
          gcongr
      _ = F / s ^ 10 := by rw [inv_div]
  have hu0 : ∀ n, 0 < u n := fun n => Real.exp_pos _
  have hfar_sum : ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n * u n ≤
      F / s ^ 10 * (A * M ^ 12) := by
    calc ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabs h n * (F / s ^ 10) :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hfar n hn) (aabs_nonneg _ _)
      _ ≤ ∑ n ∈ range (N + 1), aabs h n * (F / s ^ 10) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun n _ _ => mul_nonneg (aabs_nonneg _ _) (by positivity))
      _ = F / s ^ 10 * ∑ n ∈ range (N + 1), aabs h n := by rw [← sum_mul]; ring
      _ ≤ F / s ^ 10 * (A * M ^ 12) := by gcongr; exact hA h N
  -- the near part
  have hnear_sub : (range (N + 1)).filter (fun n => ¬ n + D ≤ N) ⊆ insert 0 (Ioc (N - D) N) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_filter.1 hn
    rw [mem_range] at h1
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_Ioc.2 ⟨by omega, by omega⟩)
  have hnear_sum : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n * u n ≤
      M ^ 11 * (c * D + 2 * C * M ^ (1 - ηs)) := by
    have ha0 : aabs h 0 = 0 := by simp [aabs, RamanujanTau.tau_zero]
    calc ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabs h n := by
          refine sum_le_sum fun n hn => ?_
          have hn' : (n : ℝ) < x := by
            have := mem_range.1 (mem_filter.1 hn).1; rw [hxdef]; exact_mod_cast this
          have : u n ≤ 1 :=
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
      _ ≤ ((c * ((N : ℝ) - ((N - D : ℕ) : ℝ)) + 2 * C * (N : ℝ) ^ (1 - ηs)) +
            (c * (((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ)) + 2 * C * ((N + h : ℕ) : ℝ) ^ (1 - ηs))) /
            2 * M ^ 11 := by
          gcongr
          · exact hRS _ _ (Nat.sub_le N D)
          · exact hRS _ _ (by omega)
      _ ≤ (2 * (c * D) + 2 * (2 * C * M ^ (1 - ηs))) / 2 * M ^ 11 := by
          have hsub : (N : ℝ) - ((N - D : ℕ) : ℝ) ≤ D := by
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hsub2 : ((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ) ≤ D := by
            push_cast
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hpN : (N : ℝ) ^ (1 - ηs) ≤ M ^ (1 - ηs) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
          have hpNh : ((N + h : ℕ) : ℝ) ^ (1 - ηs) = M ^ (1 - ηs) := by push_cast; rfl
          rw [hpNh]
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num))
            (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hsub hc0, mul_le_mul_of_nonneg_left hsub2 hc0,
            mul_le_mul_of_nonneg_left hpN (by positivity : (0 : ℝ) ≤ 2 * C)]
      _ = M ^ 11 * (c * D + 2 * C * M ^ (1 - ηs)) := by ring
  -- combine
  have herr : |∑ n ∈ range (N + 1), aR h n * (u n * (2 - u n))| ≤
      2 * (F / s ^ 10 * (A * M ^ 12) + M ^ 11 * (c * D + 2 * C * M ^ (1 - ηs))) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e : ∀ n ∈ range (N + 1), |aR h n * (u n * (2 - u n))| ≤ 2 * (aabs h n * u n) := by
      intro n hn
      have hn' : (n : ℝ) < x := by
        have := mem_range.1 hn; rw [hxdef]; exact_mod_cast this
      have hu1 : u n ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
      have := hu0 n
      rw [abs_mul, abs_aR, abs_of_nonneg (by nlinarith)]
      have ha := aabs_nonneg h n
      nlinarith [mul_nonneg ha (sq_nonneg (u n))]
    refine (sum_le_sum e).trans ?_
    rw [← mul_sum, ← sum_filter_add_sum_filter_not (range (N + 1)) (fun n => n + D ≤ N)]
    gcongr
  -- numerics
  have hxρ : x ^ (12 - ηs) ≤ M ^ (12 - ηs) := Real.rpow_le_rpow hx0.le hxM (by linarith)
  have hsinv : F / s ^ 10 ≤ 2 * F * M ^ (-ηs) := by
    have hs10 : s ^ 10 = x ^ ηs := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; unfold ηs; norm_num
    rw [hs10]
    have h2 : (M / 2) ^ ηs ≤ x ^ ηs := Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    have h3 : (M / 2) ^ ηs = M ^ ηs / 2 ^ ηs := Real.div_rpow hM0.le (by norm_num) _
    have h4 : (2 : ℝ) ^ ηs ≤ 2 := by
      calc (2 : ℝ) ^ ηs ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by simp
    have hMρ : 0 < M ^ ηs := Real.rpow_pos_of_pos hM0 _
    have hxη : 0 < x ^ ηs := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hM0.le, div_le_iff₀ hxη]
    have : M ^ ηs ≤ 2 * x ^ ηs := by
      rw [h3, div_le_iff₀ (by positivity)] at h2; nlinarith
    calc F = 2 * F * (M ^ ηs)⁻¹ * (M ^ ηs / 2) := by field_simp
      _ ≤ 2 * F * (M ^ ηs)⁻¹ * x ^ ηs := by gcongr; linarith
  have hDM : (D : ℝ) ≤ 2 * M ^ (1 - ηs) := by
    have h1 : x ^ (1 - ηs) ≤ M ^ (1 - ηs) := Real.rpow_le_rpow hx0.le hxM (by linarith)
    have h2 : 1 ≤ M ^ (1 - ηs) := Real.one_le_rpow hM1 (by linarith)
    linarith
  have hM12 : M ^ 12 * M ^ (-ηs) = M ^ (12 - ηs) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0]; norm_num; ring_nf
  have hM11 : M ^ 11 * M ^ (1 - ηs) = M ^ (12 - ηs) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0]; norm_num; ring_nf
  have hMp : 0 ≤ M ^ (12 - ηs) := (Real.rpow_pos_of_pos hM0 _).le
  rw [hdec]
  calc |(∑ n ∈ range (N + 1), aR h n * (1 - u n) ^ 2) +
        ∑ n ∈ range (N + 1), aR h n * (u n * (2 - u n))|
      ≤ |∑ n ∈ range (N + 1), aR h n * (1 - u n) ^ 2| +
          |∑ n ∈ range (N + 1), aR h n * (u n * (2 - u n))| := abs_add_le _ _
    _ ≤ C₁ * (h : ℝ) ^ (1 / 22 : ℝ) * M ^ (12 - ηs) + 2 * ((2 * F * M ^ (-ηs)) * (A * M ^ 12) +
          M ^ 11 * (c * (2 * M ^ (1 - ηs)) + 2 * C * M ^ (1 - ηs))) := by
        gcongr
        · exact hRb.trans (by gcongr)
        · refine herr.trans ?_
          gcongr
    _ = (C₁ * (h : ℝ) ^ (1 / 22 : ℝ) + 4 * F * A + 4 * c + 4 * C) * M ^ (12 - ηs) := by
        have e1 : (2 * F * M ^ (-ηs)) * (A * M ^ 12) = 2 * F * A * (M ^ 12 * M ^ (-ηs)) := by ring
        have e2 : M ^ 11 * (c * (2 * M ^ (1 - ηs)) + 2 * C * M ^ (1 - ηs)) =
            (2 * c + 2 * C) * (M ^ 11 * M ^ (1 - ηs)) := by ring
        rw [e1, e2, hM12, hM11]; ring
    _ ≤ (C₁ + 8 * F * A + 4 * c + 4 * C) * (h : ℝ) ^ (1 / 22 : ℝ) * M ^ (12 - ηs) := by
        have : C₁ * (h : ℝ) ^ (1 / 22 : ℝ) + 4 * F * A + 4 * c + 4 * C ≤
            (C₁ + 8 * F * A + 4 * c + 4 * C) * (h : ℝ) ^ (1 / 22 : ℝ) := by
          have : 0 ≤ 8 * F * A + 4 * c + 4 * C := by positivity
          nlinarith
        nlinarith

end RamanujanTau.SCSSharp2
