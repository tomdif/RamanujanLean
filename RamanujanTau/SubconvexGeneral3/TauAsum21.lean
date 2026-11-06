/-
# Unsmoothing for the `η = 1/21` chain, weight `k` (copy of `SCSSharp2.Asum21`)

* `rankin_shortT21`: Rankin short sums with exponent `1 − 1/21` (exact `N^{3/5}` error, every weight);
* `AsumT_bound_large21`: `|Σ_{n≤N} aT(n)| ≤ C h^{1/21} (N+h)^{k − 1/21}` for `1 ≤ h ≤ N`
  (`L = x^{1−2/39}`, far range killed by `e^{−u} ≤ 13!/u^{13}` at `u = x^{1/273}`).
-/
import RamanujanTau.SubconvexGeneral2.TauAsum
import RamanujanTau.SubconvexGeneral3.TauRiesz21
import RamanujanTau.SCSSharp2.Asum21

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral3

open Finset Complex
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral RamanujanTau.SubconvexGeneral2
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped MatrixGroups Real

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

/-- **Rankin short sums** with exponent `1 − 1/21`. -/
theorem rankin_shortT21 : ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ a b : ℕ, a ≤ b →
    SlamT f b - SlamT f a ≤ c * ((b : ℝ) - a) + 2 * C * (b : ℝ) ^ (1 - SCSSharp2.ηt) := by
  obtain ⟨C, hC35⟩ := RankinExact.rankinSelberg_exact_general f
  set c := RankinSelbergGeneral.rsConst f
  have hC0 : 0 ≤ C := by
    have := hC35 1 le_rfl
    simp at this
    exact le_trans (abs_nonneg _) (by simpa using this)
  have hη2 := SCSSharp2.ηt_le
  have hb : ∀ N : ℕ, |SlamT f N - c * N| ≤ C * (N : ℝ) ^ (1 - SCSSharp2.ηt) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [SlamT]
      have : (0 : ℝ) ^ (1 - SCSSharp2.ηt) = 0 := Real.zero_rpow (by linarith)
      rw [this]; simp
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      refine (le_of_eq ?_).trans ((hC35 N hN).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hC0))
      rfl
  refine ⟨|c|, C, abs_nonneg _, hC0, fun a b hab => ?_⟩
  have h1 := hb b
  have h2 := hb a
  rw [abs_le] at h1 h2
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hpow : (a : ℝ) ^ (1 - SCSSharp2.ηt) ≤ (b : ℝ) ^ (1 - SCSSharp2.ηt) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hab' (by linarith)
  have hcab : c * ((b : ℝ) - a) ≤ |c| * ((b : ℝ) - a) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  nlinarith


set_option maxHeartbeats 4000000 in
theorem AsumT_bound_large21 (hk1 : 1 ≤ k) (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ N : ℕ, h ≤ N →
      |AsumT f h N| ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * ((N : ℝ) + h) ^ ((k : ℝ) - ηt) := by
  obtain ⟨C₁, hC₁, hR⟩ := RmeanT_bound21 f hreal hpw
  obtain ⟨A, hA0, hA⟩ := sum_aabsT_le f hk1
  obtain ⟨c, C, hc0, hC0, hRS⟩ := rankin_shortT21 f
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set F : ℝ := (Nat.factorial 13 : ℝ)
  have hF : 0 < F := by positivity
  refine ⟨C₁ + 8 * F * A + 4 * c + 4 * C, by positivity, fun h hh N hN => ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hNR : (h : ℝ) ≤ N := by exact_mod_cast hN
  have hsh : (1 : ℝ) ≤ (h : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hhR (by norm_num)
  set x : ℝ := (N : ℝ) + 1 with hxdef
  set M : ℝ := (N : ℝ) + h with hMdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hxM : x ≤ M := by linarith
  have hMx : M ≤ 2 * x := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hη := ηt_pos; have hη2 := ηt_le
  set L := x * x ^ (-(2 / 39 : ℝ)) with hLdef
  have hL : 0 < L := by positivity
  have hRb := hR h hh x hx1 (by linarith)
  rw [← hLdef, hxdef, RmeanT_eq f h N hL, ← hxdef] at hRb
  set u : ℕ → ℝ := fun n => Real.exp ((n - x) / L) with hu
  -- decomposition
  have hdec : AsumT f h N = (∑ n ∈ range (N + 1), aT f h n * (1 - u n) ^ 2) +
      ∑ n ∈ range (N + 1), aT f h n * (u n * (2 - u n)) := by
    unfold AsumT; rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => by ring
  set s := x ^ (1 / 273 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  set D : ℕ := ⌈x ^ (1 - ηt)⌉₊
  have hD1 : x ^ (1 - ηt) ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ x ^ (1 - ηt) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- the far part
  have hfar : ∀ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), u n ≤ F / s ^ 13 := by
    intro n hn
    obtain ⟨-, hnD⟩ := mem_filter.1 hn
    have hnD' : (n : ℝ) + D ≤ N := by exact_mod_cast hnD
    have hkey : s ≤ (x - n) / L := by
      rw [le_div_iff₀ hL, hLdef, hs, mul_comm x, ← mul_assoc, ← Real.rpow_add hx0,
        ← Real.rpow_add_one hx0.ne']
      have : (1 / 273 : ℝ) + -(2 / 39) + 1 = 1 - ηt := by unfold ηt; norm_num
      rw [this]; linarith
    have hexp : s ^ 13 / F ≤ Real.exp ((x - n) / L) :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0.le hkey 13) hF.le).trans
        (Real.pow_div_factorial_le_exp _ (le_trans hs0.le hkey) 13)
    calc u n = (Real.exp ((x - n) / L))⁻¹ := by
          simp only [hu]; rw [← Real.exp_neg]; ring_nf
      _ ≤ (s ^ 13 / F)⁻¹ := by
          gcongr
      _ = F / s ^ 13 := by rw [inv_div]
  have hu0 : ∀ n, 0 < u n := fun n => Real.exp_pos _
  have hfar_sum : ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabsT f h n * u n ≤
      F / s ^ 13 * (A * M ^ k) := by
    calc ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabsT f h n * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), aabsT f h n * (F / s ^ 13) :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hfar n hn) (aabsT_nonneg f _ _)
      _ ≤ ∑ n ∈ range (N + 1), aabsT f h n * (F / s ^ 13) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun n _ _ => mul_nonneg (aabsT_nonneg f _ _) (by positivity))
      _ = F / s ^ 13 * ∑ n ∈ range (N + 1), aabsT f h n := by rw [← sum_mul]; ring
      _ ≤ F / s ^ 13 * (A * M ^ k) := by gcongr; exact hA h N
  -- the near part
  have hnear_sub : (range (N + 1)).filter (fun n => ¬ n + D ≤ N) ⊆ insert 0 (Ioc (N - D) N) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_filter.1 hn
    rw [mem_range] at h1
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_Ioc.2 ⟨by omega, by omega⟩)
  have hnear_sum : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabsT f h n * u n ≤
      M ^ (k - 1) * (c * D + 2 * C * M ^ (1 - ηt)) := by
    have ha0 : aabsT f h 0 = 0 := aabsT_zero f h
    calc ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabsT f h n * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), aabsT f h n := by
          refine sum_le_sum fun n hn => ?_
          have hn' : (n : ℝ) < x := by
            have := mem_range.1 (mem_filter.1 hn).1; rw [hxdef]; exact_mod_cast this
          have : u n ≤ 1 :=
            Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
          have := aabsT_nonneg f h n
          nlinarith
      _ ≤ ∑ n ∈ insert 0 (Ioc (N - D) N), aabsT f h n :=
          sum_le_sum_of_subset_of_nonneg hnear_sub (fun n _ _ => aabsT_nonneg f _ _)
      _ = aabsT f h 0 + ∑ n ∈ Ioc (N - D) N, aabsT f h n := by
          rw [sum_insert (by simp)]
      _ = ∑ n ∈ Ioc (N - D) N, aabsT f h n := by rw [ha0, zero_add]
      _ ≤ ∑ n ∈ Ioc (N - D) N, (lsqT f n + lsqT f (n + h)) / 2 * M ^ (k - 1) := by
          refine sum_le_sum fun n hn => (aabsT_le_lsq f h n).trans ?_
          have : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.1 hn).2
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _)
            (div_nonneg (add_nonneg (lsqT_nonneg f n) (lsqT_nonneg f _)) zero_le_two)
          rw [hMdef]; linarith
      _ = ((SlamT f N - SlamT f (N - D)) + (SlamT f (N + h) - SlamT f (N - D + h))) / 2 *
            M ^ (k - 1) := by
          have hS1 : ∑ n ∈ Ioc (N - D) N, lsqT f n = SlamT f N - SlamT f (N - D) := by
            unfold SlamT; rw [sum_Icc_eq_Slam_sub _ _ _ (Nat.sub_le N D)]
          have hS2 : ∑ n ∈ Ioc (N - D) N, lsqT f (n + h) =
              SlamT f (N + h) - SlamT f (N - D + h) := by
            have : ∑ n ∈ Ioc (N - D) N, lsqT f (n + h) =
                ∑ m ∈ Ioc (N - D + h) (N + h), lsqT f m := by
              have hset : Ioc (N - D + h) (N + h) = (Ioc (N - D) N).map (addRightEmbedding h) := by
                ext m; simp only [mem_map, mem_Ioc, addRightEmbedding_apply]
                constructor
                · intro hm; exact ⟨m - h, by omega, by omega⟩
                · rintro ⟨n, ⟨h1, h2⟩, rfl⟩; omega
              rw [hset, sum_map]; rfl
            rw [this]; unfold SlamT; rw [sum_Icc_eq_Slam_sub _ _ _ (by omega)]
          rw [← sum_mul, ← sum_div, sum_add_distrib, hS1, hS2]
      _ ≤ ((c * ((N : ℝ) - ((N - D : ℕ) : ℝ)) + 2 * C * (N : ℝ) ^ (1 - ηt)) +
            (c * (((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ)) +
              2 * C * ((N + h : ℕ) : ℝ) ^ (1 - ηt))) / 2 * M ^ (k - 1) := by
          gcongr
          · exact hRS _ _ (Nat.sub_le N D)
          · exact hRS _ _ (by omega)
      _ ≤ (2 * (c * D) + 2 * (2 * C * M ^ (1 - ηt))) / 2 * M ^ (k - 1) := by
          have hsub : (N : ℝ) - ((N - D : ℕ) : ℝ) ≤ D := by
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hsub2 : ((N + h : ℕ) : ℝ) - ((N - D + h : ℕ) : ℝ) ≤ D := by
            push_cast
            rcases le_total D N with hDN | hDN
            · rw [Nat.cast_sub hDN]; linarith
            · rw [Nat.sub_eq_zero_of_le hDN]; simp; exact_mod_cast hDN
          have hpN : (N : ℝ) ^ (1 - ηt) ≤ M ^ (1 - ηt) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
          have hpNh : ((N + h : ℕ) : ℝ) ^ (1 - ηt) = M ^ (1 - ηt) := by push_cast; rfl
          rw [hpNh]
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num))
            (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hsub hc0, mul_le_mul_of_nonneg_left hsub2 hc0,
            mul_le_mul_of_nonneg_left hpN (by positivity : (0 : ℝ) ≤ 2 * C)]
      _ = M ^ (k - 1) * (c * D + 2 * C * M ^ (1 - ηt)) := by ring
  -- combine
  have herr : |∑ n ∈ range (N + 1), aT f h n * (u n * (2 - u n))| ≤
      2 * (F / s ^ 13 * (A * M ^ k) + M ^ (k - 1) * (c * D + 2 * C * M ^ (1 - ηt))) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e : ∀ n ∈ range (N + 1), |aT f h n * (u n * (2 - u n))| ≤ 2 * (aabsT f h n * u n) := by
      intro n hn
      have hn' : (n : ℝ) < x := by
        have := mem_range.1 hn; rw [hxdef]; exact_mod_cast this
      have hu1 : u n ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
      have := hu0 n
      rw [abs_mul, abs_aT, abs_of_nonneg (by nlinarith)]
      have ha := aabsT_nonneg f h n
      nlinarith [mul_nonneg ha (sq_nonneg (u n))]
    refine (sum_le_sum e).trans ?_
    rw [← mul_sum, ← sum_filter_add_sum_filter_not (range (N + 1)) (fun n => n + D ≤ N)]
    gcongr
  -- numerics
  have hsinv : F / s ^ 13 ≤ 2 * F * M ^ (-ηt) := by
    have hs10 : s ^ 13 = x ^ ηt := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; unfold ηt; norm_num
    rw [hs10]
    have h2 : (M / 2) ^ ηt ≤ x ^ ηt := Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    have h3 : (M / 2) ^ ηt = M ^ ηt / 2 ^ ηt := Real.div_rpow hM0.le (by norm_num) _
    have h4 : (2 : ℝ) ^ ηt ≤ 2 := by
      calc (2 : ℝ) ^ ηt ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by simp
    have hMρ : 0 < M ^ ηt := Real.rpow_pos_of_pos hM0 _
    have hxη : 0 < x ^ ηt := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hM0.le, div_le_iff₀ hxη]
    have : M ^ ηt ≤ 2 * x ^ ηt := by
      rw [h3, div_le_iff₀ (by positivity)] at h2; nlinarith
    calc F = 2 * F * (M ^ ηt)⁻¹ * (M ^ ηt / 2) := by field_simp
      _ ≤ 2 * F * (M ^ ηt)⁻¹ * x ^ ηt := by gcongr; linarith
  have hDM : (D : ℝ) ≤ 2 * M ^ (1 - ηt) := by
    have h1 : x ^ (1 - ηt) ≤ M ^ (1 - ηt) := Real.rpow_le_rpow hx0.le hxM (by linarith)
    have h2 : 1 ≤ M ^ (1 - ηt) := Real.one_le_rpow hM1 (by linarith)
    linarith
  have hM12 : M ^ k * M ^ (-ηt) = M ^ ((k : ℝ) - ηt) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0, sub_eq_add_neg]
  have hM11 : M ^ (k - 1) * M ^ (1 - ηt) = M ^ ((k : ℝ) - ηt) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0, Nat.cast_sub hk1]
    congr 1; push_cast; ring
  have hMp : 0 ≤ M ^ ((k : ℝ) - ηt) := (Real.rpow_pos_of_pos hM0 _).le
  have hxk : x ^ ((k : ℝ) - ηt) ≤ M ^ ((k : ℝ) - ηt) :=
    Real.rpow_le_rpow hx0.le hxM (by linarith)
  rw [hdec]
  calc |(∑ n ∈ range (N + 1), aT f h n * (1 - u n) ^ 2) +
        ∑ n ∈ range (N + 1), aT f h n * (u n * (2 - u n))|
      ≤ |∑ n ∈ range (N + 1), aT f h n * (1 - u n) ^ 2| +
          |∑ n ∈ range (N + 1), aT f h n * (u n * (2 - u n))| := abs_add_le _ _
    _ ≤ C₁ * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ ((k : ℝ) - ηt) + 2 * ((2 * F * M ^ (-ηt)) * (A * M ^ k) +
          M ^ (k - 1) * (c * (2 * M ^ (1 - ηt)) + 2 * C * M ^ (1 - ηt))) := by
        gcongr
        · exact hRb.trans (by gcongr)
        · refine herr.trans ?_
          gcongr
    _ = (C₁ * (h : ℝ) ^ (1 / 21 : ℝ) + 4 * F * A + 4 * c + 4 * C) * M ^ ((k : ℝ) - ηt) := by
        have e1 : (2 * F * M ^ (-ηt)) * (A * M ^ k) = 2 * F * A * (M ^ k * M ^ (-ηt)) := by ring
        have e2 : M ^ (k - 1) * (c * (2 * M ^ (1 - ηt)) + 2 * C * M ^ (1 - ηt)) =
            (2 * c + 2 * C) * (M ^ (k - 1) * M ^ (1 - ηt)) := by ring
        rw [e1, e2, hM12, hM11]; ring
    _ ≤ (C₁ + 8 * F * A + 4 * c + 4 * C) * (h : ℝ) ^ (1 / 21 : ℝ) * M ^ ((k : ℝ) - ηt) := by
        have : C₁ * (h : ℝ) ^ (1 / 21 : ℝ) + 4 * F * A + 4 * c + 4 * C ≤
            (C₁ + 8 * F * A + 4 * c + 4 * C) * (h : ℝ) ^ (1 / 21 : ℝ) := by
          have : 0 ≤ 8 * F * A + 4 * c + 4 * C := by positivity
          nlinarith
        nlinarith

end RamanujanTau.SubconvexGeneral3
