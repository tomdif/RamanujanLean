/-
# Item 4 (part 2): Rankin input along the progression `a ∣ bn + ℓ`, and sharp sums of `cR`

* `sum_cAR_sq_le`: `Σ_{L<n≤U} cA(a,bn+ℓ)² ≤ Σ_{m₁<m≤m₂} τ(m)²`, `m₁ = ⌊(bL+ℓ)/a⌋`,
  `m₂ = ⌊(bU+ℓ)/a⌋` (`n ↦ (bn+ℓ)/a` is injective), with `m₂ − m₁ ≤ b(U−L) + 1`;
* `short_cR`: `Σ_{N−D<n≤N} |cR n| ≤ (b+1)¹² (c + 2C) x¹¹ (D + x^{1−1/21})`, `x = N+1`, `ℓ ≤ x`;
* `sum_cR_cs`: Cauchy–Schwarz, `Σ_{n≤N} |cR n| ≤ A N⁶ ((bN+ℓ)/a)⁶` (all `N`);
* **`AsumAB_bound`**: `|Σ_{n≤N} cR(n)| ≤ K ℓ^{1/21} (b+1)¹² (N+1)^{12−1/21}` for `1 ≤ ℓ ≤ N+1`.
-/
import RamanujanTau.SCS2Coprime.TauberGen

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError RamanujanTau.SCSProof
  RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped Real

lemma cAR_natCast (a : ℕ+) (k : ℕ) :
    cAR a (k : ℤ) = if (a : ℕ) ∣ k then ((tau (k / a) : ℤ) : ℝ) else 0 := by
  unfold cAR
  by_cases h : (a : ℕ) ∣ k
  · rw [if_pos ⟨Int.natCast_dvd_natCast.2 h, Int.natCast_nonneg _⟩, if_pos h]
    congr 3
  · rw [if_neg (fun h' => h (Int.natCast_dvd_natCast.1 h'.1)), if_neg h]

lemma cR_natCast (a b : ℕ+) (ℓ n : ℕ) :
    cR a b ℓ n = ((tau n : ℤ) : ℝ) * cAR a ((b * n + ℓ : ℕ) : ℤ) := by
  unfold cR; push_cast; rfl

lemma cR_zero (a b : ℕ+) (ℓ : ℤ) : cR a b ℓ 0 = 0 := by
  simp [cR, RamanujanTau.tau_zero]

/-- The progression injection. -/
theorem sum_cAR_sq_le (a b : ℕ+) (ℓ L U : ℕ) :
    ∑ n ∈ Ioc L U, cAR a ((b * n + ℓ : ℕ) : ℤ) ^ 2 ≤
      ∑ m ∈ Ioc ((b * L + ℓ) / a) ((b * U + ℓ) / a), ((tau m : ℤ) : ℝ) ^ 2 := by
  set S := (Ioc L U).filter (fun n => (a : ℕ) ∣ b * n + ℓ)
  have ha : 0 < (a : ℕ) := a.pos
  have hb : 0 < (b : ℕ) := b.pos
  have e1 : ∑ n ∈ Ioc L U, cAR a ((b * n + ℓ : ℕ) : ℤ) ^ 2 =
      ∑ n ∈ S, ((tau ((b * n + ℓ) / a) : ℤ) : ℝ) ^ 2 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    rw [cAR_natCast]
    split_ifs <;> simp
  rw [e1]
  have hinj : Set.InjOn (fun n => (b * n + ℓ) / (a : ℕ)) (S : Set ℕ) := by
    intro n hn n' hn' h
    simp only [S, coe_filter, Set.mem_setOf_eq] at hn hn'
    have h1 := Nat.div_mul_cancel hn.2
    have h2 := Nat.div_mul_cancel hn'.2
    simp only at h
    rw [h] at h1
    have : (b : ℕ) * n = b * n' := by omega
    exact Nat.eq_of_mul_eq_mul_left hb this
  rw [← sum_image (f := fun m => ((tau m : ℤ) : ℝ) ^ 2) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro m hm
  simp only [mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  simp only [S, mem_filter, mem_Ioc] at hn
  obtain ⟨⟨hLn, hnU⟩, hdvd⟩ := hn
  rw [mem_Ioc]
  constructor
  · have h1 := Nat.div_mul_cancel hdvd
    have h2 := Nat.div_mul_le_self (b * L + ℓ) a
    have h3 : b * L + ℓ < b * n + ℓ := by
      have := Nat.mul_lt_mul_of_pos_left hLn hb; omega
    have : (b * L + ℓ) / a * a < (b * n + ℓ) / a * a := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  · exact Nat.div_le_div_right (by have := Nat.mul_le_mul_left (b : ℕ) hnU; omega)

lemma div_sub_div_le (a b : ℕ+) (ℓ L U : ℕ) (hLU : L ≤ U) :
    (((b * U + ℓ) / a : ℕ) : ℝ) - (((b * L + ℓ) / a : ℕ) : ℝ) ≤ b * ((U : ℝ) - L) + 1 := by
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  set m₂ := (b * U + ℓ) / (a : ℕ)
  set m₁ := (b * L + ℓ) / (a : ℕ)
  have h2 : m₂ * a ≤ b * U + ℓ := Nat.div_mul_le_self _ _
  have h1 : b * L + ℓ < (m₁ + 1) * a := by
    have := Nat.lt_div_mul_add (a := b * L + ℓ) a.pos
    simp only [m₁]; linarith
  have h2' : (m₂ : ℝ) * a ≤ b * U + ℓ := by exact_mod_cast h2
  have h1' : (b : ℝ) * L + ℓ < (m₁ + 1) * a := by exact_mod_cast h1
  have hm : ((m₂ : ℝ) - m₁ - 1) * a < b * ((U : ℝ) - L) := by nlinarith
  have hb0 : (0 : ℝ) ≤ b * ((U : ℝ) - L) := by
    have : (L : ℝ) ≤ U := by exact_mod_cast hLU
    exact mul_nonneg (by positivity) (by linarith)
  by_contra hcon
  push Not at hcon
  have : b * ((U : ℝ) - L) < (m₂ : ℝ) - m₁ - 1 := by linarith
  nlinarith

lemma tau_sq_le_lam (m : ℕ) {X : ℝ} (hm : (m : ℝ) ≤ X) :
    ((tau m : ℤ) : ℝ) ^ 2 ≤ lam m ^ 2 * X ^ 11 := by
  have := lam_sq_eq m
  push_cast at this ⊢
  rw [this]
  gcongr

lemma sum_tau_sq_Ioc_le (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) {X : ℝ} (hX : (m₂ : ℝ) ≤ X) :
    ∑ m ∈ Ioc m₁ m₂, ((tau m : ℤ) : ℝ) ^ 2 ≤ X ^ 11 * (Slam m₂ - Slam m₁) := by
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) hX
  calc ∑ m ∈ Ioc m₁ m₂, ((tau m : ℤ) : ℝ) ^ 2 ≤ ∑ m ∈ Ioc m₁ m₂, lam m ^ 2 * X ^ 11 :=
        sum_le_sum fun m hm => tau_sq_le_lam m
          (le_trans (by exact_mod_cast (mem_Ioc.1 hm).2) hX)
    _ = X ^ 11 * (Slam m₂ - Slam m₁) := by
        rw [← sum_mul, mul_comm]; unfold Slam; rw [sum_Icc_eq_Slam_sub _ _ _ h]

lemma rpow_le_self_of_one_le {B : ℝ} (hB : 1 ≤ B) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    B ^ e ≤ B := by
  calc B ^ e ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB he1
    _ = B := Real.rpow_one B

set_option maxHeartbeats 4000000 in
/-- **Short sums of `|cR|`.** -/
theorem short_cR : ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ (a b : ℕ+) (ℓ N : ℕ), (ℓ : ℝ) ≤ (N : ℝ) + 1 →
    ∀ D : ℕ, ∑ n ∈ Ioc (N - D) N, |cR a b ℓ n| ≤
      ((b : ℝ) + 1) ^ 12 * (c + 2 * C) * ((N : ℝ) + 1) ^ 11 * (D + ((N : ℝ) + 1) ^ (1 - ηt)) := by
  obtain ⟨c, C, hc0, hC0, hRS⟩ := rankin_shortT
  refine ⟨c, C, hc0, hC0, fun a b ℓ N hℓ D => ?_⟩
  set x : ℝ := (N : ℝ) + 1 with hxdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  set B : ℝ := (b : ℝ) + 1
  have hB1 : 1 ≤ B := by linarith
  have hη := ηt_pos; have hη2 := ηt_le
  have hxe : 1 ≤ x ^ (1 - ηt) := Real.one_le_rpow hx1 (by linarith)
  set L := N - D
  have hLN : L ≤ N := Nat.sub_le N D
  have hUL : (N : ℝ) - L ≤ D := by
    rcases le_total D N with h | h
    · simp only [L]; rw [Nat.cast_sub h]; linarith
    · simp only [L]; rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h
  -- split `|τ(n) cA| ≤ (τ(n)² + cA²)/2`
  have hsplit : ∑ n ∈ Ioc L N, |cR a b ℓ n| ≤
      (∑ n ∈ Ioc L N, ((tau n : ℤ) : ℝ) ^ 2 +
        ∑ n ∈ Ioc L N, cAR a ((b * n + ℓ : ℕ) : ℤ) ^ 2) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_le_sum fun n _ => ?_
    have := abs_cR_le a b ℓ n
    push_cast at this ⊢
    exact this
  -- the `n`-part
  have hn : ∑ n ∈ Ioc L N, ((tau n : ℤ) : ℝ) ^ 2 ≤ x ^ 11 * (c * D + 2 * C * x ^ (1 - ηt)) := by
    refine (sum_tau_sq_Ioc_le L N hLN (X := x) (by linarith)).trans ?_
    gcongr
    refine (hRS L N hLN).trans ?_
    have : (N : ℝ) ^ (1 - ηt) ≤ x ^ (1 - ηt) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
    have : c * ((N : ℝ) - L) ≤ c * D := mul_le_mul_of_nonneg_left hUL hc0
    nlinarith
  -- the `m`-part
  set m₁ := (b * L + ℓ) / (a : ℕ)
  set m₂ := (b * N + ℓ) / (a : ℕ)
  have hm12 : m₁ ≤ m₂ := Nat.div_le_div_right (by
    have := Nat.mul_le_mul_left (b : ℕ) hLN; omega)
  have hm2X : (m₂ : ℝ) ≤ B * x := by
    have h1 : (m₂ : ℝ) ≤ ((b * N + ℓ : ℕ) : ℝ) / a := Nat.cast_div_le
    have h2 : ((b * N + ℓ : ℕ) : ℝ) / a ≤ ((b * N + ℓ : ℕ) : ℝ) :=
      div_le_self (Nat.cast_nonneg _) ha1
    have h3 : ((b * N + ℓ : ℕ) : ℝ) = b * N + ℓ := by push_cast; ring
    have : (b : ℝ) * N + ℓ ≤ B * x := by simp only [B]; nlinarith
    linarith
  have hm : ∑ n ∈ Ioc L N, cAR a ((b * n + ℓ : ℕ) : ℤ) ^ 2 ≤
      (B * x) ^ 11 * (c * (b * D + 1) + 2 * C * (B * x) ^ (1 - ηt)) := by
    refine (sum_cAR_sq_le a b ℓ L N).trans ((sum_tau_sq_Ioc_le m₁ m₂ hm12 hm2X).trans ?_)
    gcongr
    refine (hRS m₁ m₂ hm12).trans ?_
    have hd := div_sub_div_le a b ℓ L N hLN
    have hd' : (m₂ : ℝ) - m₁ ≤ b * D + 1 := hd.trans (by gcongr)
    have : (m₂ : ℝ) ^ (1 - ηt) ≤ (B * x) ^ (1 - ηt) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hm2X (by linarith)
    have : c * ((m₂ : ℝ) - m₁) ≤ c * (b * D + 1) := mul_le_mul_of_nonneg_left hd' hc0
    nlinarith
  -- numerics
  have hBx : (B * x) ^ (1 - ηt) ≤ B * x ^ (1 - ηt) := by
    rw [Real.mul_rpow (by linarith) hx0.le]
    gcongr
    exact rpow_le_self_of_one_le hB1 (by linarith) (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have k1 : c * D + 2 * C * x ^ (1 - ηt) ≤ (c + 2 * C) * (D + x ^ (1 - ηt)) := by nlinarith
  have k2 : c * (b * D + 1) + 2 * C * (B * x) ^ (1 - ηt) ≤
      B * ((c + 2 * C) * (D + x ^ (1 - ηt))) := by
    have : c * (b * D + 1) ≤ c * (B * D + B * x ^ (1 - ηt)) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      simp only [B]; nlinarith
    have : 2 * C * (B * x) ^ (1 - ηt) ≤ 2 * C * (B * x ^ (1 - ηt)) := by gcongr
    nlinarith
  have hx11 : 0 ≤ x ^ 11 := by positivity
  have hB11 : 1 ≤ B ^ 11 := one_le_pow₀ hB1
  have hQ : 0 ≤ (c + 2 * C) * (D + x ^ (1 - ηt)) := by positivity
  calc ∑ n ∈ Ioc L N, |cR a b ℓ n|
      ≤ (x ^ 11 * (c * D + 2 * C * x ^ (1 - ηt)) +
          (B * x) ^ 11 * (c * (b * D + 1) + 2 * C * (B * x) ^ (1 - ηt))) / 2 := by
        refine hsplit.trans ?_; gcongr
    _ ≤ (x ^ 11 * ((c + 2 * C) * (D + x ^ (1 - ηt))) +
          (B * x) ^ 11 * (B * ((c + 2 * C) * (D + x ^ (1 - ηt))))) / 2 := by gcongr
    _ = (1 + B ^ 12) / 2 * (x ^ 11 * ((c + 2 * C) * (D + x ^ (1 - ηt)))) := by ring
    _ ≤ B ^ 12 * (x ^ 11 * ((c + 2 * C) * (D + x ^ (1 - ηt)))) := by
        gcongr
        have : 1 ≤ B ^ 12 := one_le_pow₀ hB1
        linarith
    _ = _ := by ring

/-- **Cauchy–Schwarz bound**, all `N`: `Σ_{n≤N} |cR n| ≤ A N⁶ ((bN+ℓ)/a)⁶`. -/
theorem sum_cR_cs : ∃ A : ℝ, 0 ≤ A ∧ ∀ (a b : ℕ+) (ℓ N : ℕ),
    ∑ n ∈ range (N + 1), |cR a b ℓ n| ≤
      A * (N : ℝ) ^ 6 * (((b : ℝ) * N + ℓ) / a) ^ 6 := by
  obtain ⟨c, C, hc0, hC0, hRS⟩ := rankin_shortT
  have hSl : ∀ M : ℕ, Slam M ≤ (c + 2 * C) * M := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [Slam]
    have h := hRS 0 M (Nat.zero_le _)
    have h0 : Slam 0 = 0 := by simp [Slam]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have : (M : ℝ) ^ (1 - ηt) ≤ M := rpow_le_self_of_one_le hM1
      (by have := ηt_le; linarith) (by have := ηt_pos; linarith)
    rw [h0] at h; push_cast at h
    nlinarith
  refine ⟨c + 2 * C, by positivity, fun a b ℓ N => ?_⟩
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast a.one_le
  have hr : range (N + 1) = insert 0 (Ioc 0 N) := by
    ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
  rw [hr, sum_insert (by simp), cR_zero, abs_zero, zero_add]
  set f : ℕ → ℝ := fun n => |((tau n : ℤ) : ℝ)|
  set g : ℕ → ℝ := fun n => |cAR a ((b * n + ℓ : ℕ) : ℤ)|
  have hfg : ∀ n, |cR a b ℓ n| = f n * g n := fun n => by
    rw [cR_natCast, abs_mul]
  simp_rw [hfg]
  set Mr : ℝ := ((b : ℝ) * N + ℓ) / a
  have hMr0 : 0 ≤ Mr := by positivity
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc 0 N) f g
  have hF : ∑ n ∈ Ioc 0 N, f n ^ 2 ≤ (c + 2 * C) * (N : ℝ) ^ 12 := by
    simp_rw [f, sq_abs]
    refine (sum_tau_sq_Ioc_le 0 N (Nat.zero_le _) le_rfl).trans ?_
    have h0 : Slam 0 = 0 := by simp [Slam]
    rw [h0, sub_zero]
    calc (N : ℝ) ^ 11 * Slam N ≤ (N : ℝ) ^ 11 * ((c + 2 * C) * N) := by gcongr; exact hSl N
      _ = _ := by ring
  have hG : ∑ n ∈ Ioc 0 N, g n ^ 2 ≤ (c + 2 * C) * Mr ^ 12 := by
    simp_rw [g, sq_abs]
    refine (sum_cAR_sq_le a b ℓ 0 N).trans ?_
    set m₂ := (b * N + ℓ) / (a : ℕ)
    have hm2 : (m₂ : ℝ) ≤ Mr := by
      have h1 : (m₂ : ℝ) ≤ ((b * N + ℓ : ℕ) : ℝ) / a := Nat.cast_div_le
      have h3 : ((b * N + ℓ : ℕ) : ℝ) = b * N + ℓ := by push_cast; ring
      rw [h3] at h1; exact h1
    have hm12 : (b * 0 + ℓ) / (a : ℕ) ≤ m₂ := Nat.div_le_div_right (by omega)
    refine (sum_tau_sq_Ioc_le _ m₂ hm12 hm2).trans ?_
    have hS0 : 0 ≤ Slam ((b * 0 + ℓ) / (a : ℕ)) :=
      sum_nonneg fun _ _ => sq_nonneg _
    calc Mr ^ 11 * (Slam m₂ - Slam ((b * 0 + ℓ) / (a : ℕ))) ≤ Mr ^ 11 * Slam m₂ := by
          gcongr; linarith
      _ ≤ Mr ^ 11 * ((c + 2 * C) * Mr) := by
          gcongr; exact (hSl m₂).trans (by gcongr)
      _ = _ := by ring
  have hsq : (∑ n ∈ Ioc 0 N, f n * g n) ^ 2 ≤
      ((c + 2 * C) * (N : ℝ) ^ 6 * Mr ^ 6) ^ 2 := by
    refine hcs.trans ?_
    calc (∑ n ∈ Ioc 0 N, f n ^ 2) * (∑ n ∈ Ioc 0 N, g n ^ 2)
        ≤ ((c + 2 * C) * (N : ℝ) ^ 12) * ((c + 2 * C) * Mr ^ 12) :=
          mul_le_mul hF hG (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ n ∈ Ioc 0 N, f n * g n :=
    sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 hsq

set_option maxHeartbeats 4000000 in
/-- **Sharp sums of `cR`** (from `pointwise_Gc`, `AsumC_bound`, `short_cR`). -/
theorem AsumAB_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℕ+) (ℓ N : ℕ), 1 ≤ ℓ → (ℓ : ℝ) ≤ (N : ℝ) + 1 →
    |AsumC (cR a b ℓ) N| ≤
      K * (ℓ : ℝ) ^ (1 / 21 : ℝ) * ((b : ℝ) + 1) ^ 12 * ((N : ℝ) + 1) ^ (12 - ηt) := by
  obtain ⟨Kp, hKp0, hKp⟩ := pointwise_Gc
  obtain ⟨c, C, hc0, hC0, hS⟩ := short_cR
  obtain ⟨C₀, hC₀, hT⟩ := cR_laplace
  set F : ℝ := (Nat.factorial 13 : ℝ)
  refine ⟨Real.exp 1 * 48 * I2 * Kp + 2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)),
    by have := I2_nonneg; positivity, fun a b ℓ N hℓ hℓN => ?_⟩
  set x : ℝ := (N : ℝ) + 1 with hxdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.one_le
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hη := ηt_pos; have hη2 := ηt_le
  set B : ℝ := (b : ℝ) + 1
  have hB1 : 1 ≤ B := by linarith
  set A₂ : ℝ := B ^ 12 * (c + 2 * C)
  have hA20 : 0 ≤ A₂ := by positivity
  set Kc : ℝ := Kp * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (b : ℝ) ^ 12
  have hKc : 0 ≤ Kc := by positivity
  have hpt : ∀ v : ℝ, ‖Gc (cR a b ℓ) (((1 / x : ℝ) : ℂ) + v * Complex.I)‖ ≤
      Kc * (|2 * v / (1 / x)| + 3) * (1 / x) ^ (-(11901 / 1000 : ℝ)) := by
    intro v
    have h := hKp a b ℓ hℓ (1 / x) v (by positivity) ((div_le_one hx0).2 hx1 |>.trans hb1)
      (by rw [mul_one_div, div_le_iff₀ hx0]; nlinarith)
    exact h.trans (le_of_eq (by ring))
  have hsum := (hT a b ℓ (1 / x) (by positivity)).1
  have hSx : ∀ D : ℕ, ∑ n ∈ Ioc (N - D) N, |cR a b ℓ n| ≤
      A₂ * x ^ 11 * (D + x ^ (1 - ηt)) := by
    intro D
    exact hS a b ℓ N hℓN D
  have hAx : ∑ n ∈ range (N + 1), |cR a b ℓ n| ≤ (2 * A₂) * x ^ 12 := by
    have hr : range (N + 1) = insert 0 (Ioc (N - N) N) := by
      ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
    rw [hr, sum_insert (by simp), cR_zero, abs_zero, zero_add]
    refine (hSx N).trans ?_
    have h1 : x ^ (1 - ηt) ≤ x := rpow_le_self_of_one_le hx1 (by linarith) (by linarith)
    have hN : (N : ℝ) ≤ x := by linarith
    have : (N : ℝ) + x ^ (1 - ηt) ≤ 2 * x := by linarith
    calc A₂ * x ^ 11 * ((N : ℝ) + x ^ (1 - ηt)) ≤ A₂ * x ^ 11 * (2 * x) := by gcongr
      _ = _ := by ring
  have key := AsumC_bound (cR a b ℓ) Kc (2 * A₂) A₂ hKc (by positivity) hA20 (cR_zero a b ℓ) N
    hsum hpt hAx hSx
  refine key.trans ?_
  have hxp : 0 ≤ x ^ (12 - ηt) := by positivity
  have hb12 : (b : ℝ) ^ 12 ≤ B ^ 12 := by gcongr; linarith
  have hl : (1 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 21 : ℝ) := Real.one_le_rpow hℓ1 (by norm_num)
  have hB12 : 1 ≤ B ^ 12 := one_le_pow₀ hB1
  have e1 : Real.exp 1 * 48 * I2 * Kc ≤
      Real.exp 1 * 48 * I2 * Kp * ((ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12) := by
    have := I2_nonneg
    simp only [Kc]
    have h0 : 0 ≤ Real.exp 1 * 48 * I2 * Kp * (ℓ : ℝ) ^ (1 / 21 : ℝ) := by positivity
    calc Real.exp 1 * 48 * I2 * (Kp * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (b : ℝ) ^ 12)
        = Real.exp 1 * 48 * I2 * Kp * (ℓ : ℝ) ^ (1 / 21 : ℝ) * (b : ℝ) ^ 12 := by ring
      _ ≤ Real.exp 1 * 48 * I2 * Kp * (ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12 := by gcongr
      _ = _ := by ring
  have e2 : 2 * (F * (2 * A₂) + 3 * A₂) ≤
      2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)) * ((ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12) := by
    have h0 : 0 ≤ 2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)) := by positivity
    calc 2 * (F * (2 * A₂) + 3 * A₂) = 2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)) * B ^ 12 := by
          simp only [A₂]; ring
      _ ≤ 2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)) * ((ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12) := by
          gcongr; nlinarith
  calc (Real.exp 1 * 48 * I2 * Kc + 2 * (F * (2 * A₂) + 3 * A₂)) * x ^ (12 - ηt)
      ≤ (Real.exp 1 * 48 * I2 * Kp * ((ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12) +
          2 * (F * (2 * (c + 2 * C)) + 3 * (c + 2 * C)) * ((ℓ : ℝ) ^ (1 / 21 : ℝ) * B ^ 12)) *
          x ^ (12 - ηt) := by gcongr
    _ = _ := by ring

end RamanujanTau.SCS2Coprime
