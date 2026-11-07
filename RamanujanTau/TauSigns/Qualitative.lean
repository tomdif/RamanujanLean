/-
# τ(n) changes sign infinitely often

`tau_sign_changes : ∀ N, ∃ m n, N ≤ m ∧ N ≤ n ∧ 0 < τ m ∧ τ n < 0`.

Route (no L-function, no Landau theorem): on the imaginary axis
`Δ(iy) = ∑ τ(n) e^{-2πny}`, and `Δ(-1/z) = z¹² Δ(z)` gives `Δ(iy) = y^{-12} Δ(i/y)`.
By cusp decay `Δ(i/y) = O(e^{-2π/y})`, so `Δ(iy)` stays bounded as `y → 0⁺`.
If `±τ(n) ≥ 0` for `n ≥ N`, then for `K` large and `y = 1/(2πK)`,
`e^{-1} ∑_{N ≤ n ≤ K} |τ(n)| ≤ ∑_{N ≤ n ≤ K} ±τ(n) e^{-2πny} ≤ B + ∑_{n<N} |τ(n)|`,
so `∑_{n ≥ N} |τ(n)| < ∞`.  But `τ(m²) ≠ 0` for every `m ≥ 1` (`TauDensity.tau_sq_ne_zero`),
and `τ` is integer-valued, so that sum diverges.
-/
import RamanujanTau.RankinSelberg.Upper
import RamanujanTau.TauDensity.Structure

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Complex ModularForm Finset Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups Real
open RamanujanTau.RankinSelberg

local notation "𝕢" => Function.Periodic.qParam

lemma qParam_iy (y : ℝ) : 𝕢 1 (((0 : ℝ) : ℂ) + y * I) = ((Real.exp (-2 * π * y) : ℝ) : ℂ) := by
  unfold Function.Periodic.qParam
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- `Δ(iy) = ∑ τ(n) e^{-2πny}` (real form). -/
lemma hasSum_tau_iy {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (tau n : ℝ) * Real.exp (-2 * π * y) ^ n) (Δf (hp hy 0)).re := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL
  have h := hasSum_qExpansion one_pos hper
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
    (ModularFormClass.bdd_at_infty (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) (hp hy 0)
  have h2 := Complex.reCLM.hasSum h
  refine h2.congr_fun fun n => ?_
  simp only [Complex.reCLM_apply, TauBound.qExpansion_discriminant_coeff_tau, smul_eq_mul,
    hp_coe, qParam_iy]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `|Δ(z)| = |Δ(-1/z)| / |z|¹²`. -/
lemma norm_Δ_S (z : ℍ) : ‖Δf z‖ = ‖Δf (ModularGroup.S • z)‖ / ‖(z : ℂ)‖ ^ 12 := by
  have h := congrFun discriminant_S_invariant z
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  show ‖discriminant z‖ = ‖discriminant (ModularGroup.S • z)‖ / ‖(z : ℂ)‖ ^ 12
  rw [← h, norm_mul, norm_zpow]
  rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast, div_eq_mul_inv]

/-- **`Δ(iy)` is bounded as `y → 0⁺`.** -/
theorem exists_Δ_iy_bdd : ∃ y₀ : ℝ, 0 < y₀ ∧ ∃ B : ℝ, ∀ {y : ℝ} (hy : 0 < y), y ≤ y₀ →
    ‖Δf (hp hy 0)‖ ≤ B := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  set A' := max A 1
  refine ⟨1 / A', by positivity, C * (Nat.factorial 12 : ℝ) / (2 * π) ^ 12, ?_⟩
  intro y hy hyy
  have hA'pos : 0 < A' := by positivity
  set z := hp hy 0
  have hzn : ‖(z : ℂ)‖ = y := by
    rw [hp_coe]; simp [abs_of_pos hy]
  have hSim : (ModularGroup.S • z).im = 1 / y := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_S, hp_im,
      Complex.normSq_eq_norm_sq, hzn]
    field_simp
  have hge : A ≤ (ModularGroup.S • z).im := by
    rw [hSim]
    have : A' ≤ 1 / y := by
      rw [le_div_iff₀ hy]; rw [le_div_iff₀ hA'pos] at hyy; linarith
    exact le_trans (le_max_left _ _) this
  have hb := hA _ hge
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hb
  rw [hSim] at hb
  rw [norm_Δ_S, hzn]
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have := lt_of_le_of_lt hb (mul_neg_of_neg_of_pos hneg (Real.exp_pos _))
    exact absurd this (not_lt.mpr (norm_nonneg _))
  -- e^{2π/y} ≥ (2π/y)^12/12!
  have hexp := Real.pow_div_factorial_le_exp (x := 2 * π * (1 / y)) (by positivity) 12
  have hkey : Real.exp (-2 * π * (1 / y) / 1) ≤ (Nat.factorial 12 : ℝ) / (2 * π) ^ 12 * y ^ 12 := by
    rw [div_one, show -2 * π * (1 / y) = -(2 * π * (1 / y)) by ring, Real.exp_neg]
    have hpos : 0 < (2 * π * (1 / y)) ^ 12 / (Nat.factorial 12 : ℝ) := by positivity
    calc (Real.exp (2 * π * (1 / y)))⁻¹ ≤ ((2 * π * (1 / y)) ^ 12 / (Nat.factorial 12 : ℝ))⁻¹ :=
          inv_anti₀ hpos hexp
      _ = (Nat.factorial 12 : ℝ) / (2 * π) ^ 12 * y ^ 12 := by
          field_simp
  rw [div_le_iff₀ (by positivity)]
  calc ‖Δf (ModularGroup.S • z)‖ ≤ C * Real.exp (-2 * π * (1 / y) / 1) := hb
    _ ≤ C * ((Nat.factorial 12 : ℝ) / (2 * π) ^ 12 * y ^ 12) := by gcongr
    _ = C * (Nat.factorial 12 : ℝ) / (2 * π) ^ 12 * y ^ 12 := by ring

/-- `∑_{N < m ≤ M} 1 ≤ ∑_{N ≤ n ≤ M²} |τ(n)|`, from `τ(m²) ≠ 0`. -/
lemma card_le_sum_abs_tau (N M : ℕ) :
    ((M : ℝ) - N) ≤ ∑ n ∈ Icc N (M ^ 2), |(tau n : ℝ)| := by
  have hsub : (Icc (N + 1) M).image (fun m => m ^ 2) ⊆ Icc N (M ^ 2) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hm
    refine mem_Icc.mpr ⟨?_, Nat.pow_le_pow_left h2 2⟩
    calc N ≤ m := by omega
      _ ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  have hinj : Set.InjOn (fun m : ℕ => m ^ 2) (Icc (N + 1) M) :=
    fun a _ b _ hab => Nat.pow_left_injective (by norm_num) hab
  calc ((M : ℝ) - N) ≤ ((Icc (N + 1) M).card : ℝ) := by
        rw [Nat.card_Icc]
        rcases le_or_gt M N with h | h
        · have : (M : ℝ) ≤ N := by exact_mod_cast h
          have : (0 : ℝ) ≤ ((M + 1 - (N + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        · rw [show M + 1 - (N + 1) = M - N by omega, Nat.cast_sub h.le]
    _ = ∑ m ∈ Icc (N + 1) M, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ Icc (N + 1) M, |(tau (m ^ 2) : ℝ)| := by
        refine sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := by have := (mem_Icc.mp hm).1; omega
        have h0 := TauDensity.tau_sq_ne_zero hm1
        have : (1 : ℤ) ≤ |tau (m ^ 2)| := Int.one_le_abs h0
        rw [← Int.cast_abs]; exact_mod_cast this
    _ = ∑ n ∈ (Icc (N + 1) M).image (fun m => m ^ 2), |(tau n : ℝ)| := by
        rw [sum_image hinj]
    _ ≤ ∑ n ∈ Icc N (M ^ 2), |(tau n : ℝ)| :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _

/-- **No eventual sign.** For `s = ±1`, `s·τ(n) ≥ 0` cannot hold for all `n ≥ N`. -/
theorem not_eventually_signed (s : ℤ) (hs : s = 1 ∨ s = -1) (N : ℕ) :
    ¬ ∀ n, N ≤ n → 0 ≤ s * tau n := by
  intro hN
  obtain ⟨y₀, hy₀, B, hB⟩ := exists_Δ_iy_bdd
  set H : ℝ := ∑ n ∈ range N, |(tau n : ℝ)|
  have hH : 0 ≤ H := sum_nonneg fun _ _ => abs_nonneg _
  set M : ℕ := N + ⌈Real.exp 1 * (|B| + H)⌉₊ + ⌈1 / (2 * π * y₀)⌉₊ + 1
  set K : ℕ := M ^ 2
  have hM1 : (1 : ℝ) ≤ M := by
    have : 1 ≤ M := by omega
    exact_mod_cast this
  have hKM : (M : ℝ) ≤ K := by
    have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K := by linarith
  set y : ℝ := 1 / (2 * π * K)
  have hy : 0 < y := by positivity
  have hyy : y ≤ y₀ := by
    have h1 : 1 / (2 * π * y₀) ≤ (M : ℝ) := by
      have := Nat.le_ceil (1 / (2 * π * y₀))
      have h2 : (⌈1 / (2 * π * y₀)⌉₊ : ℝ) ≤ M := by
        have : ⌈1 / (2 * π * y₀)⌉₊ ≤ M := by omega
        exact_mod_cast this
      linarith
    have h3 : 1 / (2 * π * y₀) ≤ (K : ℝ) := le_trans h1 hKM
    rw [div_le_iff₀ (by positivity)] at h3
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  set r : ℝ := Real.exp (-2 * π * y)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; have := Real.pi_pos; nlinarith
  have hsA : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> simp
  set b : ℕ → ℝ := fun n => (s : ℝ) * ((tau n : ℝ) * r ^ n)
  have hb : HasSum b ((s : ℝ) * (Δf (hp hy 0)).re) := (hasSum_tau_iy hy).mul_left _
  have hnn : ∀ n ∉ range N ∪ Icc N K, 0 ≤ b n := by
    intro n hn
    have hn' : N ≤ n := by
      by_contra h; exact hn (mem_union_left _ (mem_range.mpr (by omega)))
    have h1 : (0 : ℝ) ≤ (s : ℝ) * (tau n : ℝ) := by exact_mod_cast hN n hn'
    have : b n = ((s : ℝ) * (tau n : ℝ)) * r ^ n := by simp only [b]; ring
    rw [this]; exact mul_nonneg h1 (pow_nonneg hr0 n)
  have hle := sum_le_hasSum (range N ∪ Icc N K) hnn hb
  have hdisj : Disjoint (range N) (Icc N K) := by
    rw [disjoint_left]; intro a ha hb'
    have := mem_range.mp ha; have := (mem_Icc.mp hb').1; omega
  rw [sum_union hdisj] at hle
  -- the head is ≥ -H
  have hhead : -H ≤ ∑ n ∈ range N, b n := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun n _ => ?_
    have : |b n| ≤ |(tau n : ℝ)| := by
      simp only [b, abs_mul, hsA, one_mul, abs_pow, abs_of_nonneg hr0]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hr0 hr1)
    linarith [neg_abs_le (b n)]
  -- the total is ≤ |B|
  have htot : (s : ℝ) * (Δf (hp hy 0)).re ≤ |B| := by
    calc (s : ℝ) * (Δf (hp hy 0)).re ≤ |(s : ℝ) * (Δf (hp hy 0)).re| := le_abs_self _
      _ = |(Δf (hp hy 0)).re| := by rw [abs_mul, hsA, one_mul]
      _ ≤ ‖Δf (hp hy 0)‖ := Complex.abs_re_le_norm _
      _ ≤ B := hB hy hyy
      _ ≤ |B| := le_abs_self _
  -- the window is ≥ e^{-1} ∑ |τ|
  have hwin : Real.exp (-1) * ∑ n ∈ Icc N K, |(tau n : ℝ)| ≤ ∑ n ∈ Icc N K, b n := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    have hsg : (s : ℝ) * (tau n : ℝ) = |(tau n : ℝ)| := by
      have h0 : (0 : ℝ) ≤ (s : ℝ) * (tau n : ℝ) := by exact_mod_cast hN n h1
      rw [← abs_of_nonneg h0, abs_mul, hsA, one_mul]
    have hrn : Real.exp (-1) ≤ r ^ n := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hn' : (n : ℝ) ≤ K := by exact_mod_cast h2
      have : (n : ℝ) * (-2 * π * y) = -((n : ℝ) / K) := by
        simp only [y]; field_simp
      rw [this, neg_le_neg_iff, div_le_one hKpos]; exact hn'
    have : b n = ((s : ℝ) * (tau n : ℝ)) * r ^ n := by simp only [b]; ring
    rw [this, hsg, mul_comm]
    exact mul_le_mul_of_nonneg_left hrn (abs_nonneg _)
  have hcard := card_le_sum_abs_tau N M
  have hMN : Real.exp 1 * (|B| + H) + 1 ≤ (M : ℝ) - N := by
    have := Nat.le_ceil (Real.exp 1 * (|B| + H))
    have h2 : ((N + ⌈Real.exp 1 * (|B| + H)⌉₊ + 1 : ℕ) : ℝ) ≤ M := by
      have : N + ⌈Real.exp 1 * (|B| + H)⌉₊ + 1 ≤ M := by omega
      exact_mod_cast this
    push_cast at h2
    linarith
  -- combine: e^{-1}(M - N) ≤ |B| + H
  have hfin : Real.exp (-1) * ((M : ℝ) - N) ≤ |B| + H := by
    have := mul_le_mul_of_nonneg_left hcard (Real.exp_pos (-1)).le
    linarith
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have : Real.exp (-1) * (Real.exp 1 * (|B| + H) + 1) ≤ |B| + H :=
    le_trans (mul_le_mul_of_nonneg_left hMN (Real.exp_pos (-1)).le) hfin
  have hpos := Real.exp_pos (-1)
  nlinarith [abs_nonneg B]

/-- **τ(n) changes sign infinitely often.** -/
theorem tau_sign_changes : ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ N ≤ n ∧ 0 < tau m ∧ tau n < 0 := by
  intro N
  have h1 := not_eventually_signed 1 (Or.inl rfl) N
  have h2 := not_eventually_signed (-1) (Or.inr rfl) N
  push Not at h1 h2
  obtain ⟨n, hn, hn'⟩ := h1
  obtain ⟨m, hm, hm'⟩ := h2
  exact ⟨m, n, hm, hn, by linarith, by linarith⟩

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.exists_Δ_iy_bdd
#print axioms RamanujanTau.TauSigns.tau_sign_changes
