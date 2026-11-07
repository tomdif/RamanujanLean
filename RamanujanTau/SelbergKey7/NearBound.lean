/-
# Seventh pass, R3 (near part): the bound

For `4 ≤ T`, `u ∈ [0, 4T]`, `1 ≤ |ℓ| ≤ K₀ = ⌊T^{1/100}⌋` (`line_bound`):

    ‖Σ_{M₁<m≤M₂} lineTerm(P,Q,ℓ,m) H_ℓ(m)‖ ≤ K (PQ)^{13} T^{401/420 + 1/100 − 49/50},

from `abel_line` with `B` from `abs_lineSum_le` (`scs2_general`, saving `T^{−1/21}`) and the
`H_ℓ` bounds of `Hl_deriv` on `r ≥ T^{399/400}`. Summing over the `≤ 3T^{1/100}` lines and
integrating over `t ∈ [T/2, 3T]` (`near_bound`):

    ‖Σ_{p ∈ Near} ∫ Fq(p)‖ ≤ K (PQ)^{13} T^{1 − 11/2100}.

Level 1.
-/
import RamanujanTau.SelbergKey7.NearAbel

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex Finset RamanujanTau.SelbergKey4 RamanujanTau.SelbergKey5
open scoped Real

lemma one_div_pow_le {T r c : ℝ} (hT : 0 < T) (hr : T ^ c ≤ r) (k : ℕ) :
    1 / r ^ k ≤ T ^ (-((k : ℝ) * c)) := by
  have hTc : 0 < T ^ c := Real.rpow_pos_of_pos hT c
  have h1 : (T ^ c) ^ k ≤ r ^ k := pow_le_pow_left₀ hTc.le hr k
  have e : T ^ (-((k : ℝ) * c)) = 1 / (T ^ c) ^ k := by
    rw [Real.rpow_neg hT.le, mul_comm, Real.rpow_mul hT.le, Real.rpow_natCast, one_div]
  rw [e]
  exact one_div_le_one_div_of_le (pow_pos hTc k) h1

lemma two_rpow_le {T : ℝ} (hT : 4 ≤ T) : 2 * T ^ (1 / 100 : ℝ) ≤ T ^ (399 / 400 : ℝ) := by
  have hT0 : 0 < T := by linarith
  have h1 : T ^ (399 / 400 : ℝ) = T ^ (1 / 100 : ℝ) * T ^ (395 / 400 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have h2 : (2 : ℝ) ≤ T ^ (395 / 400 : ℝ) := by
    have h3 : T ^ (1 / 2 : ℝ) ≤ T ^ (395 / 400 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h4 : (2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hT
    linarith
  rw [h1]
  have : 0 < T ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hT0 _
  nlinarith

/-- The `T`-power algebra of the variation. -/
lemma var_T_alg {T M : ℝ} (hT : 1 ≤ T) (hM : M ≤ T ^ (401 / 400 : ℝ)) :
    T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) + M * (T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) +
      4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ)))) ≤
      6 * T ^ (-(49 / 50) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have a1 : T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) ≤ T ^ (-(49 / 50) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hp2 : 0 ≤ T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) := by positivity
  have hp3 : 0 ≤ 4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ))) := by positivity
  have a2 : M * T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) ≤ T ^ (-(49 / 50) : ℝ) := by
    calc M * T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) ≤
          T ^ (401 / 400 : ℝ) * T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) :=
          mul_le_mul_of_nonneg_right hM hp2
      _ = T ^ ((401 / 400 : ℝ) + -((2 : ℕ) * (399 / 400 : ℝ))) := (Real.rpow_add hT0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have a3 : M * (4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ)))) ≤
      4 * T ^ (-(49 / 50) : ℝ) := by
    calc M * (4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ)))) ≤
          T ^ (401 / 400 : ℝ) * (4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ)))) :=
          mul_le_mul_of_nonneg_right hM hp3
      _ = 4 * (T ^ (401 / 400 : ℝ) * T ^ (1 : ℝ) * T ^ (1 / 100 : ℝ) *
            T ^ (-((3 : ℕ) * (399 / 400 : ℝ)))) := by rw [Real.rpow_one]; ring
      _ = 4 * T ^ ((401 / 400 : ℝ) + 1 + 1 / 100 + -((3 : ℕ) * (399 / 400 : ℝ))) := by
          rw [Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_add hT0]
      _ = 4 * T ^ (-(49 / 50) : ℝ) := by norm_num
  nlinarith

/-- **One line.** -/
theorem line_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (P Q : ℕ) (ℓ : ℤ) (T u v : ℝ), 1 ≤ P → 1 ≤ Q → 4 ≤ T →
    0 ≤ u → u ≤ 4 * T → |v| ≤ 1 → ℓ ≠ 0 → ℓ.natAbs ≤ K0 T →
      ‖∑ m ∈ Icc (M1 T + 1) (M2 T), ((lineTerm P Q ℓ m : ℝ) : ℂ) * Hl P Q ℓ u v m‖ ≤
        K * ((P : ℝ) * Q) ^ 13 * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50) := by
  obtain ⟨CL, hCL0, hCL⟩ := abs_lineSum_le
  obtain ⟨KH, hKH0, hKH⟩ := Hl_deriv
  refine ⟨36 * CL * KH, by positivity, fun P Q ℓ T u v hP hQ hT hu0 hu hv hℓ0 hℓK => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set R := T ^ (399 / 400 : ℝ)
  have hR0 : 0 < R := Real.rpow_pos_of_pos hT0 _
  have hRM : R ≤ ((M1 T : ℕ) : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hK0 : ((K0 T : ℕ) : ℝ) ≤ T ^ (1 / 100 : ℝ) := Nat.floor_le (Real.rpow_nonneg hT0.le _)
  have hM2 : ((M2 T : ℕ) : ℝ) ≤ T ^ (401 / 400 : ℝ) := Nat.floor_le (Real.rpow_nonneg hT0.le _)
  have hℓT : |(ℓ : ℝ)| ≤ T ^ (1 / 100 : ℝ) := by
    have : ((ℓ.natAbs : ℕ) : ℝ) ≤ K0 T := by exact_mod_cast hℓK
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    linarith
  have hℓ1 : 1 ≤ |(ℓ : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hℓ0
  have h2ℓ : ∀ r, R ≤ r → 2 * |(ℓ : ℝ)| ≤ r := fun r hr => by
    have := two_rpow_le hT; linarith
  -- partial sums
  set X : ℝ := ((M2 T + P * M2 T + K0 T : ℕ) : ℝ)
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = CL * X ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) *
      ((P * Q : ℕ) : ℝ) ^ 12 := ⟨_, rfl⟩
  have hB : ∀ M ≤ M2 T, |lineSum P Q ℓ M| ≤ B := by
    intro M hM
    refine (hCL P Q ℓ M hP hQ hℓ0).trans ?_
    rw [hBd]
    have : ((M + P * M + ℓ.natAbs : ℕ) : ℝ) ≤ X := by
      simp only [X]; exact_mod_cast (by nlinarith : M + P * M + ℓ.natAbs ≤ M2 T + P * M2 T + K0 T)
    gcongr
  -- weight bounds
  set V := KH * Q * (T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) +
    4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ))))
  have hH0 : ∀ r, R ≤ r → ‖Hl P Q ℓ u v r‖ ≤ KH * Q * T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hR0 hr
    refine (hKH P Q ℓ u v r hP hQ hv hr0 (h2ℓ r hr)).1.trans ?_
    have := one_div_pow_le hT0 hr 1
    rw [pow_one] at this
    calc KH * Q / r = KH * Q * (1 / r) := by ring
      _ ≤ KH * Q * T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
  have hH : ∀ r, R ≤ r → ∃ D, HasDerivAt (Hl P Q ℓ u v) D r ∧ ‖D‖ ≤ V := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hR0 hr
    obtain ⟨D, hD, hDb⟩ := (hKH P Q ℓ u v r hP hQ hv hr0 (h2ℓ r hr)).2
    refine ⟨D, hD, hDb.trans ?_⟩
    have e2 := one_div_pow_le hT0 hr 2
    have e3 := one_div_pow_le hT0 hr 3
    have hul : |u| * |(ℓ : ℝ)| ≤ 4 * T * T ^ (1 / 100 : ℝ) := by
      rw [abs_of_nonneg hu0]
      exact mul_le_mul hu hℓT (abs_nonneg _) (by positivity)
    have : |u| * |(ℓ : ℝ)| / r ^ 3 ≤ 4 * T * T ^ (1 / 100 : ℝ) * T ^ (-((3 : ℕ) * (399 / 400 : ℝ))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hul e3 (by positivity) (by positivity)
    simp only [V]
    gcongr
  have hV0 : 0 ≤ V := by positivity
  refine (abel_line hRM hB hH0 hH hV0).trans ?_
  -- the `T`-algebra
  have hA := var_T_alg hT1 hM2
  have hX : X ≤ 3 * P * T ^ (401 / 400 : ℝ) := by
    simp only [X]; push_cast
    have h1 : T ^ (1 / 100 : ℝ) ≤ T ^ (401 / 400 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
    have h2 : (P : ℝ) * (M2 T) ≤ P * T ^ (401 / 400 : ℝ) := mul_le_mul_of_nonneg_left hM2 (by positivity)
    have h3 : 0 ≤ T ^ (401 / 400 : ℝ) := by positivity
    nlinarith
  have hX1 : X ^ (1 - 1 / 21 : ℝ) ≤ 3 * P * T ^ (401 / 420 : ℝ) := by
    calc X ^ (1 - 1 / 21 : ℝ) ≤ (3 * P * T ^ (401 / 400 : ℝ)) ^ (1 - 1 / 21 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hX (by norm_num)
      _ = (3 * P) ^ (1 - 1 / 21 : ℝ) * T ^ (401 / 420 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT0.le]; norm_num
      _ ≤ (3 * P) ^ (1 : ℝ) * T ^ (401 / 420 : ℝ) := by
          gcongr
          · linarith
          · norm_num
      _ = 3 * P * T ^ (401 / 420 : ℝ) := by rw [Real.rpow_one]
  have hℓ21 : |(ℓ : ℝ)| ^ (1 / 21 : ℝ) ≤ T ^ (1 / 100 : ℝ) := by
    calc |(ℓ : ℝ)| ^ (1 / 21 : ℝ) ≤ |(ℓ : ℝ)| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)
      _ ≤ _ := by rw [Real.rpow_one]; exact hℓT
  have hBb : B ≤ CL * (3 * P * T ^ (401 / 420 : ℝ)) * T ^ (1 / 100 : ℝ) * ((P : ℝ) * Q) ^ 12 := by
    rw [hBd]; push_cast
    gcongr
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hsum : KH * Q * T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) + (M2 T : ℝ) * V ≤
      KH * Q * (6 * T ^ (-(49 / 50) : ℝ)) := by
    simp only [V]
    have e : KH * Q * T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) + (M2 T : ℝ) * (KH * Q *
        (T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) + 4 * T * T ^ (1 / 100 : ℝ) *
          T ^ (-((3 : ℕ) * (399 / 400 : ℝ))))) =
        KH * Q * (T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) + (M2 T : ℝ) *
          (T ^ (-((2 : ℕ) * (399 / 400 : ℝ))) + 4 * T * T ^ (1 / 100 : ℝ) *
            T ^ (-((3 : ℕ) * (399 / 400 : ℝ))))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  calc 2 * B * (KH * Q * T ^ (-((1 : ℕ) * (399 / 400 : ℝ))) + (M2 T : ℝ) * V)
      ≤ 2 * (CL * (3 * P * T ^ (401 / 420 : ℝ)) * T ^ (1 / 100 : ℝ) * ((P : ℝ) * Q) ^ 12) *
          (KH * Q * (6 * T ^ (-(49 / 50) : ℝ))) := by
        gcongr
    _ = 36 * CL * KH * ((P : ℝ) * Q) ^ 13 *
          (T ^ (401 / 420 : ℝ) * T ^ (1 / 100 : ℝ) * T ^ (-(49 / 50) : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; ring_nf

lemma card_Lset_le {T : ℝ} (hT : 1 ≤ T) : ((Lset T).card : ℝ) ≤ 3 * T ^ (1 / 100 : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hK0 : ((K0 T : ℕ) : ℝ) ≤ T ^ (1 / 100 : ℝ) := Nat.floor_le (Real.rpow_nonneg hT0.le _)
  have h1 : (Lset T).card ≤ 2 * K0 T + 1 := by
    unfold Lset
    refine (card_erase_le).trans (le_of_eq ?_)
    rw [Int.card_Icc]; omega
  have h2 : 1 ≤ T ^ (1 / 100 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have h3 : ((Lset T).card : ℝ) ≤ 2 * (K0 T : ℝ) + 1 := by exact_mod_cast h1
  linarith

/-- **R3: the near part.** -/
theorem near_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c d : ℕ) (T x v : ℝ), 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d →
    4 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 →
      ‖∑ p ∈ nearSet (a * c) (b * d) T, ∫ t in (T / 2)..(3 * T), Fq T x v (a, b, c, d) p t‖ ≤
        K * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 13 * T ^ (299 / 300 : ℝ) := by
  obtain ⟨K1, hK10, hK1⟩ := line_bound
  refine ⟨8 * K1, by positivity, fun a b c d T x v ha hb hc hd hT hx0 hx1 hv => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hP : 1 ≤ a * c := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hQ : 1 ≤ b * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  set W := (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 13
  have hW0 : 0 ≤ W := by positivity
  set E := 3 * T ^ (1 / 100 : ℝ) * (K1 * W * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50))
  rw [← intervalIntegral.integral_finsetSum fun p _ =>
    (continuous_Fq T x v (a, b, c, d) p).intervalIntegrable _ _]
  have hpt : ∀ t ∈ Set.uIoc (T / 2) (3 * T),
      ‖∑ p ∈ nearSet (a * c) (b * d) T, Fq T x v (a, b, c, d) p t‖ ≤ E := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    rw [near_sum_eq a b c d ha hb hc hd T x v t, norm_mul]
    have hu0 : 0 ≤ t + x := by linarith [ht.1]
    have hu : t + x ≤ 4 * T := by linarith [ht.2]
    have hl : ∀ ℓ ∈ Lset T, ‖∑ m ∈ Icc (M1 T + 1) (M2 T),
        ((lineTerm (a * c) (b * d) ℓ m : ℝ) : ℂ) * Hl (a * c) (b * d) ℓ (t + x) v m‖ ≤
          K1 * W * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50) := by
      intro ℓ hℓ
      rw [mem_Lset] at hℓ
      have := hK1 (a * c) (b * d) ℓ T (t + x) v hP hQ hT hu0 hu hv hℓ.1 hℓ.2
      simpa [W] using this
    have hs := (norm_sum_le _ _).trans (sum_le_sum hl)
    rw [sum_const, nsmul_eq_mul] at hs
    have hc := card_Lset_le hT1
    have hX : 0 ≤ K1 * W * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50) := by positivity
    calc ‖Zt a b c d T x v t‖ * _ ≤ 1 * (((Lset T).card : ℝ) *
          (K1 * W * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50))) :=
          mul_le_mul (norm_Zt_le _ _ _ _ _ _ _ _) hs (norm_nonneg _) zero_le_one
      _ ≤ E := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hc hX
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * T - T / 2)]
  have e : E * (3 * T - T / 2) = 15 / 2 * K1 * W *
      (T ^ (1 : ℝ) * T ^ (1 / 100 : ℝ) * T ^ ((401 / 420 : ℝ) + 1 / 100 - 49 / 50)) := by
    simp only [E]; rw [Real.rpow_one]; ring
  rw [e, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have h1 : T ^ ((1 : ℝ) + 1 / 100 + ((401 / 420 : ℝ) + 1 / 100 - 49 / 50)) ≤ T ^ (299 / 300 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have h2 : 0 ≤ 15 / 2 * K1 * W := by positivity
  calc 15 / 2 * K1 * W * T ^ ((1 : ℝ) + 1 / 100 + ((401 / 420 : ℝ) + 1 / 100 - 49 / 50))
      ≤ 15 / 2 * K1 * W * T ^ (299 / 300 : ℝ) := mul_le_mul_of_nonneg_left h1 h2
    _ ≤ 8 * K1 * W * T ^ (299 / 300 : ℝ) := by
        have : 0 ≤ K1 * W * T ^ (299 / 300 : ℝ) := by positivity
        nlinarith

end RamanujanTau.SelbergKey7
