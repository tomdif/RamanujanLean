/-
# Assembly: `∫_0^T |L(Δ,6+it)|² dt ≫ T log T`

Take `δ = K/T`, `β = π/2 − δ`, `κ = cot β = tan δ ∈ (0, 2δ]`, `N₂ = ⌊1/κ⌋`.  Then
`ray_lower` gives `LHS(β) ≥ a κ^{-12}(log N₂ − log N₁) ≥ a (T/2K)^{12} (log T − L₀)`, while
`lhs_le` + `ioi_le` give `LHS(β) ≤ 2C_Γ[(1+T)¹¹ J(T) + D e^{−2K} T¹² (1+log T)]`.
For `K` large the tail is at most a quarter of the main term, which leaves
`J(T) ≫ K^{-12} T log T`.
-/
import RamanujanTau.CriticalMeanSquareLower.RayBlock
import RamanujanTau.CriticalMeanSquareLower.Tail

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareLower

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare
open scoped Real

/-- `tan δ ≤ 2δ` and `0 < tan δ` for `0 < δ ≤ 1`, in the form `cot(π/2 − δ)`. -/
lemma cot_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < Real.cos (π / 2 - δ) / Real.sin (π / 2 - δ) ∧
      Real.cos (π / 2 - δ) / Real.sin (π / 2 - δ) ≤ 2 * δ := by
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_gt_three])
  have hc : 1 / 2 ≤ Real.cos δ := by
    have := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  have hsl : Real.sin δ ≤ δ := Real.sin_le hδ0.le
  refine ⟨div_pos hs (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The final real-number bookkeeping. -/
lemma final_arith {A' P Lg L0 CΓ T J : ℝ} (hA' : 0 < A') (hT : 1 ≤ T) (hCΓ : 0 < CΓ)
    (hJ : 0 ≤ J) (hL0 : 0 ≤ L0) (hLg : 4 * L0 + 1 ≤ Lg) (hP : P = T ^ 12)
    (hmain : A' * P * (Lg - L0) ≤ 2 * CΓ * ((1 + T) ^ 11 * J) + A' / 4 * P * (1 + Lg)) :
    A' / (2 ^ 13 * CΓ) * T * Lg ≤ J := by
  have hT0 : 0 < T := by linarith
  have hP0 : 0 < P := by rw [hP]; positivity
  have hkey : A' / 2 * P * Lg ≤ 2 * CΓ * ((1 + T) ^ 11 * J) := by
    have : 0 ≤ A' * P * (Lg / 4 - L0 - 1 / 4) := by
      apply mul_nonneg (by positivity); linarith
    linarith
  have h1T : (1 + T) ^ 11 * J ≤ 2 ^ 11 * T ^ 11 * J := by
    have : (1 + T) ^ 11 ≤ (2 * T) ^ 11 := by gcongr; linarith
    calc (1 + T) ^ 11 * J ≤ (2 * T) ^ 11 * J := by gcongr
      _ = 2 ^ 11 * T ^ 11 * J := by ring
  have hfin : A' / 2 * T ^ 12 * Lg ≤ 2 * CΓ * (2 ^ 11 * T ^ 11 * J) := by
    have := mul_le_mul_of_nonneg_left h1T (by positivity : (0 : ℝ) ≤ 2 * CΓ)
    rw [← hP]; linarith
  have hT11 : 0 < T ^ 11 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e1 : A' * T * Lg * T ^ 11 = 2 * (A' / 2 * T ^ 12 * Lg) := by ring
  have e2 : J * (2 ^ 13 * CΓ) * T ^ 11 = 2 * (2 * CΓ * (2 ^ 11 * T ^ 11 * J)) := by ring
  rw [← mul_le_mul_iff_of_pos_right hT11, e1, e2]
  linarith

/-- **Lower bound for the critical mean square.** -/
theorem critical_mean_square_lower : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀,
    c * T * Real.log T ≤ ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 := by
  obtain ⟨a, ha, N₁, hN₁, hray⟩ := ray_lower
  obtain ⟨CΓ, hCΓ, hw⟩ := exists_weight_bound
  obtain ⟨Cd, hCd0, hCd⟩ := dyadic_upper
  set D : ℝ := 2 * Cd * 3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Q : ℝ := 8 * CΓ * D * 2 ^ 12 * (Nat.factorial 12 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set K : ℝ := 1 + Real.log (Q / a + 1) with hK
  have hlogQ : 0 ≤ Real.log (Q / a + 1) := Real.log_nonneg (by
    have : 0 ≤ Q / a := div_nonneg hQ0 ha.le
    linarith)
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hK0 : 0 < K := by linarith
  -- the tail constant is small: `2 C_Γ D e^{−2K} ≤ a / (4 (2K)^{12})`
  have hsmall : 2 * CΓ * D * Real.exp (-2 * K) ≤ a / (2 * K) ^ 12 / 4 := by
    have hfact := Real.pow_div_factorial_le_exp K hK0.le 12
    rw [div_le_iff₀ (by positivity)] at hfact
    have heK : Q / a + 1 ≤ Real.exp K := by
      rw [hK, Real.exp_add]
      rw [Real.exp_log (by have : 0 ≤ Q / a := div_nonneg hQ0 ha.le; linarith)]
      have := Real.add_one_le_exp 1
      have h0 : 0 ≤ Q / a + 1 := by have : 0 ≤ Q / a := div_nonneg hQ0 ha.le; linarith
      nlinarith
    have hQa : Q ≤ a * Real.exp K := by
      have : Q / a ≤ Real.exp K := by linarith
      rw [div_le_iff₀ ha] at this; linarith
    have hE : Real.exp (-2 * K) * Real.exp K * Real.exp K = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
    have hEpos : 0 < Real.exp (-2 * K) := Real.exp_pos _
    calc 2 * CΓ * D * Real.exp (-2 * K) * 4 * (2 * K) ^ 12
        = 8 * CΓ * D * 2 ^ 12 * Real.exp (-2 * K) * K ^ 12 := by ring
      _ ≤ 8 * CΓ * D * 2 ^ 12 * Real.exp (-2 * K) * (Real.exp K * (Nat.factorial 12 : ℝ)) := by
          gcongr
      _ = Q * (Real.exp (-2 * K) * Real.exp K) := by rw [hQ]; ring
      _ ≤ a * Real.exp K * (Real.exp (-2 * K) * Real.exp K) := by gcongr
      _ = a * (Real.exp (-2 * K) * Real.exp K * Real.exp K) := by ring
      _ = a := by rw [hE, mul_one]
  set A' : ℝ := a / (2 * K) ^ 12 with hA'
  have hA'0 : 0 < A' := by rw [hA']; positivity
  set L0 : ℝ := Real.log (4 * K) + Real.log N₁ with hL0
  have hN₁r : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hL00 : 0 ≤ L0 := by
    rw [hL0]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * K by linarith)
    have := Real.log_nonneg hN₁r
    linarith
  refine ⟨A' / (2 ^ 13 * CΓ), max (4 * K * N₁) (Real.exp (4 * L0 + 1)), by positivity,
    fun T hT => ?_⟩
  have hT1 : 4 * K * N₁ ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : Real.exp (4 * L0 + 1) ≤ T := le_trans (le_max_right _ _) hT
  have hTK : 4 * K ≤ T := by nlinarith
  have hT0 : 0 < T := by linarith
  have hTge1 : 1 ≤ T := by linarith
  set Lg : ℝ := Real.log T with hLgdef
  have hLg : 4 * L0 + 1 ≤ Lg := by
    rw [hLgdef]; exact (Real.le_log_iff_exp_le hT0).mpr hT2
  -- parameters
  set δ : ℝ := K / T with hδ
  have hδ0 : 0 < δ := by positivity
  have hδT : δ * T = K := by rw [hδ]; field_simp
  have hδ4 : δ ≤ 1 / 4 := by rw [hδ, div_le_iff₀ hT0]; linarith
  set β : ℝ := π / 2 - δ with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith [Real.pi_gt_three]
  have hβπ : β < π / 2 := by rw [hβ]; linarith
  obtain ⟨hκ0, hκ2⟩ := cot_bounds hδ0 (by linarith)
  rw [← hβ] at hκ0 hκ2
  set κ : ℝ := Real.cos β / Real.sin β with hκ
  have hκ12 : κ ≤ 1 / 2 := by linarith
  -- `N₂ = ⌊1/κ⌋`
  set N₂ : ℕ := ⌊1 / κ⌋₊ with hN₂
  have hκN₂ : κ * N₂ ≤ 1 := by
    have := Nat.floor_le (show 0 ≤ 1 / κ by positivity)
    calc κ * N₂ ≤ κ * (1 / κ) := by gcongr
      _ = 1 := by field_simp
  have hN₂lo : T / (4 * K) ≤ N₂ := by
    have h1 := Nat.lt_floor_add_one (1 / κ)
    rw [← hN₂] at h1
    have h2 : 2 ≤ 1 / κ := by rw [le_div_iff₀ hκ0]; linarith
    have h3 : 1 / (2 * κ) ≤ N₂ := by
      have : 1 / (2 * κ) = (1 / κ) / 2 := by field_simp
      rw [this]; linarith
    have h4 : T / (4 * K) ≤ 1 / (2 * κ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : κ * T ≤ 2 * K := by
        calc κ * T ≤ 2 * δ * T := by gcongr
          _ = 2 * K := by rw [mul_assoc, hδT]
      nlinarith
    linarith
  have hN₁N₂r : (N₁ : ℝ) ≤ N₂ := by
    refine le_trans ?_ hN₂lo
    rw [le_div_iff₀ (by positivity)]; linarith
  have hN₁N₂ : N₁ ≤ N₂ := by exact_mod_cast hN₁N₂r
  have hN₂pos : (0 : ℝ) < N₂ := by linarith
  -- lower side
  have hR := hray β hβ0 hβπ N₂ hN₁N₂ hκN₂
  have hlogN₂ : Lg - Real.log (4 * K) ≤ Real.log N₂ := by
    have := Real.log_le_log (by positivity) hN₂lo
    rw [Real.log_div hT0.ne' (by positivity)] at this
    rw [hLgdef]; linarith
  have hRnn : 0 ≤ Real.log N₂ - Real.log N₁ := by
    have := Real.log_le_log (by positivity) hN₁N₂r; linarith
  have hκpow : T ^ 12 / (2 * K) ^ 12 ≤ 1 / κ ^ 12 := by
    have e : T ^ 12 / (2 * K) ^ 12 = 1 / (2 * δ) ^ 12 := by
      rw [hδ]; field_simp
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hκ0.le hκ2 12)
  have hlow : A' * T ^ 12 * (Lg - L0) ≤
      ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) := by
    refine le_trans ?_ hR
    have e1 : A' * T ^ 12 * (Lg - L0) = a * (T ^ 12 / (2 * K) ^ 12) * (Lg - L0) := by
      rw [hA']; ring
    have e2 : a / κ ^ 12 * (Real.log N₂ - Real.log N₁) =
        a * (1 / κ ^ 12) * (Real.log N₂ - Real.log N₁) := by ring
    rw [e1, e2]
    have hLL : Lg - L0 ≤ Real.log N₂ - Real.log N₁ := by rw [hL0]; linarith
    calc a * (T ^ 12 / (2 * K) ^ 12) * (Lg - L0)
        ≤ a * (T ^ 12 / (2 * K) ^ 12) * (Real.log N₂ - Real.log N₁) := by gcongr
      _ ≤ a * (1 / κ ^ 12) * (Real.log N₂ - Real.log N₁) := by gcongr
  -- upper side
  have hup1 := lhs_le hCΓ hw hβ0.le hβπ
  have hδβ : π / 2 - β = δ := by rw [hβ]; ring
  rw [hδβ] at hup1
  have hup2 := ioi_le hCd0 hCd hδ0 hTge1 (by rw [hδT]; exact hK1)
  set J : ℝ := ∫ t in (0 : ℝ)..T, Lsq t with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hT0.le (fun t _ => Lsq_nonneg t)
  have heδ : Real.exp (-2 * δ * T) = Real.exp (-2 * K) := by
    congr 1; rw [mul_assoc, hδT]
  rw [heδ, ← hLgdef] at hup2
  have hlogT0 : 0 ≤ Lg := by rw [hLgdef]; exact Real.log_nonneg hTge1
  set P : ℝ := T ^ 12 with hP
  have hP0 : 0 < P := by positivity
  have htail : 2 * CΓ * (2 * (Cd * (3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 *
      Real.exp (-2 * K) * P * (1 + Lg)))) ≤ A' / 4 * P * (1 + Lg) := by
    have e : 2 * CΓ * (2 * (Cd * (3 ^ 11 * (Nat.factorial 13 : ℝ) * Real.exp 1 *
        Real.exp (-2 * K) * P * (1 + Lg)))) = (2 * CΓ * D * Real.exp (-2 * K)) * (P * (1 + Lg)) := by
      rw [hD]; ring
    rw [e]
    have : A' / 4 * P * (1 + Lg) = (a / (2 * K) ^ 12 / 4) * (P * (1 + Lg)) := by rw [hA']; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hsmall (by positivity)
  have h := hlow.trans (hup1.trans (mul_le_mul_of_nonneg_left hup2 (by positivity)))
  rw [mul_add] at h
  have hmain : A' * P * (Lg - L0) ≤ 2 * CΓ * ((1 + T) ^ 11 * J) + A' / 4 * P * (1 + Lg) :=
    h.trans (add_le_add le_rfl htail)
  have hfin := final_arith hA'0 hTge1 hCΓ hJ0 hL00 hLg hP hmain
  show A' / (2 ^ 13 * CΓ) * T * Lg ≤ ∫ t in Icc 0 T, Lsq t
  rw [setIntegral_Icc_eq_interval hT0.le]
  exact hfin

/-- **Order of magnitude**: `∫_0^T |L(Δ,6+it)|² dt ≍ T log T`. -/
theorem critical_mean_square_order : ∃ c C T₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ T ≥ T₀,
    c * T * Real.log T ≤ ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ∧
      ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T := by
  obtain ⟨c, T₀, hc, hlo⟩ := critical_mean_square_lower
  obtain ⟨C, hC0, hup⟩ := critical_mean_square_upper
  exact ⟨c, C, max T₀ (Real.exp 1), hc, hC0, fun T hT =>
    ⟨hlo T (le_trans (le_max_left _ _) hT), hup T (le_trans (le_max_right _ _) hT)⟩⟩

/-- **`∫_0^T |L(Δ,6+it)|² dt = Θ(T log T)`.** -/
theorem critical_mean_square_isTheta :
    (fun T : ℝ => ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2) =Θ[atTop]
      fun T => T * Real.log T := by
  obtain ⟨c, C, T₀, hc, hC0, h⟩ := critical_mean_square_order
  have hnn : ∀ T : ℝ, 0 ≤ ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 := fun T =>
    setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
  refine ⟨Asymptotics.IsBigO.of_bound C ?_, Asymptotics.IsBigO.of_bound (1 / c) ?_⟩
  · filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop 1] with T hT hT1
    rw [Real.norm_of_nonneg (hnn T),
      Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hT1))]
    have := (h T hT).2; linarith
  · filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop 1] with T hT hT1
    rw [Real.norm_of_nonneg (hnn T),
      Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hT1))]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
    have := (h T hT).1; linarith

end RamanujanTau.CriticalMeanSquareLower
