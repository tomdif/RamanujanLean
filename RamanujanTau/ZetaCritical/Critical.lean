/-
# Hardy–Littlewood on the critical line: `∫₁ᵀ |ζ(1/2+it)|² = T log T + O(T √log T)`

On `s = 1/2 − it`, `N = ⌈V⌉`:
* `∫_1^V |ζ − P_N|² ≤ (4+16π) V` (`ZetaMeanSquare.err_L2` at `σ = 1/2`);
* `| |ζ|² − |P|² | ≤ η|P|² + (1+1/η)|ζ−P|²` (`sq_compare`);
* `u ↦ ∫_1^u |ζ|²` is monotone, so it is sandwiched by its averages over `[T, T+H]` and
  `[T−H, T]`, and the averaged polynomial mean value (`avg_mv`) has off-diagonal `O(N²/H)`
  without any logarithm (`offdiag_ch_le`).
With `H = εT/2`, `η = ε`: `|∫_1^T |ζ|² − T log T| ≤ 2ε T log T + K T/ε`; `ε = (log T)^{−1/2}`.
-/
import RamanujanTau.ZetaCritical.Bound
import RamanujanTau.ZetaCritical.Algebra
import RamanujanTau.ZetaMeanSquare.Zeta

set_option autoImplicit false

namespace RamanujanTau.ZetaCritical

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.MeanSquare (dpoly H H_le_one_add_log continuous_dpoly H_nonneg)
open RamanujanTau.ZetaMeanSquare (Pz err_L2 sq_compare norm_Pz_eq continuousAt_zeta_line
  continuous_Pz_line ceil_bounds bσ)

/-- `|ζ(1/2 − it)|²`. -/
noncomputable def fz (t : ℝ) : ℝ := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) - t * I)‖ ^ 2

/-- `|ζ(1/2 − it) − P_N(1/2 − it)|²`. -/
noncomputable def fe (N : ℕ) (t : ℝ) : ℝ :=
  ‖riemannZeta (((1 / 2 : ℝ) : ℂ) - t * I) - Pz N (((1 / 2 : ℝ) : ℂ) - t * I)‖ ^ 2

/-- `G_N(u) = ∫₀ᵘ |P_N|²`. -/
noncomputable def G (N : ℕ) (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, ‖dpoly (fun n => (ch n : ℂ)) N t‖ ^ 2

/-- `I(u) = ∫₁ᵘ |ζ(1/2 − it)|²`. -/
noncomputable def Iz (u : ℝ) : ℝ := ∫ t in (1 : ℝ)..u, fz t

/-- The constant of `err_L2`. -/
noncomputable def CE : ℝ := 4 + 16 * Real.pi

lemma CE_nonneg : 0 ≤ CE := by unfold CE; positivity

lemma bσ_half : bσ (1 / 2) = fun n => (ch n : ℂ) := rfl

lemma continuousOn_fz {a b : ℝ} (ha : 0 < a) : ContinuousOn fz (Icc a b) := fun t ht =>
  ((continuousAt_zeta_line _ (by linarith [ht.1] : t ≠ 0)).norm.pow 2).continuousWithinAt

lemma continuousOn_fe (N : ℕ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (fe N) (Icc a b) :=
  fun t ht => (((continuousAt_zeta_line _ (by linarith [ht.1] : t ≠ 0)).sub
    (continuous_Pz_line N _).continuousAt).norm.pow 2).continuousWithinAt

lemma ii_fz {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable fz volume a b :=
  (continuousOn_fz ha).intervalIntegrable_of_Icc hab

lemma ii_fe (N : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable (fe N) volume a b :=
  (continuousOn_fe N ha).intervalIntegrable_of_Icc hab

lemma continuous_G (N : ℕ) : Continuous (G N) := continuous_primitive_P ch N

lemma G_one_nonneg (N : ℕ) : 0 ≤ G N 1 :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => by positivity

lemma Iz_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : Iz u ≤ Iz v := by
  unfold Iz
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_fz one_pos hu) (ii_fz (by linarith) huv)]
  have : 0 ≤ ∫ t in u..v, fz t := intervalIntegral.integral_nonneg huv fun _ _ => by
    unfold fz; positivity
  linarith

/-- `∫_1^u |ζ − P|² ≤ CE · V` for `1 ≤ u ≤ V`, `N = ⌈V⌉`. -/
lemma err_le {u V : ℝ} (hu : 1 ≤ u) (huV : u ≤ V) :
    ∫ t in (1 : ℝ)..u, fe ⌈V⌉₊ t ≤ CE * V := by
  have hV : 1 ≤ V := hu.trans huV
  have h := err_L2 (σ := 1 / 2) (by norm_num) (by norm_num) hV
  have e : V ^ (2 - 2 * (1 / 2 : ℝ)) = V := by norm_num
  rw [e] at h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (ii_fe ⌈V⌉₊ one_pos hu)
    (ii_fe ⌈V⌉₊ (by linarith) huV)
  have h0 : 0 ≤ ∫ t in u..V, fe ⌈V⌉₊ t := intervalIntegral.integral_nonneg huV fun _ _ => by
    unfold fe; positivity
  unfold CE
  unfold fe at hsplit h0 ⊢
  linarith

/-- The two comparison inequalities on `[1, u]`. -/
lemma compare {u V η : ℝ} (hu : 1 ≤ u) (huV : u ≤ V) (hη : 0 < η) :
    Iz u ≤ (1 + η) * (G ⌈V⌉₊ u - G ⌈V⌉₊ 1) + (1 + 1 / η) * (CE * V) ∧
      G ⌈V⌉₊ u - G ⌈V⌉₊ 1 ≤ Iz u + η * (G ⌈V⌉₊ u - G ⌈V⌉₊ 1) + (1 + 1 / η) * (CE * V) := by
  set N := ⌈V⌉₊ with hN
  set fp : ℝ → ℝ := fun t => ‖dpoly (fun n => (ch n : ℂ)) N t‖ ^ 2 with hfp
  have hcp : Continuous fp := (continuous_dpoly _ N).norm.pow 2
  have hip : IntervalIntegrable fp volume 1 u := hcp.intervalIntegrable _ _
  have hiz := ii_fz one_pos hu
  have hie := ii_fe N one_pos hu
  have hGP : G N u - G N 1 = ∫ t in (1 : ℝ)..u, fp t := by
    unfold G
    exact intervalIntegral.integral_interval_sub_left (hcp.intervalIntegrable _ _)
      (hcp.intervalIntegrable _ _)
  have hE := err_le hu huV
  rw [← hN] at hE
  have hpt : ∀ t ∈ Icc (1 : ℝ) u, fz t ≤ (1 + η) * fp t + (1 + 1 / η) * fe N t ∧
      fp t ≤ fz t + η * fp t + (1 + 1 / η) * fe N t := by
    intro t _
    have hPz := norm_Pz_eq N (1 / 2) t
    rw [bσ_half] at hPz
    have h1 := norm_le_norm_add_norm_sub' (riemannZeta (((1 / 2 : ℝ) : ℂ) - t * I))
      (Pz N (((1 / 2 : ℝ) : ℂ) - t * I))
    have h2 := norm_le_norm_add_norm_sub' (Pz N (((1 / 2 : ℝ) : ℂ) - t * I))
      (riemannZeta (((1 / 2 : ℝ) : ℂ) - t * I))
    rw [norm_sub_rev] at h2
    rw [hPz] at h1 h2
    exact sq_compare (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hη h1 h2
  have hup : Iz u ≤ (1 + η) * (∫ t in (1 : ℝ)..u, fp t) + (1 + 1 / η) * ∫ t in (1 : ℝ)..u, fe N t := by
    have := intervalIntegral.integral_mono_on hu hiz
      ((hip.const_mul (1 + η)).add (hie.const_mul (1 + 1 / η))) (fun t ht => (hpt t ht).1)
    rw [intervalIntegral.integral_add (hip.const_mul _) (hie.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
    exact this
  have hlo : (∫ t in (1 : ℝ)..u, fp t) ≤ Iz u + η * (∫ t in (1 : ℝ)..u, fp t) +
      (1 + 1 / η) * ∫ t in (1 : ℝ)..u, fe N t := by
    have := intervalIntegral.integral_mono_on hu hip
      ((hiz.add (hip.const_mul η)).add (hie.const_mul (1 + 1 / η))) (fun t ht => (hpt t ht).2)
    rw [intervalIntegral.integral_add (hiz.add (hip.const_mul _)) (hie.const_mul _),
      intervalIntegral.integral_add hiz (hip.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
    exact this
  have hc : 0 ≤ 1 + 1 / η := by positivity
  rw [hGP]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hE hc]
  · nlinarith [mul_le_mul_of_nonneg_left hE hc]

/-- The averaged polynomial mean value with the explicit off-diagonal bound. -/
lemma avg_G (N : ℕ) (a b : ℝ) :
    |(∫ u in a..b, G N u) - (b ^ 2 - a ^ 2) / 2 * H N| ≤ 20 * (N : ℝ) ^ 2 := by
  have h := avg_mv ch N a b
  rw [sum_ch_sq] at h
  exact h.trans (offdiag_ch_le N)

/-- **Upper half.** -/
lemma upper {ε T : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hT : 2 ≤ T) :
    Iz T ≤ (1 + 2 * ε) * T * Real.log T + (729 + 3 * CE) * T / ε := by
  set V : ℝ := T + ε * T / 2 with hV
  have hT0 : 0 < T := by linarith
  have hTV : T ≤ V := by rw [hV]; nlinarith
  have hV1 : 1 ≤ V := by linarith
  set N := ⌈V⌉₊ with hN
  obtain ⟨hN1, hVN, hNV⟩ := ceil_bounds hV1
  rw [← hN] at hN1 hVN hNV
  -- pointwise on the window
  have hpt : ∀ u ∈ Icc T V, Iz T ≤ (1 + ε) * G N u + (1 + 1 / ε) * (CE * V) := by
    intro u hu
    have h1 := Iz_mono (by linarith) hu.1
    have h2 := (compare (by linarith [hu.1]) hu.2 hε0).1
    rw [← hN] at h2
    have := G_one_nonneg N
    nlinarith
  have hGi : IntervalIntegrable (G N) volume T V := (continuous_G N).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on hTV
    ((continuous_const : Continuous fun _ : ℝ => Iz T).intervalIntegrable (μ := volume) T V)
    ((hGi.const_mul (1 + ε)).add ((continuous_const : Continuous fun _ : ℝ => (1 + 1 / ε) * (CE * V)).intervalIntegrable (μ := volume) T V)) hpt
  rw [intervalIntegral.integral_add (hGi.const_mul _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul] at hint
  have havg := (abs_le.1 (avg_G N T V)).2
  have hVT : V - T = ε * T / 2 := by rw [hV]; ring
  rw [hVT] at hint
  have main : ε * T / 2 * Iz T ≤ (1 + ε) * (((T + ε * T / 2) ^ 2 - T ^ 2) / 2 * H N +
      20 * (N : ℝ) ^ 2) + ε * T / 2 * ((1 + 1 / ε) * (CE * (T + ε * T / 2))) := by
    rw [← hV]
    have : (1 + ε) * (∫ u in T..V, G N u) ≤ (1 + ε) * ((V ^ 2 - T ^ 2) / 2 * H N + 20 * (N : ℝ) ^ 2) := by
      gcongr; linarith
    linarith
  have hH := H_le_one_add_log N
  have hlogN : Real.log N ≤ 2 + Real.log T := by
    have hN0 : (0 : ℝ) < N := by linarith
    have h3 : (N : ℝ) ≤ 3 * T := by nlinarith
    have := Real.log_le_log hN0 h3
    rw [Real.log_mul (by norm_num) hT0.ne'] at this
    have : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  exact upper_alg T ε (H N) N (Iz T) (Real.log T) CE hT hε0 hε1 (Nat.cast_nonneg _)
    (by nlinarith) (H_nonneg N) (by linarith) (Real.log_nonneg (by linarith)) CE_nonneg main

/-- **Lower half.** -/
lemma lower {ε T : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hT : 2 ≤ T) :
    (1 - 2 * ε) * T * Real.log T - (168 + 2 * CE) * T / ε ≤ Iz T := by
  set U : ℝ := T - ε * T / 2 with hU
  have hT0 : 0 < T := by linarith
  have hUT : U ≤ T := by rw [hU]; nlinarith
  have hU1 : 1 ≤ U := by rw [hU]; nlinarith
  set N := ⌈T⌉₊ with hN
  obtain ⟨hN1, hTN, hNT⟩ := ceil_bounds (show 1 ≤ T by linarith)
  rw [← hN] at hN1 hTN hNT
  have hη1 : 0 ≤ 1 - ε := by linarith
  have hpt : ∀ u ∈ Icc U T, (1 - ε) * G N u - (1 - ε) * G N 1 ≤
      Iz T + (1 + 1 / ε) * (CE * T) := by
    intro u hu
    have h1 := Iz_mono (by linarith [hu.1]) hu.2
    have h2 := (compare (by linarith [hu.1]) hu.2 hε0).2
    rw [← hN] at h2
    nlinarith
  have hGi : IntervalIntegrable (G N) volume U T := (continuous_G N).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on hUT
    ((hGi.const_mul (1 - ε)).sub ((continuous_const : Continuous fun _ : ℝ => (1 - ε) * G N 1).intervalIntegrable (μ := volume) U T))
    ((continuous_const : Continuous fun _ : ℝ => Iz T + (1 + 1 / ε) * (CE * T)).intervalIntegrable (μ := volume) U T)
    hpt
  rw [intervalIntegral.integral_sub (hGi.const_mul _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul] at hint
  have havg := (abs_le.1 (avg_G N U T)).1
  have hTU : T - U = ε * T / 2 := by rw [hU]; ring
  rw [hTU] at hint
  have main : (1 - ε) * ((T ^ 2 - (T - ε * T / 2) ^ 2) / 2 * H N - 20 * (N : ℝ) ^ 2 -
      ε * T / 2 * G N 1) ≤ ε * T / 2 * (Iz T + (1 + 1 / ε) * (CE * T)) := by
    rw [← hU]
    have : (1 - ε) * ((T ^ 2 - U ^ 2) / 2 * H N - 20 * (N : ℝ) ^ 2) ≤
        (1 - ε) * (∫ u in U..T, G N u) := by
      gcongr; linarith
    nlinarith
  have hL : Real.log T ≤ H N :=
    (Real.log_le_log hT0 hTN).trans (log_le_H N)
  have hg := primitive_one_le N
  exact lower_alg T ε (H N) N (Iz T) (Real.log T) CE (G N 1) hT hε0 hε1 (Nat.cast_nonneg _)
    hNT hL (Real.log_nonneg (by linarith)) CE_nonneg (G_one_nonneg N) hg main

/-- **The sandwich with a free parameter.** For `0 < ε ≤ 1`, `T ≥ 2`:
`|∫₁ᵀ |ζ(1/2 − it)|² − T log T| ≤ 2ε T log T + K T/ε`. -/
theorem Iz_eps (ε T : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hT : 2 ≤ T) :
    |Iz T - T * Real.log T| ≤ 2 * ε * (T * Real.log T) + (729 + 3 * CE) * T / ε :=
  abs_alg (by linarith [CE_nonneg]) (upper hε0 hε1 hT) (lower hε0 hε1 hT) (by linarith) hε0

lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- **Quantitative Hardy–Littlewood** on `[1, T]`, line `1/2 − it`. -/
theorem Iz_sqrt (T : ℝ) (hT : 3 ≤ T) :
    |Iz T - T * Real.log T| ≤ (731 + 3 * CE) * (T * Real.sqrt (Real.log T)) := by
  set L := Real.log T with hL
  have hL1 : 1 ≤ L := one_le_log_three.trans (Real.log_le_log (by norm_num) hT)
  set r := Real.sqrt L with hr
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.2 hL1
  have hr0 : 0 < r := by linarith
  have hrr : r * r = L := Real.mul_self_sqrt (by linarith)
  have h := Iz_eps (1 / r) T (by positivity) (by rw [div_le_one hr0]; exact hr1) (by linarith)
  have e1 : 2 * (1 / r) * (T * L) = 2 * (T * r) := by
    rw [← hrr]; field_simp
  have e2 : (729 + 3 * CE) * T / (1 / r) = (729 + 3 * CE) * (T * r) := by
    field_simp
  rw [e1, e2] at h
  have : (731 + 3 * CE) * (T * r) = 2 * (T * r) + (729 + 3 * CE) * (T * r) := by ring
  rw [this]; exact h

end RamanujanTau.ZetaCritical
