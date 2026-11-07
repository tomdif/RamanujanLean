/-
# The Appell–Lerch form of the rank generating function, analytically

`rank_disc`: for `z ≠ 0` and `|Q| < min(|z|, 1/|z|)`,

  `(Q;Q)_∞ Σ_{n≥0} Q^{n²}/((zQ;Q)_n(Q/z;Q)_n)
     = 1 + Σ_{r≥1} (−1)^r Q^{r(3r+1)/2}(1+Q^r)(1−z)(1−z⁻¹)/((1−zQ^r)(1−Q^r/z))`.

This is the formal identity `RankProof.rank_AL` (in `ℂ⟦q⟧`, for a *constant* `z`), transferred to holomorphic
functions. When `|z| ≠ 1` the two sides are only holomorphic on the smaller disc `|Q| < ρ = min(|z|,1/|z|)`,
so we transfer on the unit disc in the rescaled variable `u = Q/ρ`: Taylor series commute with rescaling
(`T_scale`), and `PowerSeries.rescale ρ` is a ring homomorphism.

The point of allowing `|z| < 1` is that `z` may afterwards be specialized to a power of `Q` itself: this gives
the Appell–Lerch form of Watson's `ψ` (`z = Q`, base `Q⁴`) in `PsiAL.lean`.
-/
import RamanujanTau.MockCusp.FAL

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Function Set PowerSeries Taylor
open scoped Topology Nat

noncomputable section

/-! ### rescaling the variable -/

lemma mapsTo_scale {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) : MapsTo (fun u : ℂ => ρ * u) (ball (0 : ℂ) 1) (ball 0 1) := by
  intro u hu
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_mul]
  calc ‖ρ‖ * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
    _ < 1 := by simpa using hu

lemma hol_scale {F : ℂ → ℂ} (hF : Hol F) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) : Hol (fun u => F (ρ * u)) :=
  hF.comp ((differentiableOn_const ρ).mul differentiableOn_id) (mapsTo_scale hρ)

/-- **Taylor series commute with rescaling.** -/
lemma T_scale {F : ℂ → ℂ} (hF : Hol F) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    T (fun u => F (ρ * u)) = rescale ρ (T F) := by
  ext n
  rw [coeff_T, coeff_rescale, coeff_T]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have h1 := iteratedDerivWithin_comp_const_smul (n := n) h0 isOpen_ball.uniqueDiffOn
    (hF.contDiffOn isOpen_ball) ρ (mapsTo_scale hρ)
  simp only [mul_zero] at h1
  rw [iteratedDerivWithin_of_isOpen isOpen_ball h0, iteratedDerivWithin_of_isOpen isOpen_ball h0,
    smul_eq_mul] at h1
  rw [h1]; ring

/-! ### the two sides -/

/-- `(cQ;Q)_n = ∏_{i<n}(1 − cQ^{1+i})`. -/
def pc (c : ℂ) (n : ℕ) (Q : ℂ) : ℂ := ∏ i ∈ Finset.range n, (1 - c * Q ^ (1 + i))

/-- `Q^{n²}/((zQ;Q)_n(Q/z;Q)_n)`. -/
def rT (z : ℂ) (n : ℕ) (Q : ℂ) : ℂ := Q ^ (n ^ 2) * (pc z n Q)⁻¹ * (pc z⁻¹ n Q)⁻¹

/-- the rank generating function `R(z;Q) = Σ_n Q^{n²}/((zQ;Q)_n(Q/z;Q)_n)`. -/
def Rd (z Q : ℂ) : ℂ := ∑' n, rT z n Q

/-- `(1 − zQ^{n+1})(1 − z⁻¹Q^{n+1})`. -/
def hq (z : ℂ) (n : ℕ) (Q : ℂ) : ℂ := (1 - z * Q ^ (n + 1)) * (1 - z⁻¹ * Q ^ (n + 1))

/-- the `r = n+1` term of the Appell–Lerch side. -/
def aT (z : ℂ) (n : ℕ) (Q : ℂ) : ℂ :=
  (-1) ^ (n + 1) * ((1 - z) * (1 - z⁻¹)) * (Q ^ eN n * (1 + Q ^ (n + 1))) * (hq z n Q)⁻¹

/-- `1 + Σ_{r≥1} (−1)^r Q^{r(3r+1)/2}(1+Q^r)(1−z)(1−z⁻¹)/((1−zQ^r)(1−Q^r/z))`. -/
def Ad (z Q : ℂ) : ℂ := 1 + ∑' n, aT z n Q

/-! ### bounds on the rescaled disc -/

section Bounds
variable {ρ u : ℂ} {r : ℝ}

lemma lin_lower {c : ℂ} (hc : ‖c‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r) (hr : r < 1) {k : ℕ}
    (hk : 1 ≤ k) : 1 - r ≤ ‖1 - c * (ρ * u) ^ k‖ := by
  have hu1 : ‖u‖ ≤ 1 := hu.trans hr.le
  have hw : ‖c * (ρ * u) ^ k‖ ≤ r := by
    rw [norm_mul, norm_pow, norm_mul, mul_pow]
    have h1 : ‖ρ‖ ^ k ≤ ‖ρ‖ := pow_le_of_le_one (norm_nonneg _) hρ (by omega)
    have h2 : ‖u‖ ^ k ≤ ‖u‖ := pow_le_of_le_one (norm_nonneg _) hu1 (by omega)
    calc ‖c‖ * (‖ρ‖ ^ k * ‖u‖ ^ k) ≤ ‖c‖ * (‖ρ‖ * ‖u‖) := by gcongr
      _ = (‖c‖ * ‖ρ‖) * ‖u‖ := by ring
      _ ≤ 1 * r := by gcongr
      _ = r := one_mul r
  have := norm_sub_norm_le (1 : ℂ) (c * (ρ * u) ^ k)
  rw [norm_one] at this
  linarith

lemma pc_lower {c : ℂ} (hc : ‖c‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r) (hr : r < 1) (n : ℕ) :
    (1 - r) ^ n ≤ ‖pc c n (ρ * u)‖ := by
  rw [pc, norm_prod, show (1 - r) ^ n = ∏ _i ∈ Finset.range n, (1 - r) by simp]
  exact Finset.prod_le_prod (fun _ _ => by linarith) fun i _ => lin_lower hc hρ hu hr (k := 1 + i) (by omega)

lemma pc_ne {c : ℂ} (hc : ‖c‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : u ∈ ball (0 : ℂ) 1) (n : ℕ) :
    pc c n (ρ * u) ≠ 0 := by
  have hu1 : ‖u‖ < 1 := by simpa using hu
  have := pc_lower hc hρ le_rfl hu1 n
  intro h; rw [h, norm_zero] at this
  have : 0 < (1 - ‖u‖) ^ n := pow_pos (by linarith) n
  linarith

lemma hq_lower {z : ℂ} (hz1 : ‖z‖ * ‖ρ‖ ≤ 1) (hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r)
    (hr : r < 1) (n : ℕ) : (1 - r) ^ 2 ≤ ‖hq z n (ρ * u)‖ := by
  rw [hq, norm_mul, sq]
  have h1 := lin_lower hz1 hρ hu hr (k := n + 1) (by omega)
  have h2 := lin_lower hz2 hρ hu hr (k := n + 1) (by omega)
  exact mul_le_mul h1 h2 (by linarith) (norm_nonneg _)

lemma hq_ne {z : ℂ} (hz1 : ‖z‖ * ‖ρ‖ ≤ 1) (hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1)
    (hu : u ∈ ball (0 : ℂ) 1) (n : ℕ) : hq z n (ρ * u) ≠ 0 := by
  have hu1 : ‖u‖ < 1 := by simpa using hu
  have := hq_lower hz1 hz2 hρ le_rfl hu1 n
  intro h; rw [h, norm_zero] at this
  have : 0 < (1 - ‖u‖) ^ 2 := pow_pos (by linarith) 2
  linarith

lemma norm_scale_pow (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r) (hr : r < 1) (m : ℕ) : ‖(ρ * u) ^ m‖ ≤ r ^ m := by
  rw [norm_pow, norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  calc ‖ρ‖ * ‖u‖ ≤ 1 * r := by gcongr
    _ = r := one_mul r

lemma rT_bound {z : ℂ} (hz1 : ‖z‖ * ‖ρ‖ ≤ 1) (hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r)
    (hr : r < 1) (n : ℕ) : ‖rT z n (ρ * u)‖ ≤ r ^ (n ^ 2) * (((1 - r) ^ 2)⁻¹) ^ n := by
  have hr1 : 0 < 1 - r := by linarith
  rw [rT, norm_mul, norm_mul, norm_inv, norm_inv]
  have e1 := pc_lower hz1 hρ hu hr n
  have e2 := pc_lower hz2 hρ hu hr n
  have i1 : ‖pc z n (ρ * u)‖⁻¹ ≤ ((1 - r) ^ n)⁻¹ := inv_anti₀ (by positivity) e1
  have i2 : ‖pc z⁻¹ n (ρ * u)‖⁻¹ ≤ ((1 - r) ^ n)⁻¹ := inv_anti₀ (by positivity) e2
  have hr0 : 0 ≤ r := (norm_nonneg u).trans hu
  have e0 := norm_scale_pow hρ hu hr (n ^ 2)
  have hp : ((1 - r) ^ 2) ^ n = (1 - r) ^ n * (1 - r) ^ n := by rw [← pow_mul, ← pow_add]; ring_nf
  calc ‖(ρ * u) ^ (n ^ 2)‖ * ‖pc z n (ρ * u)‖⁻¹ * ‖pc z⁻¹ n (ρ * u)‖⁻¹
      ≤ r ^ (n ^ 2) * ((1 - r) ^ n)⁻¹ * ((1 - r) ^ n)⁻¹ := by gcongr
    _ = r ^ (n ^ 2) * (((1 - r) ^ 2)⁻¹) ^ n := by rw [inv_pow, hp, mul_inv]; ring

lemma aT_bound {z : ℂ} (hz1 : ‖z‖ * ‖ρ‖ ≤ 1) (hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1) (hu : ‖u‖ ≤ r)
    (hr : r < 1) (n : ℕ) :
    ‖aT z n (ρ * u)‖ ≤ ‖1 - z‖ * ‖1 - z⁻¹‖ * 2 * ((1 - r) ^ 2)⁻¹ * r ^ n := by
  have hr1 : 0 < 1 - r := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg u).trans hu
  simp only [aT, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv]
  have e1 : ‖(ρ * u) ^ eN n‖ ≤ r ^ n :=
    (norm_scale_pow hρ hu hr _).trans (pow_le_pow_of_le_one hr0 hr.le (by have := eN_ge n; omega))
  have e2 : ‖1 + (ρ * u) ^ (n + 1)‖ ≤ 2 := by
    have := norm_add_le (1 : ℂ) ((ρ * u) ^ (n + 1))
    have h3 : ‖(ρ * u) ^ (n + 1)‖ ≤ 1 :=
      (norm_scale_pow hρ hu hr _).trans (pow_le_one₀ hr0 hr.le)
    rw [norm_one] at this; linarith
  have e3 : ‖hq z n (ρ * u)‖⁻¹ ≤ ((1 - r) ^ 2)⁻¹ := inv_anti₀ (by positivity) (hq_lower hz1 hz2 hρ hu hr n)
  rw [norm_pow, norm_mul] at e1
  calc ‖1 - z‖ * ‖1 - z⁻¹‖ * ((‖ρ‖ * ‖u‖) ^ eN n * ‖1 + (ρ * u) ^ (n + 1)‖) * ‖hq z n (ρ * u)‖⁻¹
      ≤ ‖1 - z‖ * ‖1 - z⁻¹‖ * (r ^ n * 2) * ((1 - r) ^ 2)⁻¹ := by gcongr
    _ = ‖1 - z‖ * ‖1 - z⁻¹‖ * 2 * ((1 - r) ^ 2)⁻¹ * r ^ n := by ring

end Bounds

/-! ### Taylor series of the pieces -/

lemma T_Xpow (m : ℕ) : T (fun Q : ℂ => Q ^ m) = X ^ m := by
  rw [T_pow (f := fun Q : ℂ => Q) differentiableOn_id, T_id]

lemma hol_lin (c : ℂ) (k : ℕ) : Hol (fun Q : ℂ => 1 - c * Q ^ k) :=
  (differentiableOn_const _).sub ((differentiableOn_const _).mul (differentiableOn_id.pow _))

lemma T_lin (c : ℂ) (k : ℕ) : T (fun Q : ℂ => 1 - c * Q ^ k) = 1 - C c * X ^ k := by
  rw [T_sub (f := fun _ => (1 : ℂ)) (g := fun Q : ℂ => c * Q ^ k) (differentiableOn_const _)
    ((differentiableOn_const _).mul (differentiableOn_id.pow _)), T_const, map_one,
    T_mul (f := fun _ => c) (g := fun Q : ℂ => Q ^ k) (differentiableOn_const _) (differentiableOn_id.pow _),
    T_const, T_Xpow]

lemma hol_pc (c : ℂ) (n : ℕ) : Hol (pc c n) := by
  unfold pc
  induction n with
  | zero => simp only [Finset.range_zero, Finset.prod_empty]; exact differentiableOn_const _
  | succ n ih =>
    simp only [Finset.prod_range_succ]
    exact ih.mul (hol_lin c _)

lemma T_pc (c : ℂ) (n : ℕ) : T (pc c n) = CrankProof.poch c 1 n := by
  induction n with
  | zero => rw [CrankProof.poch_zero]; exact T_const 1
  | succ n ih =>
    have e : pc c (n + 1) = fun Q => pc c n Q * (1 - c * Q ^ (1 + n)) := by
      funext Q; simp only [pc, Finset.prod_range_succ]
    rw [e, T_mul (hol_pc c n) (hol_lin c _), ih, T_lin, CrankProof.poch_succ]

lemma rescale_inverse (ρ : ℂ) {p : PowerSeries ℂ} (hp : constantCoeff p ≠ 0) :
    (rescale ρ p)⁻¹ = rescale ρ (Ring.inverse p) := by
  have hu : IsUnit p := by rw [PowerSeries.isUnit_iff_constantCoeff]; exact hp.isUnit
  rw [CrankProof.map_inverse (rescale ρ) hu, inverse_eq_inv]
  have := coeff_rescale p ρ 0
  rw [pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply] at this
  rw [this]; exact hp

lemma cc_poch (c : ℂ) (n : ℕ) : constantCoeff (CrankProof.poch c 1 n) ≠ 0 :=
  (PowerSeries.isUnit_iff_constantCoeff.mp (CrankProof.isUnit_poch c le_rfl n)).ne_zero

lemma rescale_C' (ρ a : ℂ) : rescale ρ (C a) = C a := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

/-- the formal denominator `(1 − zX^{n+1})(1 − z⁻¹X^{n+1})`. -/
def hqF (z : ℂ) (n : ℕ) : PowerSeries ℂ := (1 - C z * X ^ (n + 1)) * (1 - C z⁻¹ * X ^ (n + 1))

/-- the formal `r = n+1` term, without its constant. -/
def GF (z : ℂ) (n : ℕ) : PowerSeries ℂ := X ^ eN n * (1 + X ^ (n + 1)) * Ring.inverse (hqF z n)

lemma cc_hqF (z : ℂ) (n : ℕ) : constantCoeff (hqF z n) ≠ 0 := by
  simp [hqF]

lemma ALser_sub_one (z : ℂ) (c N : ℕ) (hN : c ≤ N) :
    coeff c (RankProof.ALser z - 1) =
      coeff c (∑ n ∈ Finset.range N, C ((-1) ^ (n + 1) * ((1 - z) * (1 - z⁻¹))) * GF z n) := by
  rw [map_sub, RankProof.ALser, coeff_mk, Finset.sum_range_succ', ← Finset.sum_range_add_sum_Ico _ hN]
  simp only [show RankProof.αser z 0 = 1 by simp [RankProof.αser], ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, pow_zero, mul_one, map_add, add_sub_cancel_right]
  have htail : coeff c (∑ k ∈ Finset.Ico c N, C ((-1) ^ (k + 1) * ((1 - z) * (1 - z⁻¹))) * GF z k) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := (Finset.mem_Ico.mp hk).1
    have := eN_ge k
    rw [GF, ← mul_assoc, mul_comm (C _), mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  rw [htail, add_zero, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold RankProof.αser
  rw [if_neg (by omega), GF, eN_eq, hqF, pow_add]
  ring

/-! ### the rescaled transfer -/

section Scaled
variable {z ρ : ℂ} (hz : z ≠ 0) (hρ : ‖ρ‖ ≤ 1) (hz1 : ‖z‖ * ‖ρ‖ ≤ 1) (hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1)
include hρ hz1 hz2

lemma hol_rTs (n : ℕ) : Hol (fun u => rT z n (ρ * u)) := by
  have h1 : Hol (fun u : ℂ => (ρ * u) ^ (n ^ 2)) := hol_scale (differentiableOn_id.pow _) hρ
  have h2 : Hol (fun u => (pc z n (ρ * u))⁻¹) :=
    (hol_scale (hol_pc z n) hρ).inv fun u hu => pc_ne hz1 hρ hu n
  have h3 : Hol (fun u => (pc z⁻¹ n (ρ * u))⁻¹) :=
    (hol_scale (hol_pc z⁻¹ n) hρ).inv fun u hu => pc_ne hz2 hρ hu n
  exact (h1.mul h2).mul h3

lemma T_rTs (n : ℕ) : T (fun u => rT z n (ρ * u)) =
    rescale ρ (X ^ (n ^ 2) * Ring.inverse (CrankProof.poch z 1 n) * Ring.inverse (CrankProof.poch z⁻¹ 1 n)) := by
  have h1 : Hol (fun u : ℂ => (ρ * u) ^ (n ^ 2)) := hol_scale (differentiableOn_id.pow _) hρ
  have g2 := hol_scale (hol_pc z n) hρ
  have g3 := hol_scale (hol_pc z⁻¹ n) hρ
  have h2 : Hol (fun u => (pc z n (ρ * u))⁻¹) := g2.inv fun u hu => pc_ne hz1 hρ hu n
  have h3 : Hol (fun u => (pc z⁻¹ n (ρ * u))⁻¹) := g3.inv fun u hu => pc_ne hz2 hρ hu n
  have t1 := T_scale (F := fun Q : ℂ => Q ^ (n ^ 2)) (differentiableOn_id.pow _) hρ
  have t2 := T_scale (hol_pc z n) hρ
  have t3 := T_scale (hol_pc z⁻¹ n) hρ
  simp only at t1
  show T (fun u => (ρ * u) ^ (n ^ 2) * (pc z n (ρ * u))⁻¹ * (pc z⁻¹ n (ρ * u))⁻¹) = _
  rw [T_mul (f := fun u => (ρ * u) ^ (n ^ 2) * (pc z n (ρ * u))⁻¹) (g := fun u => (pc z⁻¹ n (ρ * u))⁻¹)
      (h1.mul h2) h3, T_mul (f := fun u => (ρ * u) ^ (n ^ 2)) (g := fun u => (pc z n (ρ * u))⁻¹) h1 h2,
    T_inv g2 (fun u hu => pc_ne hz1 hρ hu n),
    T_inv g3 (fun u hu => pc_ne hz2 hρ hu n), t1, t2, t3, T_Xpow, T_pc, T_pc,
    rescale_inverse ρ (cc_poch z n), rescale_inverse ρ (cc_poch z⁻¹ n), map_mul, map_mul]

lemma tlu_rTs : TendstoLocallyUniformlyOn (fun N u => ∑ n ∈ Finset.range N, rT z n (ρ * u))
    (fun u => ∑' n, rT z n (ρ * u)) atTop (ball 0 1) := by
  refine tlu_tsum_nat fun r h0 h1 => ⟨fun n => r ^ (n ^ 2) * (((1 - r) ^ 2)⁻¹) ^ n, ?_, fun n u hu => ?_⟩
  · exact summable_sq_mul_pow h0 h1 _ (by have : 0 < 1 - r := by linarith
                                          positivity)
  · exact rT_bound hz1 hz2 hρ hu h1 n

include hz in
lemma T_Rds : Hol (fun u => Rd z (ρ * u)) ∧ T (fun u => Rd z (ρ * u)) = rescale ρ (CrankProof.Dser z z⁻¹) := by
  have hT := tlu_rTs hρ hz1 hz2
  have hFh : ∀ N, Hol (fun u => ∑ n ∈ Finset.range N, rT z n (ρ * u)) := fun N =>
    DifferentiableOn.fun_sum fun n _ => hol_rTs hρ hz1 hz2 n
  refine ⟨Hol.of_tlu hT hFh, T_of_tlu hT hFh fun c => ?_⟩
  filter_upwards [eventually_ge_atTop (c + 1)] with N hN
  rw [T_sum _ _ fun n => hol_rTs hρ hz1 hz2 n]
  simp only [T_rTs hρ hz1 hz2, ← map_sum, coeff_rescale]
  congr 1
  rw [CrankProof.Dser, coeff_mk]
  simp only [mul_inv_cancel₀ hz, one_pow, map_one, one_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hN, map_add, map_sum (coeff c) _ (Finset.Ico _ _),
    Finset.sum_eq_zero (s := Finset.Ico (c + 1) N) fun k hk => by
      have := (Finset.mem_Ico.mp hk).1
      rw [mul_assoc, coeff_X_pow_mul', if_neg (by nlinarith)], add_zero]

lemma hol_aTs (n : ℕ) : Hol (fun u => aT z n (ρ * u)) := by
  have hg : Hol (fun Q : ℂ => Q ^ eN n * (1 + Q ^ (n + 1))) :=
    (differentiableOn_id.pow _).mul ((differentiableOn_const _).add (differentiableOn_id.pow _))
  have hh : Hol (hq z n) := (hol_lin z (n + 1)).mul (hol_lin z⁻¹ (n + 1))
  exact ((differentiableOn_const _).mul (hol_scale hg hρ)).mul
    ((hol_scale hh hρ).inv fun u hu => hq_ne hz1 hz2 hρ hu n)

lemma T_aTs (n : ℕ) : T (fun u => aT z n (ρ * u)) =
    rescale ρ (C ((-1) ^ (n + 1) * ((1 - z) * (1 - z⁻¹))) * GF z n) := by
  have hg : Hol (fun Q : ℂ => Q ^ eN n * (1 + Q ^ (n + 1))) :=
    (differentiableOn_id.pow _).mul ((differentiableOn_const _).add (differentiableOn_id.pow _))
  have hh : Hol (hq z n) := (hol_lin z (n + 1)).mul (hol_lin z⁻¹ (n + 1))
  have Tg : T (fun Q : ℂ => Q ^ eN n * (1 + Q ^ (n + 1))) = X ^ eN n * (1 + X ^ (n + 1)) := by
    rw [T_mul (f := fun Q : ℂ => Q ^ eN n) (g := fun Q : ℂ => 1 + Q ^ (n + 1)) (differentiableOn_id.pow _)
      ((differentiableOn_const _).add (differentiableOn_id.pow _)), T_Xpow,
      T_add (f := fun _ => (1 : ℂ)) (g := fun Q : ℂ => Q ^ (n + 1)) (differentiableOn_const _)
        (differentiableOn_id.pow _), T_const, T_Xpow, map_one]
  have Th : T (hq z n) = hqF z n := by
    show T (fun Q => (1 - z * Q ^ (n + 1)) * (1 - z⁻¹ * Q ^ (n + 1))) = _
    rw [T_mul (hol_lin z (n + 1)) (hol_lin z⁻¹ (n + 1)), T_lin, T_lin, hqF]
  have tg := T_scale hg hρ
  have th := T_scale hh hρ
  simp only at tg
  have hc : Hol (fun _ : ℂ => (-1 : ℂ) ^ (n + 1) * ((1 - z) * (1 - z⁻¹))) := differentiableOn_const _
  show T (fun u => (fun _ => (-1 : ℂ) ^ (n + 1) * ((1 - z) * (1 - z⁻¹))) u *
    (fun u => (ρ * u) ^ eN n * (1 + (ρ * u) ^ (n + 1))) u * (fun u => (hq z n (ρ * u))⁻¹) u) = _
  rw [T_mul (f := fun u => (-1 : ℂ) ^ (n + 1) * ((1 - z) * (1 - z⁻¹)) * ((ρ * u) ^ eN n * (1 + (ρ * u) ^ (n + 1))))
      (g := fun u => (hq z n (ρ * u))⁻¹)
      (hc.mul (hol_scale hg hρ)) ((hol_scale hh hρ).inv fun u hu => hq_ne hz1 hz2 hρ hu n),
    T_mul (f := fun _ => (-1 : ℂ) ^ (n + 1) * ((1 - z) * (1 - z⁻¹)))
      (g := fun u => (ρ * u) ^ eN n * (1 + (ρ * u) ^ (n + 1))) hc (hol_scale hg hρ), T_inv (hol_scale hh hρ) (fun u hu => hq_ne hz1 hz2 hρ hu n), tg, th, Tg, Th,
    T_const, rescale_inverse ρ (cc_hqF z n)]
  simp only [GF, map_mul, rescale_C']
  ring

lemma tlu_aTs : TendstoLocallyUniformlyOn (fun N u => ∑ n ∈ Finset.range N, aT z n (ρ * u))
    (fun u => ∑' n, aT z n (ρ * u)) atTop (ball 0 1) := by
  refine tlu_tsum_nat fun r h0 h1 =>
    ⟨fun n => ‖1 - z‖ * ‖1 - z⁻¹‖ * 2 * ((1 - r) ^ 2)⁻¹ * r ^ n, ?_, fun n u hu => ?_⟩
  · exact (summable_geometric_of_lt_one h0 h1).mul_left _
  · exact aT_bound hz1 hz2 hρ hu h1 n

lemma T_Ads : Hol (fun u => Ad z (ρ * u)) ∧ T (fun u => Ad z (ρ * u)) = rescale ρ (RankProof.ALser z) := by
  have hT := tlu_aTs hρ hz1 hz2
  have hFh : ∀ N, Hol (fun u => ∑ n ∈ Finset.range N, aT z n (ρ * u)) := fun N =>
    DifferentiableOn.fun_sum fun n _ => hol_aTs hρ hz1 hz2 n
  have hS := Hol.of_tlu hT hFh
  have hTS : T (fun u => ∑' n, aT z n (ρ * u)) = rescale ρ (RankProof.ALser z - 1) := by
    refine T_of_tlu hT hFh fun c => ?_
    filter_upwards [eventually_ge_atTop c] with N hN
    rw [T_sum _ _ fun n => hol_aTs hρ hz1 hz2 n]
    simp only [T_aTs hρ hz1 hz2, ← map_sum, coeff_rescale]
    rw [ALser_sub_one z c N hN]
  refine ⟨(differentiableOn_const _).add hS, ?_⟩
  show T (fun u => (fun _ => (1 : ℂ)) u + (fun u => ∑' n, aT z n (ρ * u)) u) = _
  rw [T_add (differentiableOn_const _) hS, T_const, hTS, map_sub, map_one, map_one]
  ring

end Scaled

/-- **the Appell–Lerch form of the rank generating function on a disc**: for `z ≠ 0` and
`|Q| < min(|z|, 1/|z|)`, `(Q;Q)_∞ R(z;Q) = 1 + Σ_{r≥1}(−1)^r Q^{r(3r+1)/2}(1+Q^r)(1−z)(1−z⁻¹)/((1−zQ^r)(1−Q^r/z))`. -/
theorem rank_disc {z Q : ℂ} (hz : z ≠ 0) (h1 : ‖Q‖ < ‖z‖) (h2 : ‖Q‖ * ‖z‖ < 1) :
    HardyRamanujan.Pq Q * Rd z Q = Ad z Q := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set ρr : ℝ := min ‖z‖ ‖z‖⁻¹ with hρr
  have hρ0 : 0 < ρr := lt_min hzn (inv_pos.mpr hzn)
  have hρ1 : ρr ≤ 1 := by
    rcases le_total ‖z‖ 1 with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)
  set ρ : ℂ := (ρr : ℂ)
  have hρn : ‖ρ‖ = ρr := by simp only [ρ, norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hρ : ‖ρ‖ ≤ 1 := hρn ▸ hρ1
  have hz1 : ‖z‖ * ‖ρ‖ ≤ 1 := by
    rw [hρn]
    calc ‖z‖ * ρr ≤ ‖z‖ * ‖z‖⁻¹ := by gcongr; exact min_le_right _ _
      _ = 1 := mul_inv_cancel₀ hzn.ne'
  have hz2 : ‖z⁻¹‖ * ‖ρ‖ ≤ 1 := by
    rw [hρn, norm_inv]
    calc ‖z‖⁻¹ * ρr ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr; exact min_le_left _ _
      _ = 1 := inv_mul_cancel₀ hzn.ne'
  have hQρ : ‖Q‖ < ρr := lt_min h1 (by rw [← one_div, lt_div_iff₀ hzn]; exact h2)
  have hρne : ρ ≠ 0 := by simp only [ρ]; exact_mod_cast hρ0.ne'
  set u := Q / ρ
  have hu : u ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, hρn, div_lt_one hρ0]; exact hQρ
  have hQ : ρ * u = Q := by simp only [u]; field_simp
  have hP : Hol HardyRamanujan.Pq := (Realize.realizes_Pinf 1 1 le_rfl le_rfl).diff
  have hR := T_Rds hz hρ hz1 hz2
  have hA := T_Ads hρ hz1 hz2
  have hPs := hol_scale hP hρ
  have hT : T (fun u => HardyRamanujan.Pq (ρ * u) * Rd z (ρ * u)) = T (fun u => Ad z (ρ * u)) := by
    rw [T_mul (f := fun u => HardyRamanujan.Pq (ρ * u)) (g := fun u => Rd z (ρ * u)) hPs hR.1, T_scale hP hρ,
      hR.2, hA.2, Pq_T, ← map_mul, RankProof.rank_AL hz, ← qfacInf_eq, ← mul_assoc]
    have hu : IsUnit MockTheta5.JTP.qfacInf := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [MockTheta5.JTP.qfacInf, MockTheta5.Bailey.qfac]
    rw [CrankProof.map_inverse _ hu, Ring.mul_inverse_cancel _ (hu.map _), one_mul]
  have := eq_of_T (f := fun u => HardyRamanujan.Pq (ρ * u) * Rd z (ρ * u)) (hPs.mul hR.1) hA.1 hT hu
  simpa only [hQ] using this

end

end MockCusp
