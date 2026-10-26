/-
# Taylor coefficients at `0` as a ring map to formal power series

For `f` holomorphic on the unit disc, `T f = Σ_n (f⁽ⁿ⁾(0)/n!) qⁿ ∈ ℂ⟦q⟧`. Then
* `T` is additive and multiplicative, `T (1/h) = (T h)⁻¹`, `T id = q`, `T c = c`;
* `T` commutes with locally uniform limits on the disc (Weierstrass);
* `f` is recovered from `T f` on the disc (Taylor), so `T f = T g` forces `f = g` there.

This turns a formal identity between q-series built from sums, products, quotients and limits into the
corresponding identity of holomorphic functions on `|q| < 1`.
-/
import RamanujanTau.Realize

set_option autoImplicit false

namespace Taylor
open Complex Filter Metric Function Set
open scoped Topology Nat

/-- the Taylor series at `0`. -/
noncomputable def T (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => iteratedDeriv n f 0 / n !

/-- holomorphic on the unit disc. -/
def Hol (f : ℂ → ℂ) : Prop := DifferentiableOn ℂ f (ball 0 1)

lemma Hol.contDiffAt {f : ℂ → ℂ} (hf : Hol f) (n : ℕ) : ContDiffAt ℂ n f 0 :=
  (hf.contDiffOn isOpen_ball).contDiffAt (ball_mem_nhds 0 one_pos)

lemma coeff_T (f : ℂ → ℂ) (n : ℕ) : PowerSeries.coeff n (T f) = iteratedDeriv n f 0 / n ! := by
  simp [T]

/-- **Taylor**: `f z = Σ (T f)ₙ zⁿ` on the disc. -/
lemma Hol.hasSum {f : ℂ → ℂ} (hf : Hol f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n => PowerSeries.coeff n (T f) * z ^ n) (f z) := by
  have H := Complex.hasSum_taylorSeries_on_ball hf hz
  convert H using 1
  funext n
  rw [coeff_T, sub_zero, smul_eq_mul, smul_eq_mul]; ring

theorem eq_of_T {f g : ℂ → ℂ} (hf : Hol f) (hg : Hol g) (h : T f = T g) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    f z = g z :=
  (hf.hasSum hz).unique (by rw [h]; exact hg.hasSum hz)

lemma T_add {f g : ℂ → ℂ} (hf : Hol f) (hg : Hol g) : T (fun z => f z + g z) = T f + T g := by
  ext n
  simp only [coeff_T, map_add]
  rw [iteratedDeriv_fun_add (hf.contDiffAt n) (hg.contDiffAt n), add_div]

lemma T_neg (f : ℂ → ℂ) : T (fun z => -f z) = -T f := by
  ext n; simp only [coeff_T, map_neg, iteratedDeriv_fun_neg, neg_div]

lemma T_sub {f g : ℂ → ℂ} (hf : Hol f) (hg : Hol g) : T (fun z => f z - g z) = T f - T g := by
  ext n
  simp only [coeff_T, map_sub]
  rw [iteratedDeriv_fun_sub (hf.contDiffAt n) (hg.contDiffAt n), sub_div]

lemma T_mul {f g : ℂ → ℂ} (hf : Hol f) (hg : Hol g) : T (fun z => f z * g z) = T f * T g := by
  ext n
  rw [coeff_T, iteratedDeriv_fun_mul (hf.contDiffAt n) (hg.contDiffAt n), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_T]
  have h := Nat.choose_mul_factorial_mul_factorial hin
  have h1 : (i ! : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i) ! : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n ! : ℂ) = n.choose i * i ! * (n - i) ! := by exact_mod_cast h.symm
  have h4 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin).ne'
  rw [h3]; field_simp

lemma T_const (c : ℂ) : T (fun _ => c) = PowerSeries.C c := by
  ext n
  rw [coeff_T, PowerSeries.coeff_C]
  rcases n with _ | n
  · simp
  · simp [iteratedDeriv_const]

lemma T_id : T (fun z => z) = PowerSeries.X := by
  ext n
  rw [coeff_T, PowerSeries.coeff_X]
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [iteratedDeriv_succ', iteratedDeriv_succ']
    simp

lemma T_pow {f : ℂ → ℂ} (hf : Hol f) (k : ℕ) : T (fun z => f z ^ k) = T f ^ k := by
  induction k with
  | zero => simpa using T_const 1
  | succ k ih =>
    have := T_mul (f := fun z => f z ^ k) (g := f) (hf.pow k) hf
    simp only [pow_succ]
    rw [this, ih]

lemma T_inv {h : ℂ → ℂ} (hh : Hol h) (h0 : ∀ z ∈ ball (0 : ℂ) 1, h z ≠ 0) :
    T (fun z => (h z)⁻¹) = (T h)⁻¹ := by
  have hi : Hol (fun z => (h z)⁻¹) := hh.inv h0
  have hm : T h * T (fun z => (h z)⁻¹) = 1 := by
    rw [← T_mul hh hi]
    have : (fun z => h z * (h z)⁻¹) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
      exact mul_inv_cancel₀ (h0 z hz)
    ext n
    rw [coeff_T, (RamanujanTau.DiscriminantBridge.eventuallyEq_iteratedDeriv this n).eq_of_nhds, ← coeff_T,
      T_const, map_one]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_T]
    simpa using h0 0 (mem_ball_self one_pos))).mpr (by rw [mul_comm]; exact hm)

/-- **Weierstrass**: `T` commutes with locally uniform limits on the disc. -/
lemma tendsto_coeff_T {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : TendstoLocallyUniformlyOn F f atTop (ball 0 1))
    (hFh : ∀ N, Hol (F N)) (n : ℕ) :
    Tendsto (fun N => PowerSeries.coeff n (T (F N))) atTop (𝓝 (PowerSeries.coeff n (T f))) := by
  simp only [coeff_T]
  exact ((RamanujanTau.DiscriminantBridge.tlu_iteratedDeriv isOpen_ball n hF hFh).tendsto_at
    (mem_ball_self one_pos)).div_const _

lemma Hol.of_tlu {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : TendstoLocallyUniformlyOn F f atTop (ball 0 1))
    (hFh : ∀ N, Hol (F N)) : Hol f :=
  hF.differentiableOn (Eventually.of_forall hFh) isOpen_ball

/-- a locally uniform limit whose Taylor coefficients stabilize to those of `G`. -/
lemma T_of_tlu {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {G : PowerSeries ℂ}
    (hF : TendstoLocallyUniformlyOn F f atTop (ball 0 1)) (hFh : ∀ N, Hol (F N))
    (hst : ∀ n, ∀ᶠ N in atTop, PowerSeries.coeff n (T (F N)) = PowerSeries.coeff n G) : T f = G := by
  ext n
  exact tendsto_nhds_unique (tendsto_coeff_T hF hFh n)
    (tendsto_const_nhds.congr' (EventuallyEq.symm (hst n)))

end Taylor
