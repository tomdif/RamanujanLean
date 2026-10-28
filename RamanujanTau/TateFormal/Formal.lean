import RamanujanTau.TateFormal.Analytic
import RamanujanTau.TateFormal.Ident
import RamanujanTau.TateFormal.Val
import RamanujanTau.TateCurve.Basic

/-!
# The Tate parametrization as a formal identity over `ℤ[u, u⁻¹]⟦q⟧`

With `A = ℤ[u, u⁻¹]` and (`x̌ = (u−1)² x`, `y̌ = (u−1)³ y`, `q̌ = 2y̌ + (u−1)x̌ = (u−1)³(2y + x)`)
* `x̌ = u + (u−1)² Σ_N Σ_{d∣N} d (uᵈ + u⁻ᵈ − 2) qᴺ`,
* `q̌ = −u(1+u) + (u−1)³ Σ_N Σ_{d∣N} d² (uᵈ − u⁻ᵈ) qᴺ`,
we prove `q̌² = 4x̌³ + (u−1)² x̌² + 4a₄ (u−1)⁴ x̌ + 4a₆ (u−1)⁶` (`EA_eq_zero`), by evaluating at
complex `u = e^{2πiz}`, `q = e^{2πiτ}` (`0 < Im z < Im τ`) and using `℘'² = 4℘³ − g₂℘ − g₃`.
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open PowerSeries
open scoped ArithmeticFunction.sigma

/-- `A = ℤ[u, u⁻¹]`. -/
abbrev A := LaurentPolynomial ℤ

local notation "LT" => LaurentPolynomial.T (R := ℤ)

/-- `u`. -/
def U : A := LT 1

def Pc (N : ℕ) : A := ∑ d ∈ N.divisors, (d : A) * (LT d + LT (-d) - 2)
def Qc (N : ℕ) : A := ∑ d ∈ N.divisors, (d : A) ^ 2 * (LT d - LT (-d))
def Yc (N : ℕ) : A :=
  ∑ d ∈ N.divisors, ((d.choose 2 : A) * LT d - ((d + 1).choose 2 : A) * LT (-d) + d)

/-- `x̌ = (u−1)² x`. -/
def xA : PowerSeries A := C U + C ((U - 1) ^ 2) * mk Pc
/-- `q̌ = (u−1)³ (2y + x)`. -/
def qA : PowerSeries A := C (-(U * (1 + U))) + C ((U - 1) ^ 3) * mk Qc
/-- `y̌ = (u−1)³ y`. -/
def yA : PowerSeries A := C (-(U ^ 2)) + C ((U - 1) ^ 3) * mk Yc

def a4A : PowerSeries A := PowerSeries.map (Int.castRingHom A) TateCurve.a4
def a6A : PowerSeries A := PowerSeries.map (Int.castRingHom A) TateCurve.a6

/-- the Weierstrass defect (times `4 (u−1)⁶`). -/
def EA : PowerSeries A :=
  qA ^ 2 - (4 * xA ^ 3 + C ((U - 1) ^ 2) * xA ^ 2 + 4 * C ((U - 1) ^ 4) * a4A * xA +
    4 * C ((U - 1) ^ 6) * a6A)

/-! ## evaluation at a complex `u` -/

/-- evaluation `A → ℂ` at `u ≠ 0`. -/
def ev (u : ℂ) (hu : u ≠ 0) : A →+* ℂ := LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 u hu)

variable {u : ℂ} (hu : u ≠ 0)

lemma ev_T (n : ℤ) : ev u hu (LT n) = u ^ n := by
  rw [ev, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

lemma ev_T_nat (d : ℕ) : ev u hu (LT d) = u ^ d := by rw [ev_T, zpow_natCast]
lemma ev_T_neg (d : ℕ) : ev u hu (LT (-d)) = u⁻¹ ^ d := by rw [ev_T, zpow_neg, zpow_natCast, inv_pow]
lemma ev_U : ev u hu U = u := by rw [U, ev_T, zpow_one]

/-- `c j w N = Σ_{d ∣ N} d^j wᵈ`. -/
def c (j : ℕ) (w : ℂ) (N : ℕ) : ℂ := ∑ d ∈ N.divisors, (d : ℂ) ^ j * w ^ d

/-- the series `Σ_N c j w N qᴺ`. -/
def Cser (j : ℕ) (w : ℂ) : PowerSeries ℂ := mk (c j w)

lemma ev_Pc (N : ℕ) : ev u hu (Pc N) = c 1 u N + c 1 u⁻¹ N - 2 * c 1 1 N := by
  simp only [Pc, map_sum, map_mul, map_add, map_sub, map_natCast, map_ofNat, ev_T_nat, ev_T_neg, c,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp; ring

lemma ev_Qc (N : ℕ) : ev u hu (Qc N) = c 2 u N - c 2 u⁻¹ N := by
  simp only [Qc, map_sum, map_mul, map_sub, map_pow, map_natCast, ev_T_nat, ev_T_neg, c,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

lemma map_Pc : PowerSeries.map (ev u hu) (mk Pc) = Cser 1 u + Cser 1 u⁻¹ - C 2 * Cser 1 1 := by
  ext N; simp [Cser, ev_Pc, coeff_C_mul]

lemma map_Qc : PowerSeries.map (ev u hu) (mk Qc) = Cser 2 u - Cser 2 u⁻¹ := by
  ext N; simp [Cser, ev_Qc]

lemma map_xA : PowerSeries.map (ev u hu) xA =
    C u + C ((u - 1) ^ 2) * (Cser 1 u + Cser 1 u⁻¹ - C 2 * Cser 1 1) := by
  rw [xA, map_add, map_mul, map_C, map_C, map_Pc, map_pow, map_sub, map_one, ev_U]

lemma map_qA : PowerSeries.map (ev u hu) qA =
    C (-(u * (1 + u))) + C ((u - 1) ^ 3) * (Cser 2 u - Cser 2 u⁻¹) := by
  rw [qA, map_add, map_mul, map_C, map_C, map_Qc, map_pow, map_sub, map_one, map_neg, map_mul,
    map_add, map_one, ev_U]

lemma map_int (f : PowerSeries ℤ) :
    PowerSeries.map (ev u hu) (PowerSeries.map (Int.castRingHom A) f) =
      PowerSeries.map (Int.castRingHom ℂ) f := by
  ext N; simp [coeff_map]

lemma sigma_eq_c (k N : ℕ) : (σ k N : ℂ) = c k 1 N := by
  simp [c, ArithmeticFunction.sigma_apply]

lemma map_a4A : PowerSeries.map (ev u hu) a4A = C (-5) * Cser 3 1 := by
  rw [a4A, map_int]
  ext N
  simp only [TateCurve.a4, coeff_map, coeff_C_mul, Cser, coeff_mk]
  rw [show (-5 : PowerSeries ℤ) = C (-5) by simp, coeff_C_mul, TateCurve.coeff_s]
  simp only [eq_intCast]
  push_cast
  rw [sigma_eq_c]

lemma map_a6A : PowerSeries.map (ev u hu) a6A = C (-5 / 12) * Cser 3 1 + C (-7 / 12) * Cser 5 1 := by
  rw [a6A, map_int]
  ext N
  simp only [TateCurve.a6, coeff_map, coeff_mk, map_add, coeff_C_mul, Cser]
  have h := congrArg (Int.cast : ℤ → ℂ) (TateCurve.twelve_mul_a6coeff N)
  push_cast at h
  rw [sigma_eq_c, sigma_eq_c] at h
  simp only [eq_intCast, Int.cast_neg]
  linear_combination (-1 / 12 : ℂ) * h

/-! ## closed forms of `S₁`, `S₂` -/

lemma S1_eq {w : ℂ} (hw : ‖w‖ < 1) : S 1 w = w / (1 - w) ^ 2 := by
  rw [S]; simp only [pow_one]; exact tsum_coe_mul_geometric_of_norm_lt_one hw

lemma S2_eq {w : ℂ} (hw : ‖w‖ < 1) : S 2 w = w * (1 + w) / (1 - w) ^ 3 := by
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 2 hw
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 1 hw
  have h0 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 0 hw
  have h := ((h2.mul_left 2).sub (h1.mul_left 3)).add h0
  have hne : (1 - w) ≠ 0 := by
    intro h0; have : w = 1 := by linear_combination -h0
    rw [this, norm_one] at hw; exact lt_irrefl _ hw
  have e1 : (fun d : ℕ => (d : ℂ) ^ 2 * w ^ d) = fun b => 2 * (((b + 2).choose 2 : ℕ) * w ^ b) -
      3 * (((b + 1).choose 1 : ℕ) * w ^ b) + (((b + 0).choose 0 : ℕ) * w ^ b) := by
    funext n
    rw [Nat.cast_choose_two]
    simp only [Nat.choose_one_right, Nat.choose_zero_right]
    push_cast; ring
  rw [S, e1, h.tsum_eq, eq_div_iff (pow_ne_zero 3 hne)]
  have h3 : (1 / (1 - w) ^ (2 + 1)) * (1 - w) ^ 3 = 1 := by field_simp
  have h2' : (1 / (1 - w) ^ (1 + 1)) * (1 - w) ^ 3 = 1 - w := by field_simp
  have h1' : (1 / (1 - w) ^ (0 + 1)) * (1 - w) ^ 3 = (1 - w) ^ 2 := by
    rw [zero_add, pow_one]; field_simp
  linear_combination 2 * h3 - 3 * h2' + h1'

/-! ## values at `q = e τ` -/

section values
variable (τ : UpperHalfPlane) {z : ℂ} (hz0 : 0 < z.im) (hz1 : z.im < τ.im)
include hz0 hz1

lemma AC_Cser (j : ℕ) (w : ℂ) (hw : ‖w‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖) : AC (e τ) (Cser j w) := by
  unfold AC
  simpa [Cser, coeff_mk, c] using summable_coeff_norm j (r_lt τ hz1) (hq_le τ hz0) hw

lemma val_Cser (j : ℕ) (hj : 1 ≤ j) (w : ℂ) (hw : ‖w‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖) :
    val (e τ) (Cser j w) = T τ j w := by
  unfold val
  simpa [Cser, coeff_mk, c] using (regroup j hj (r_lt τ hz1) (hq_le τ hz0) hw).tsum_eq

lemma val_Cser_sigma (k : ℕ) (hk : 1 ≤ k) :
    val (e τ) (Cser k 1) = ∑' n : ℕ+, (σ k n : ℂ) * e τ ^ (n : ℕ) := by
  have hs := (regroup k hk (r_lt τ hz1) (hq_le τ hz0) (hw_one τ hz0)).summable
  unfold val
  rw [← tsum_zero_pnat_eq_tsum_nat (by simpa [Cser, coeff_mk, c] using hs)]
  simp [Cser, coeff_mk, c, sigma_eq_c]

omit hz0 hz1 in
lemma ez_ne : e z ≠ 0 := Complex.exp_ne_zero _

/-- **the evaluated defect vanishes**. -/
theorem val_EA : AC (e τ) (PowerSeries.map (ev (e z) ez_ne) EA) ∧
    val (e τ) (PowerSeries.map (ev (e z) ez_ne) EA) = 0 := by
  set u := e z with hu_def
  have hu : u ≠ 0 := ez_ne
  set R := acRing (e τ)
  let k : ℂ → R := fun a => ⟨C a, AC_C _ a⟩
  let c1u : R := ⟨Cser 1 u, AC_Cser τ hz0 hz1 1 u (hw_u τ hz0)⟩
  let c1i : R := ⟨Cser 1 u⁻¹, AC_Cser τ hz0 hz1 1 u⁻¹ (hw_inv τ)⟩
  let c11 : R := ⟨Cser 1 1, AC_Cser τ hz0 hz1 1 1 (hw_one τ hz0)⟩
  let c2u : R := ⟨Cser 2 u, AC_Cser τ hz0 hz1 2 u (hw_u τ hz0)⟩
  let c2i : R := ⟨Cser 2 u⁻¹, AC_Cser τ hz0 hz1 2 u⁻¹ (hw_inv τ)⟩
  let c31 : R := ⟨Cser 3 1, AC_Cser τ hz0 hz1 3 1 (hw_one τ hz0)⟩
  let c51 : R := ⟨Cser 5 1, AC_Cser τ hz0 hz1 5 1 (hw_one τ hz0)⟩
  let X : R := k u + k ((u - 1) ^ 2) * (c1u + c1i - k 2 * c11)
  let Q : R := k (-(u * (1 + u))) + k ((u - 1) ^ 3) * (c2u - c2i)
  let a4 : R := k (-5) * c31
  let a6 : R := k (-5 / 12) * c31 + k (-7 / 12) * c51
  let E : R := Q ^ 2 - (k 4 * X ^ 3 + k ((u - 1) ^ 2) * X ^ 2 + k 4 * k ((u - 1) ^ 4) * a4 * X +
    k 4 * k ((u - 1) ^ 6) * a6)
  have hE : PowerSeries.map (ev u hu) EA = (E : PowerSeries ℂ) := by
    simp only [EA, map_sub, map_add, map_mul, map_pow, map_ofNat, map_C, map_xA, map_qA, map_a4A,
      map_a6A, map_one, ev_U]
    simp only [E, X, Q, a4, a6, Subring.coe_add, Subring.coe_mul, Subring.coe_pow,
      AddSubgroupClass.coe_sub, k, c1u, c1i, c11, c2u, c2i, c31, c51]
    simp only [map_sub, map_pow, map_one, map_ofNat]
  have hval : ∀ f : R, val (e τ) (f : PowerSeries ℂ) = valHom (e τ) f := fun _ => rfl
  refine ⟨by rw [hE]; exact E.2, ?_⟩
  rw [hE, hval]
  have hk : ∀ a, valHom (e τ) (k a) = a := fun a => val_C _ a
  have v1u : valHom (e τ) c1u = T τ 1 u := val_Cser τ hz0 hz1 1 le_rfl u (hw_u τ hz0)
  have v1i : valHom (e τ) c1i = T τ 1 u⁻¹ := val_Cser τ hz0 hz1 1 le_rfl u⁻¹ (hw_inv τ)
  have v11 : valHom (e τ) c11 = T τ 1 1 := val_Cser τ hz0 hz1 1 le_rfl 1 (hw_one τ hz0)
  have v2u : valHom (e τ) c2u = T τ 2 u := val_Cser τ hz0 hz1 2 (by norm_num) u (hw_u τ hz0)
  have v2i : valHom (e τ) c2i = T τ 2 u⁻¹ := val_Cser τ hz0 hz1 2 (by norm_num) u⁻¹ (hw_inv τ)
  have v31 : valHom (e τ) c31 = ∑' n : ℕ+, (σ 3 n : ℂ) * e τ ^ (n : ℕ) :=
    val_Cser_sigma τ hz0 hz1 3 (by norm_num)
  have v51 : valHom (e τ) c51 = ∑' n : ℕ+, (σ 5 n : ℂ) * e τ ^ (n : ℕ) :=
    val_Cser_sigma τ hz0 hz1 5 (by norm_num)
  simp only [E, X, Q, a4, a6, map_sub, map_add, map_mul, map_pow, hk, v1u, v1i, v11, v2u,
    v2i, v31, v51]
  have hW := weierstrass_q τ hz0 hz1
  have hu1 : ‖u‖ < 1 := nu_lt hz0
  rw [S1_eq hu1, S2_eq hu1] at hW
  have hne : (1 - u) ≠ 0 := by
    intro h0; have : u = 1 := by linear_combination -h0
    rw [this, norm_one] at hu1; exact lt_irrefl _ hu1
  set s3 := ∑' n : ℕ+, (σ 3 n : ℂ) * e τ ^ (n : ℕ)
  set s5 := ∑' n : ℕ+, (σ 5 n : ℂ) * e τ ^ (n : ℕ)
  set X' := T τ 1 u + T τ 1 u⁻¹ - 2 * T τ 1 1
  set Q' := T τ 2 u - T τ 2 u⁻¹
  simp only [← hu_def] at hW
  have hne' : (u - 1) ≠ 0 := fun h => hne (by linear_combination -h)
  have hX : u + (u - 1) ^ 2 * X' = (u - 1) ^ 2 * (u / (1 - u) ^ 2 + T τ 1 u + T τ 1 u⁻¹ - 2 * T τ 1 1) := by
    simp only [X']; field_simp; ring
  have hQ : -(u * (1 + u)) + (u - 1) ^ 3 * Q' =
      (u - 1) ^ 3 * (u * (1 + u) / (1 - u) ^ 3 + T τ 2 u - T τ 2 u⁻¹) := by
    simp only [Q']
    have : (1 - u) ^ 3 = -(u - 1) ^ 3 := by ring
    rw [this]; field_simp; ring
  rw [hX, hQ]
  linear_combination (u - 1) ^ 6 * hW

end values

/-- every `0 < ‖q‖ < e^{-2πt}` is `e τ` with `Im τ > t`. -/
lemma exists_tau (q : ℂ) (hq0 : q ≠ 0) (t : ℝ) (ht : 0 ≤ t) (hq : ‖q‖ < Real.exp (-2 * Real.pi * t)) :
    ∃ τ : UpperHalfPlane, e τ = q ∧ t < τ.im := by
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hlog : Real.log ‖q‖ < -2 * Real.pi * t := by
    rw [Real.log_lt_iff_lt_exp hn]; exact hq
  set w : ℂ := ((Complex.arg q : ℂ) - Complex.I * Real.log ‖q‖) / (2 * Real.pi)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : w.im = -Real.log ‖q‖ / (2 * Real.pi) := by
    simp only [w]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
    simp
  have hwt : t < w.im := by
    rw [him, lt_div_iff₀ hpi]; nlinarith
  refine ⟨⟨w, by linarith⟩, ?_, hwt⟩
  show Complex.exp (2 * Real.pi * Complex.I * w) = q
  have : 2 * (Real.pi : ℂ) * Complex.I * w = Complex.log q := by
    simp only [w]
    rw [Complex.log]
    have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    linear_combination (-(Real.log ‖q‖ : ℂ)) * Complex.I_sq
  rw [this, Complex.exp_log hq0]

/-- **the Tate parametrization identity** over `ℤ[u, u⁻¹]⟦q⟧`. -/
theorem EA_eq_zero : EA = 0 := by
  refine PowerSeries.ext fun N => ?_
  rw [map_zero]
  set S : Set ℂ := ((↑) : ℝ → ℂ) '' Set.Ioo 0 1
  have hS : S.Infinite := (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
    (fun a _ b _ h => by exact_mod_cast h)
  have h0 : ∀ v ∈ S, v ≠ 0 := by
    rintro v ⟨x, hx, rfl⟩; exact_mod_cast hx.1.ne'
  apply laurent_eq_zero _ S hS h0
  rintro v ⟨x, hx, rfl⟩
  set t : ℝ := -Real.log x / (2 * Real.pi)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlogx : Real.log x < 0 := Real.log_neg hx.1 hx.2
  have ht : 0 < t := div_pos (by linarith) hpi
  set z : ℂ := Complex.I * t
  have hzim : z.im = t := by simp [z]
  have hez : e z = x := by
    show Complex.exp (2 * Real.pi * Complex.I * (Complex.I * t)) = x
    have : 2 * (Real.pi : ℂ) * Complex.I * (Complex.I * t) = (Real.log x : ℂ) := by
      simp only [t]; push_cast
      have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
      linear_combination (-(Real.log x : ℂ)) * Complex.I_sq
    rw [this, ← Complex.ofReal_exp, Real.exp_log hx.1]
  have hxt : Real.exp (-2 * Real.pi * t) = x := by
    rw [show -2 * Real.pi * t = Real.log x by simp only [t]; field_simp, Real.exp_log hx.1]
  have key : ∀ v (hv : v ≠ 0), v = e z → ev v hv (coeff N EA) = 0 := by
    rintro v hv rfl
    have hc := fun M => (coeff_map (ev (e z) hv) M EA).symm
    rw [← coeff_map]
    -- choose `ρ = x/2`
    obtain ⟨τ0, hτ0, hτ0t⟩ := exists_tau ((x / 2 : ℝ) : ℂ) (by exact_mod_cast (by linarith [hx.1] : x / 2 ≠ 0).symm.symm) t ht.le
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1]), hxt]; linarith [hx.1])
    have hAC := (val_EA τ0 (by rw [hzim]; exact ht) (by rw [hzim]; exact hτ0t)).1
    apply coeff_zero_of_vanish (fun M => coeff M (PowerSeries.map (ev (e z) ez_ne) EA)) ⟨x / 2, by linarith [hx.1]⟩
      (by show (0 : ℝ) < x / 2; linarith [hx.1])
    · have := hAC
      unfold AC at this
      rw [hτ0] at this
      refine this.congr fun M => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])]
      rfl
    · intro q hq0 hq
      obtain ⟨τ, hτ, hτt⟩ := exists_tau q hq0 t ht.le (by
        rw [hxt]; exact lt_trans (show ‖q‖ < x / 2 from hq) (by linarith [hx.1]))
      have := (val_EA τ (by rw [hzim]; exact ht) (by rw [hzim]; exact hτt)).2
      rw [hτ] at this
      exact this
  exact key _ _ hez.symm

end TateFormal
