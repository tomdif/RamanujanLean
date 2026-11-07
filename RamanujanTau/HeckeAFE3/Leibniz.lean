/-
# All `t`-derivatives of the Gamma ratio `R(t) = Γ(6+it+u)/Γ(6+it)`

Fix the line `u = x + iy`, `x ≥ −1`.

* `iteratedDeriv_line`: `∂_t^k [c F(6+it+v)] = c i^k F^{(k)}(6+it+v)` for `F` analytic on the slit plane;
* `Rf x t y = Γ(6+it+u)/Γ(6+it)`, `ell x t y = i(ψ(6+it+u) − ψ(6+it))`, `deriv R = ell · R`;
* `Rd x m t y`: the explicit recursion `Rd (m+1) = Σ_{i≤m} C(m,i) ell^{(i)} Rd (m−i)`;
* `iteratedDeriv_Rf`: `∂_t^m R = Rd m` (Leibniz, `iteratedDeriv_mul`);
* **`norm_Rd_le`**: `‖∂_t^m R(t)‖ ≤ B_m (1+|y|)^{3m} (1+|t|)^{−m} ‖R(t)‖` (symbol bound, all `m`).
-/
import RamanujanTau.HeckeAFE3.PsiK

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE3

open Complex Set Metric Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
open scoped Real

lemma line_mem_slit {v : ℂ} (hv : -1 ≤ v.re) (t : ℝ) : (6 + t * I) + v ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by simp; linarith))

lemma hasDerivAt_line_aff (v : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℝ => (6 + (w : ℂ) * I) + v) I t := by
  have := (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add 6 |>.add_const v
  simpa using this

lemma contDiff_aff (v : ℂ) (n : WithTop ℕ∞) : ContDiff ℝ n (fun w : ℝ => (6 + (w : ℂ) * I) + v) :=
  (contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)).add contDiff_const

lemma contDiff_line {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F slitPlane) {v : ℂ} (hv : -1 ≤ v.re)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun w : ℝ => F ((6 + w * I) + v)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact ((hF _ (line_mem_slit hv t)).contDiffAt.restrict_scalars ℝ).comp t
    ((contDiff_aff v n).contDiffAt)

theorem iteratedDeriv_line {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F slitPlane) {v : ℂ}
    (hv : -1 ≤ v.re) (k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun w : ℝ => c * F ((6 + w * I) + v)) =
      fun w : ℝ => c * I ^ k * iteratedDeriv k F ((6 + w * I) + v) := by
  induction k generalizing F c with
  | zero => funext w; simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun w : ℝ => c * F ((6 + w * I) + v)) =
        fun w : ℝ => (c * I) * deriv F ((6 + w * I) + v) := by
      funext w
      have h1 := ((hF _ (line_mem_slit hv w)).differentiableAt.hasDerivAt).comp w
        (hasDerivAt_line_aff v w)
      have h2 : HasDerivAt (fun w : ℝ => c * F ((6 + w * I) + v))
          (c * (deriv F ((6 + w * I) + v) * I)) w := h1.const_mul c
      rw [h2.deriv]; ring
    rw [hd, ih hF.deriv (c * I)]
    funext w
    rw [iteratedDeriv_succ']; ring

/-! ## The ratio and its logarithmic derivative -/

/-- `R(t) = Γ(6+it+u)/Γ(6+it)`, `u = x + iy`. -/
noncomputable def Rf (x t y : ℝ) : ℂ :=
  Gamma ((6 + t * I) + ((x : ℂ) + y * I)) / Gamma (6 + t * I)

/-- `ell(t) = i ψ(6+it+u) − i ψ(6+it)`. -/
noncomputable def ell (x t y : ℝ) : ℂ :=
  I * digamma ((6 + t * I) + ((x : ℂ) + y * I)) - I * digamma (6 + t * I)

/-- `ell^{(i)}` in closed form. -/
noncomputable def elld (x : ℝ) (i : ℕ) (t y : ℝ) : ℂ :=
  I ^ (i + 1) * (iteratedDeriv i digamma ((6 + t * I) + ((x : ℂ) + y * I)) -
    iteratedDeriv i digamma (6 + t * I))

lemma re_u (x y : ℝ) : ((x : ℂ) + y * I).re = x := by simp

lemma contDiff_ell {x : ℝ} (hx : -1 ≤ x) (y : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun t => ell x t y) := by
  have h1 := (contDiff_const (c := I)).mul
    (contDiff_line analyticOnNhd_digamma (v := (x : ℂ) + y * I) (by rw [re_u]; exact hx) n)
  have h2 := (contDiff_const (c := I)).mul
    (contDiff_line analyticOnNhd_digamma (v := 0) (by simp) n)
  simp only [add_zero] at h2
  exact h1.sub h2

theorem iteratedDeriv_ell {x : ℝ} (hx : -1 ≤ x) (y : ℝ) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun t => ell x t y) t = elld x i t y := by
  have hv : -1 ≤ ((x : ℂ) + y * I).re := by rw [re_u]; exact hx
  have h1 := iteratedDeriv_line analyticOnNhd_digamma hv i I
  have h2 := iteratedDeriv_line analyticOnNhd_digamma (v := 0) (by simp) i I
  simp only [add_zero] at h2
  have hc1 := (contDiff_const (c := I)).mul (contDiff_line analyticOnNhd_digamma hv i)
  have hc2 := (contDiff_const (c := I)).mul
    (contDiff_line analyticOnNhd_digamma (v := 0) (by simp) i)
  simp only [add_zero] at hc2
  have e : (fun t => ell x t y) = (fun w : ℝ => I * digamma ((6 + w * I) + ((x : ℂ) + y * I))) -
      (fun w : ℝ => I * digamma (6 + w * I)) := by funext w; rfl
  rw [e, iteratedDeriv_sub (hc1.contDiffAt) (hc2.contDiffAt), h1, h2]
  unfold elld; ring

lemma Gamma_line_ne (t : ℝ) : Gamma (6 + t * I) ≠ 0 := Gamma_line_ne_zero t

lemma contDiff_Rf {x : ℝ} (hx : -1 ≤ x) (y : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun t => Rf x t y) := by
  have h1 := contDiff_line analyticOnNhd_Gamma_slit (v := (x : ℂ) + y * I)
    (by rw [re_u]; exact hx) n
  have h2 := contDiff_line analyticOnNhd_Gamma_slit (v := 0) (by simp) n
  simp only [add_zero] at h2
  have e : (fun t => Rf x t y) = fun t : ℝ => Gamma ((6 + t * I) + ((x : ℂ) + y * I)) *
      (Gamma (6 + t * I))⁻¹ := by funext t; rw [Rf, div_eq_mul_inv]
  rw [e]
  exact h1.mul (h2.inv fun t => Gamma_line_ne t)

theorem hasDerivAt_Rf {x : ℝ} (hx : -1 ≤ x) (y t : ℝ) :
    HasDerivAt (fun t => Rf x t y) (ell x t y * Rf x t y) t := by
  have hA := hasDerivAt_Gamma_line hx y t
  have hB : HasDerivAt (fun w : ℝ => Gamma (6 + w * I)) (I * deriv Gamma (6 + t * I)) t := by
    have := hasDerivAt_Gamma_line (x := 0) (by norm_num) 0 t
    simpa using this
  have h := hA.div hB (Gamma_line_ne t)
  convert h using 1
  unfold ell Rf
  rw [deriv_Gamma_eq (shift_re_pos hx t y), deriv_Gamma_eq (by simp : (0:ℝ) < (6 + t * I).re)]
  have := Gamma_line_ne t
  field_simp

/-! ## The Leibniz recursion -/

/-- `Rd 0 = R`, `Rd (m+1) = Σ_{i ≤ m} C(m,i) ell^{(i)} Rd (m−i)`. -/
noncomputable def Rd (x : ℝ) : ℕ → ℝ → ℝ → ℂ
  | 0 => fun t y => Rf x t y
  | m + 1 => fun t y => ∑ i : Fin (m + 1), (m.choose i : ℂ) * elld x i t y * Rd x (m - i) t y
decreasing_by omega

lemma Rd_zero (x t y : ℝ) : Rd x 0 t y = Rf x t y := by rw [Rd]

lemma Rd_succ (x : ℝ) (m : ℕ) (t y : ℝ) :
    Rd x (m + 1) t y = ∑ i : Fin (m + 1), (m.choose i : ℂ) * elld x i t y * Rd x (m - i) t y := by
  rw [Rd]

theorem iteratedDeriv_Rf {x : ℝ} (hx : -1 ≤ x) (y : ℝ) (m : ℕ) :
    ∀ t : ℝ, iteratedDeriv m (fun t => Rf x t y) t = Rd x m t y := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | m
    · simp [Rd_zero]
    · rw [iteratedDeriv_succ']
      have hd : deriv (fun t => Rf x t y) = (fun t => ell x t y) * (fun t => Rf x t y) := by
        funext w; exact (hasDerivAt_Rf hx y w).deriv
      rw [hd, iteratedDeriv_mul ((contDiff_ell hx y m).contDiffAt) ((contDiff_Rf hx y m).contDiffAt),
        Rd_succ, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [iteratedDeriv_ell hx y i t, ih (m - i) (by omega) t]

/-! ## The symbol bound -/

lemma one_le_one_add_abs (y : ℝ) : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]

lemma norm_elld_le {x : ℝ} (hx : -1 ≤ x) (i : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t y : ℝ, ‖elld x i t y‖ ≤ D * (1 + |y|) ^ (i + 2) / (1 + |t|) ^ (i + 1) := by
  obtain ⟨D, hD0, hD⟩ := norm_iteratedDeriv_digamma_diff_le hx i
  refine ⟨D, hD0, fun t y => ?_⟩
  unfold elld
  rw [norm_mul, norm_pow, norm_I, one_pow, one_mul]
  exact hD t y

theorem norm_Rd_le {x : ℝ} (hx : -1 ≤ x) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t y : ℝ,
      ‖Rd x m t y‖ ≤ B * (1 + |y|) ^ (3 * m) / (1 + |t|) ^ m * ‖Rf x t y‖ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · exact ⟨1, zero_le_one, fun t y => by simp [Rd_zero]⟩
    · choose D hD0 hD using fun i : ℕ => norm_elld_le hx i
      choose B hB0 hB using fun i : Fin (m + 1) => ih (m - i) (by omega)
      refine ⟨∑ i : Fin (m + 1), (m.choose i : ℝ) * D i * B i, ?_, fun t y => ?_⟩
      · exact Finset.sum_nonneg fun i _ => by have := hD0 i; have := hB0 i; positivity
      have hy1 := one_le_one_add_abs y
      have ht1 := one_le_one_add_abs t
      have hR := norm_nonneg (Rf x t y)
      rw [Rd_succ, Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.2
      rw [norm_mul, norm_mul]
      have hc : ‖((m.choose i : ℕ) : ℂ)‖ = (m.choose i : ℝ) := by simp
      rw [hc]
      have h1 := hD i t y
      have h2 := hB i t y
      have hpow1 : (1 + |y|) ^ ((i : ℕ) + 2) * (1 + |y|) ^ (3 * (m - i)) ≤ (1 + |y|) ^ (3 * (m + 1)) := by
        rw [← pow_add]; exact pow_le_pow_right₀ hy1 (by omega)
      have hpow2 : (1 + |t|) ^ ((i : ℕ) + 1) * (1 + |t|) ^ (m - i) = (1 + |t|) ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      have hDi := hD0 i
      have hBi := hB0 i
      have step1 : (m.choose i : ℝ) * ‖elld x i t y‖ * ‖Rd x (m - i) t y‖
          ≤ (m.choose i : ℝ) * (D i * (1 + |y|) ^ ((i : ℕ) + 2) / (1 + |t|) ^ ((i : ℕ) + 1)) *
            (B i * (1 + |y|) ^ (3 * (m - i)) / (1 + |t|) ^ (m - i) * ‖Rf x t y‖) := by gcongr
      have hT0 : 0 < 1 + |t| := by positivity
      generalize (1 + |t|) = T at step1 hpow2 hT0 ⊢
      generalize (1 + |y|) = Y at step1 hpow1 ⊢
      have hK : 0 ≤ (m.choose i : ℝ) * D i * B i * ‖Rf x t y‖ / T ^ (m + 1) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hDi) hBi) hR)
          (pow_nonneg hT0.le _)
      refine step1.trans ?_
      calc (m.choose i : ℝ) * (D i * Y ^ ((i : ℕ) + 2) / T ^ ((i : ℕ) + 1)) *
            (B i * Y ^ (3 * (m - i)) / T ^ (m - i) * ‖Rf x t y‖)
          = (m.choose i : ℝ) * D i * B i * ‖Rf x t y‖ / (T ^ ((i : ℕ) + 1) * T ^ (m - i)) *
            (Y ^ ((i : ℕ) + 2) * Y ^ (3 * (m - i))) := by ring
        _ = (m.choose i : ℝ) * D i * B i * ‖Rf x t y‖ / T ^ (m + 1) *
            (Y ^ ((i : ℕ) + 2) * Y ^ (3 * (m - i))) := by rw [hpow2]
        _ ≤ (m.choose i : ℝ) * D i * B i * ‖Rf x t y‖ / T ^ (m + 1) * Y ^ (3 * (m + 1)) :=
            mul_le_mul_of_nonneg_left hpow1 hK
        _ = _ := by ring

end RamanujanTau.HeckeAFE3
