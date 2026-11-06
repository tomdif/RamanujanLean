/-
# Regularity of the arithmetic objects of `SKQFHyp` in the lag `v`

* `continuous_NpC_line`, `continuous_DpC_line`: `v ↦ N_p(a, 1−iv)`, `v ↦ D_p(1−iv)` are continuous
  (Weierstrass M-test: the `j`-th term has modulus `|λ(p^{j+a})λ(p^j)| p^{−j}`, independent of `v`);
* `measurable_rhoC_line`, `measurable_Sv`, `continuous_S0v`, `measurable_Av`: hence `𝒮`, `𝒮⁰`, and
  `v ↦ 𝒜(v, L)` are (Borel) measurable (no non-vanishing of `D_p` is needed: division is total).
Level 1.
-/
import RamanujanTau.SelbergKey.Arith
import RamanujanTau.HafnerBridge.Local

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag

open Complex MeasureTheory
open RamanujanTau.SelbergKey

lemma norm_cpow_line {p : ℕ} (hp : 0 < p) (j : ℕ) (v : ℝ) :
    ‖(p : ℂ) ^ (-((j : ℂ) * (1 - v * I)))‖ = (p : ℝ) ^ (-(j : ℝ)) := by
  rw [norm_natCast_cpow_of_pos hp]
  congr 1
  simp

lemma continuous_cpow_line {p : ℕ} (hp : 0 < p) (j : ℕ) :
    Continuous fun v : ℝ => (p : ℂ) ^ (-((j : ℂ) * (1 - v * I))) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  exact Continuous.const_cpow (by fun_prop) (Or.inl hp')

theorem continuous_NpC_line {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Continuous fun v : ℝ => NpC p a (1 - v * I) := by
  unfold NpC
  refine continuous_tsum (fun j => continuous_const.mul (continuous_cpow_line hp.pos j))
    (HafnerBridge.summable_Np hp a).abs fun j v => ?_
  have hpos : (0:ℝ) ≤ (p : ℝ) ^ (-(j : ℝ)) := by positivity
  rw [norm_mul, norm_cpow_line hp.pos, Complex.norm_real, Real.norm_eq_abs]
  refine le_of_eq ?_
  rw [abs_mul _ ((p : ℝ) ^ (-(j : ℝ))), abs_of_nonneg hpos]

theorem continuous_DpC_line {p : ℕ} (hp : p.Prime) :
    Continuous fun v : ℝ => DpC p (1 - v * I) := by
  unfold DpC
  refine continuous_tsum (fun j => continuous_const.mul (continuous_cpow_line hp.pos j))
    (HafnerBridge.summable_Dp hp).abs fun j v => ?_
  have hpos : (0:ℝ) ≤ (p : ℝ) ^ (-(j : ℝ)) := by positivity
  rw [norm_mul, norm_cpow_line hp.pos, Complex.norm_real, Real.norm_eq_abs]
  refine le_of_eq ?_
  rw [abs_mul _ ((p : ℝ) ^ (-(j : ℝ))), abs_of_nonneg hpos]

theorem measurable_rhoC_line (m : ℕ) : Measurable fun v : ℝ => rhoC m (1 - v * I) := by
  unfold rhoC
  refine Finset.measurable_prod _ fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact (continuous_NpC_line hpp _).measurable.div (continuous_DpC_line hpp).measurable

lemma continuous_ev (a b c d : ℕ) : Continuous fun v : ℝ => ev a b c d v := by
  unfold ev; fun_prop

theorem measurable_Sv (y : ℕ) : Measurable fun v : ℝ => Sv y v := by
  unfold Sv sum4
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun d _ => ?_
  exact ((measurable_const.mul (continuous_ev a b c d).measurable).mul
    (measurable_rhoC_line _)).mul (measurable_rhoC_line _)

theorem continuous_S0v (y : ℕ) : Continuous fun v : ℝ => S0v y v := by
  unfold S0v sum4
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
  have := continuous_ev a b c d
  fun_prop

theorem measurable_Av (y : ℕ) (L : ℝ) : Measurable fun v : ℝ => Av y v L := by
  unfold Av
  have h1 : Measurable fun v : ℝ => (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I) :=
    measurable_const.div (by fun_prop)
  have h2 : Continuous fun v : ℝ => ((Real.exp (-(v ^ 2 / 4)) : ℝ) : ℂ) := by fun_prop
  have h3 : Continuous fun v : ℝ => cexp (-((v * L : ℝ) : ℂ) * I) := by fun_prop
  have hS := measurable_Sv y
  have hS0 := (continuous_S0v y).measurable
  exact (h1.mul ((h2.measurable.mul hS0).sub (h3.measurable.mul hS))).add
    ((measurable_const.mul h3.measurable).mul hS)

theorem measurable_reAv (y : ℕ) (L : ℝ) : Measurable fun v : ℝ => (Av y v L).re :=
  Complex.measurable_re.comp (measurable_Av y L)

end RamanujanTau.SelbergKeyDiag
