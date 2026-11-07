/-
# Gaussian-windowed mean value of a real-coefficient Dirichlet polynomial: exact expansion

For `P(t) = ∑_{n ≤ N} aₙ n^{−it}` (`aₙ ∈ ℝ`) and `w(t) = e^{−((t−T)/H)²}`:

    ∫ w(t) |P(t)|² dt = H√π ∑_{m,n ≤ N} aₘ aₙ e^{−(H log(n/m))²/4} cos(T log(n/m))

(`integral_gw_normSq`), and grouping by `h = m − n` (`reindex_symm`), when `aₘ = 0` for `m > N`,

    |∫ w |P|²| ≤ H√π (∑ aₙ² + 2 ∑_{h=1}^{N} |S_h|),   S_h = ∑_n a_{n+h} aₙ k(n+h,n)

(`integral_gw_normSq_le`).
-/
import RamanujanTau.SubconvexityCond.Gauss
import RamanujanTau.MeanSquare.Poly

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Complex MeasureTheory Finset
open RamanujanTau.MeanSquare

/-- The real-coefficient Dirichlet polynomial `∑_{n=1}^{N} aₙ n^{−it}`. -/
noncomputable def rpoly (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℂ := dpoly (fun n => (a n : ℂ)) N t

lemma continuous_rpoly (a : ℕ → ℝ) (N : ℕ) : Continuous (rpoly a N) :=
  continuous_dpoly _ N

lemma re_ex (l t : ℝ) : (ex l t).re = Real.cos (l * t) := by
  unfold ex; rw [Complex.exp_ofReal_mul_I_re]

/-- `|P(t)|² = ∑_{m,n} aₘ aₙ cos((log n − log m) t)`. -/
lemma normSq_rpoly (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ‖rpoly a N t‖ ^ 2 = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      a m * a n * Real.cos ((Real.log n - Real.log m) * t) := by
  have h1 : ‖rpoly a N t‖ ^ 2 = (rpoly a N t * (starRingEnd ℂ) (rpoly a N t)).re := by
    rw [Complex.mul_conj, ← Complex.sq_norm]; norm_cast
  rw [h1]
  unfold rpoly dpoly
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_ex]
  have e : (a m : ℂ) * ex (-Real.log m) t * ((a n : ℂ) * ex (-(-Real.log n)) t) =
      ((a m * a n : ℝ) : ℂ) * ex (Real.log n - Real.log m) t := by
    rw [show Real.log n - Real.log m = -Real.log m + -(-Real.log n) by ring, ← ex_mul]
    push_cast; ring
  rw [e, re_ofReal_mul, re_ex]

/-- The Gaussian kernel `k(m,n) = e^{−(H log(n/m))²/4} cos(T log(n/m))`. -/
noncomputable def kw (H T : ℝ) (m n : ℕ) : ℝ :=
  Real.exp (-(H * (Real.log n - Real.log m)) ^ 2 / 4) * Real.cos ((Real.log n - Real.log m) * T)

lemma kw_symm (H T : ℝ) (m n : ℕ) : kw H T m n = kw H T n m := by
  unfold kw
  rw [show Real.log m - Real.log n = -(Real.log n - Real.log m) by ring, neg_mul, Real.cos_neg,
    mul_neg, neg_sq]

lemma kw_self (H T : ℝ) (n : ℕ) : kw H T n n = 1 := by simp [kw]

lemma integrable_term {H : ℝ} (hH : 0 < H) (T c l : ℝ) :
    Integrable fun t : ℝ => gw H T t * (c * Real.cos (l * t)) := by
  have := (integrable_gw_cos hH T l).const_mul c
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only; ring

lemma integrable_gw_normSq {H : ℝ} (hH : 0 < H) (T : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    Integrable fun t : ℝ => gw H T t * ‖rpoly a N t‖ ^ 2 := by
  simp_rw [normSq_rpoly, Finset.mul_sum]
  exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    integrable_term hH T _ _

/-- **Exact Gaussian mean value.** -/
theorem integral_gw_normSq {H : ℝ} (hH : 0 < H) (T : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    ∫ t : ℝ, gw H T t * ‖rpoly a N t‖ ^ 2 =
      H * Real.sqrt π * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * kw H T m n := by
  simp_rw [normSq_rpoly, Finset.mul_sum]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => integrable_term hH T _ _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => integrable_term hH T _ _]
  refine sum_congr rfl fun n _ => ?_
  have e : (fun t : ℝ => gw H T t * (a m * a n * Real.cos ((Real.log n - Real.log m) * t))) =
      fun t => (a m * a n) * (gw H T t * Real.cos ((Real.log n - Real.log m) * t)) := by
    funext t; ring
  rw [e, integral_const_mul, integral_gw_cos hH, kw]
  ring

/-- One row of the off-diagonal: `∑_{m ≤ N, m > n} F m n = ∑_{h=1}^{N} F (n+h) n`. -/
lemma row_reindex (F : ℕ → ℕ → ℝ) (N n : ℕ) (hv : ∀ m k, N < m → F m k = 0) :
    ∑ m ∈ Icc 1 N, (if n < m then F m n else 0) = ∑ h ∈ Icc 1 N, F (n + h) n := by
  rw [← Finset.sum_filter]
  have e1 : (Icc 1 N).filter (fun m => n < m) = Ioc n N := by
    ext m; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [e1]
  have e2 : ∑ h ∈ Icc 1 N, F (n + h) n = ∑ m ∈ (Icc 1 N).map (addLeftEmbedding n), F m n := by
    rw [Finset.sum_map]; rfl
  rw [e2]
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    simp only [mem_Ioc] at hm
    simp only [mem_map, mem_Icc, addLeftEmbedding_apply]
    exact ⟨m - n, by omega, by omega⟩
  · intro m hm hm'
    simp only [mem_map, mem_Icc, addLeftEmbedding_apply] at hm
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hm'
    obtain ⟨h, ⟨h1, h2⟩, rfl⟩ := hm
    exact hv _ _ (by omega)

/-- **Grouping a symmetric double sum by the difference `h = m − n`.** -/
lemma reindex_symm (F : ℕ → ℕ → ℝ) (N : ℕ) (hs : ∀ m n, F m n = F n m)
    (hv : ∀ m n, N < m → F m n = 0) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n =
      ∑ n ∈ Icc 1 N, F n n + 2 * ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F (n + h) n := by
  have split : ∀ m n, F m n = (if m < n then F m n else 0) + (if m = n then F m n else 0) +
      (if n < m then F m n else 0) := by
    intro m n
    rcases lt_trichotomy m n with h | rfl | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp
    · simp [h, h.ne', not_lt.2 h.le]
  have hsum : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then F m n else 0) +
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then F m n else 0) +
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n < m then F m n else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => split m n
  have h2 : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then F m n else 0) =
      ∑ n ∈ Icc 1 N, F n n := by
    refine sum_congr rfl fun m hm => ?_
    rw [Finset.sum_ite_eq]; simp [hm]
  have h1 : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then F m n else 0) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n < m then F m n else 0) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [hs]
  have h3 : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n < m then F m n else 0) =
      ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F (n + h) n := by
    rw [Finset.sum_comm]
    rw [show ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (if n < m then F m n else 0) =
        ∑ n ∈ Icc 1 N, ∑ h ∈ Icc 1 N, F (n + h) n from
      sum_congr rfl fun n _ => row_reindex F N n hv]
    exact Finset.sum_comm
  rw [hsum, h1, h2, h3]; ring

/-- The off-diagonal correlation `S_h = ∑_{n ≤ N} a_{n+h} aₙ k(n+h, n)`. -/
noncomputable def offS (a : ℕ → ℝ) (H T : ℝ) (N h : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, a (n + h) * a n * kw H T (n + h) n

/-- **Mean value ≤ diagonal + off-diagonal.** -/
theorem integral_gw_normSq_le {H : ℝ} (hH : 0 < H) (T : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ m, N < m → a m = 0) :
    ∫ t : ℝ, gw H T t * ‖rpoly a N t‖ ^ 2 ≤
      H * Real.sqrt π * (∑ n ∈ Icc 1 N, a n ^ 2 + 2 * ∑ h ∈ Icc 1 N, |offS a H T N h|) := by
  rw [integral_gw_normSq hH]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [reindex_symm (fun m n => a m * a n * kw H T m n) N
    (fun m n => by simp only; rw [kw_symm]; ring) (fun m n hm => by simp [ha m hm])]
  simp only [kw_self, mul_one]
  have : ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a (n + h) * a n * kw H T (n + h) n ≤
      ∑ h ∈ Icc 1 N, |offS a H T N h| :=
    sum_le_sum fun h _ => le_abs_self _
  have e : ∀ n, a n * a n = a n ^ 2 := fun n => (sq _).symm
  simp only [e]
  linarith

end RamanujanTau.SubconvexityCond
