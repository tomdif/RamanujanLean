/-
# GORZ Theorem 3 (general sequences) and its corollary (eventual hyperbolicity)

GORZ, Theorem 3, in the form used in their §5 (eq. (15)): let `α, A, δ` be real sequences, `α > 0`,
`δ > 0`, `δ → 0`, and suppose that for some `d` and all `0 ≤ j ≤ d`

  `log(α(n+j)/α(n)) = A(n) j − δ(n)² j² + Σ_{i=3}^{d} g_i(n) j^i + o(δ(n)^d)`,   `g_i(n) = o(δ(n)^i)`.

Then `Ĵ^{d,n}(X) = δ^{-d}/α(n) · J^{d,n}_α((δX − 1)/e^{A(n)}) → H_d(X)` uniformly on compact sets (GORZ's
Hermite polynomials, `e^{−t²+Xt} = Σ H_d(X) t^d/d!`), and `J^{d,n}_α` is hyperbolic for all large `n`.
(The arXiv statement, eq. (4), is the special case `g = 0`: `gorz_thm3_arxiv`.)

* `exp_poly_expansion` : the analytic core. If `log(α(n+j)/α(n)) − A j = Q_n(δ j) + o(δ^d)` for polynomials `Q_n`
  of bounded degree with `Q_n(0) = 0` whose coefficients converge (to `Q_∞`), then the hypothesis (8) of
  Theorem 6 holds with `C_i(n)` = coefficients of `P_n = Σ_{m≤d} Q_n^m/m!` (truncated exponential).
  Proof: `|e^a − e^b| ≤ 2e|a−b|`, `|e^x − Σ_{m≤d} x^m/m!| ≤ C|x|^{d+1}` with `x = Q_n(δj) = O(δ)`, and
  the monomials of `P_n` of degree `> d` are `o(δ^d)`.
* **`gorz_thm3`** : Theorem 3 + Corollary (coefficientwise, uniform on compacts, eventually hyperbolic).
* **`gorz_thm3_diff`** : an intrinsic variant through forward differences of `log α`: if
  `Δ²[log α](n)/δ² → −2` and `Δ^k[log α](n)/δ^k → 0` (`3 ≤ k ≤ d`), the same conclusions hold with
  `e^{A(n)} = α(n+1)/α(n)`. (Newton interpolation turns this into the polynomial form.)
-/
import RamanujanTau.GORZXi.Theorem6

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial Asymptotics JensenThreshold

/-! ## asymptotic helpers -/

section helpers

variable {δ : ℕ → ℝ}

lemma pow_isLittleO_pow (hδ0 : Tendsto δ atTop (𝓝 0)) {i d : ℕ} (h : d < i) :
    (fun n => δ n ^ i) =o[atTop] (fun n => δ n ^ d) := by
  have h1 : (fun n => δ n ^ (i - d)) =o[atTop] (fun _ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    have := hδ0.pow (i - d); rwa [zero_pow (by omega)] at this
  have h2 := h1.mul_isBigO (isBigO_refl (fun n => δ n ^ d) atTop)
  simp only [one_mul] at h2
  refine h2.congr_left fun n => ?_
  rw [← pow_add]; congr 1; omega

lemma pow_isBigO_self (hδ0 : Tendsto δ atTop (𝓝 0)) {i : ℕ} (h : 1 ≤ i) :
    (fun n => δ n ^ i) =O[atTop] δ := by
  have h1 : (fun n => δ n ^ (i - 1)) =O[atTop] (fun _ => (1 : ℝ)) := (hδ0.pow (i - 1)).isBigO_one ℝ
  have h2 := h1.mul (isBigO_refl δ atTop)
  simp only [one_mul] at h2
  refine h2.congr_left fun n => ?_
  rw [← pow_succ]; congr 1; omega

lemma bdd_mul_isLittleO {a b g : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) (hb : b =o[atTop] g) :
    (fun n => a n * b n) =o[atTop] g := by
  have := (ha.isBigO_one ℝ).mul_isLittleO hb
  simpa using this

lemma bdd_mul_isBigO {a b g : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) (hb : b =O[atTop] g) :
    (fun n => a n * b n) =O[atTop] g := by
  have := (ha.isBigO_one ℝ).mul hb
  simpa using this

end helpers

/-! ## coefficientwise convergence of polynomials is an algebra -/

/-- coefficientwise convergence `P n → Pl`. -/
def CoeffTo (P : ℕ → ℝ[X]) (Pl : ℝ[X]) : Prop :=
  ∀ i, Tendsto (fun n => (P n).coeff i) atTop (𝓝 (Pl.coeff i))

lemma CoeffTo.mul {P Q : ℕ → ℝ[X]} {Pl Ql : ℝ[X]} (hP : CoeffTo P Pl) (hQ : CoeffTo Q Ql) :
    CoeffTo (fun n => P n * Q n) (Pl * Ql) := by
  intro i
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)

lemma CoeffTo.pow {P : ℕ → ℝ[X]} {Pl : ℝ[X]} (hP : CoeffTo P Pl) (m : ℕ) :
    CoeffTo (fun n => P n ^ m) (Pl ^ m) := by
  induction m with
  | zero => intro i; simp only [pow_zero]; exact tendsto_const_nhds
  | succ m ih => simpa only [pow_succ] using ih.mul hP

lemma CoeffTo.C_mul {P : ℕ → ℝ[X]} {Pl : ℝ[X]} (hP : CoeffTo P Pl) (a : ℝ) :
    CoeffTo (fun n => C a * P n) (C a * Pl) := by
  intro i; simp only [coeff_C_mul]; exact (hP i).const_mul a

lemma CoeffTo.sum {ι : Type*} (s : Finset ι) {P : ι → ℕ → ℝ[X]} {Pl : ι → ℝ[X]}
    (h : ∀ m ∈ s, CoeffTo (P m) (Pl m)) : CoeffTo (fun n => ∑ m ∈ s, P m n) (∑ m ∈ s, Pl m) := by
  intro i; simp only [finsetSum_coeff]; exact tendsto_finsetSum _ fun m hm => h m hm i

/-- the truncated exponential `Σ_{m≤d} Q^m/m!`. -/
noncomputable def texp (d : ℕ) (Q : ℝ[X]) : ℝ[X] := ∑ m ∈ range (d + 1), C ((m.factorial : ℝ)⁻¹) * Q ^ m

lemma eval_texp (d : ℕ) (Q : ℝ[X]) (y : ℝ) :
    (texp d Q).eval y = ∑ m ∈ range (d + 1), (Q.eval y) ^ m / (m.factorial : ℝ) := by
  simp only [texp, eval_finsetSum, eval_mul, eval_C, eval_pow]
  refine sum_congr rfl fun m _ => ?_
  rw [div_eq_inv_mul]

lemma natDegree_texp_le (d D : ℕ) (Q : ℝ[X]) (hQ : Q.natDegree ≤ D) : (texp d Q).natDegree ≤ d * D := by
  unfold texp
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  have : m ≤ d := by have := Finset.mem_range.mp hm; omega
  exact Nat.mul_le_mul this hQ

/-! ## the analytic core -/

/-- **Exponential of a polynomial expansion** (the analytic content of Theorem 3). -/
theorem exp_poly_expansion {δ : ℕ → ℝ} {d D : ℕ} (hδ0 : Tendsto δ atTop (𝓝 0))
    (Q : ℕ → ℝ[X]) (Ql : ℝ[X]) (hdeg : ∀ n, (Q n).natDegree ≤ D) (h0 : ∀ᶠ n in atTop, (Q n).coeff 0 = 0)
    (hQ : CoeffTo Q Ql) (φ : ℕ → ℕ → ℝ)
    (hφ : ∀ j ≤ d, (fun n => φ n j - (Q n).eval (δ n * j)) =o[atTop] (fun n => δ n ^ d)) :
    CoeffTo (fun n => texp d (Q n)) (texp d Ql) ∧
    ∀ j ≤ d, (fun n => Real.exp (φ n j) -
        ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * δ n ^ i * (j : ℝ) ^ i) =o[atTop] (fun n => δ n ^ d) := by
  have hP : CoeffTo (fun n => texp d (Q n)) (texp d Ql) := by
    unfold texp
    exact CoeffTo.sum _ fun m _ => (hQ.pow m).C_mul _
  refine ⟨hP, fun j hj => ?_⟩
  set x : ℕ → ℝ := fun n => (Q n).eval (δ n * j) with hx
  -- `x = O(δ)`
  have hxO : x =O[atTop] δ := by
    have e : ∀ n, x n = ∑ i ∈ range (D + 1), (Q n).coeff i * (j : ℝ) ^ i * δ n ^ i := by
      intro n
      rw [hx]; dsimp only
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg n))]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow]; ring
    rw [show x = fun n => ∑ i ∈ range (D + 1), (Q n).coeff i * (j : ℝ) ^ i * δ n ^ i from funext e]
    refine IsBigO.sum fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      refine IsBigO.of_bound 0 ?_
      filter_upwards [h0] with n hn
      simp [hn]
    · exact bdd_mul_isBigO (((hQ i).mul_const ((j : ℝ) ^ i))) (pow_isBigO_self hδ0 hi)
  have hx0 : Tendsto x atTop (𝓝 0) := hxO.trans_tendsto hδ0
  -- term 1: `e^{φ} − e^{x}`
  have hT1 : (fun n => Real.exp (φ n j) - Real.exp (x n)) =o[atTop] (fun n => δ n ^ d) := by
    have hd0 : Tendsto (fun n => φ n j - x n) atTop (𝓝 0) := by
      have h := (hφ j hj).trans_isBigO ((hδ0.pow d).isBigO_one ℝ)
      exact (isLittleO_one_iff ℝ).mp h
    refine IsBigO.trans_isLittleO ?_ (hφ j hj)
    refine IsBigO.of_bound (2 * Real.exp 1) ?_
    filter_upwards [hd0.eventually (Metric.closedBall_mem_nhds 0 one_pos),
      hx0.eventually (Metric.closedBall_mem_nhds 0 one_pos)] with n hn hxn
    rw [Real.dist_0_eq_abs] at hn hxn
    simp only [Real.norm_eq_abs]
    have e : Real.exp (φ n j) - Real.exp (x n) = Real.exp (x n) * (Real.exp (φ n j - x n) - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    rw [e, abs_mul, Real.abs_exp]
    have h1 := Real.abs_exp_sub_one_le hn
    have h2 : Real.exp (x n) ≤ Real.exp 1 := Real.exp_le_exp.mpr ((le_abs_self _).trans hxn)
    calc Real.exp (x n) * |Real.exp (φ n j - x n) - 1| ≤ Real.exp 1 * (2 * |φ n j - x n|) :=
          mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
      _ = 2 * Real.exp 1 * |φ n j - x n| := by ring
  -- term 2: `e^{x} − Σ_{m≤d} x^m/m!`
  have hT2 : (fun n => Real.exp (x n) - (texp d (Q n)).eval (δ n * j)) =o[atTop] (fun n => δ n ^ d) := by
    have hpow : (fun n => x n ^ (d + 1)) =o[atTop] (fun n => δ n ^ d) :=
      (hxO.pow (d + 1)).trans_isLittleO (pow_isLittleO_pow hδ0 (Nat.lt_succ_self d))
    refine IsBigO.trans_isLittleO ?_ hpow
    refine IsBigO.of_bound (((d + 1).succ : ℝ) / ((d + 1).factorial * (d + 1))) ?_
    filter_upwards [hx0.eventually (Metric.closedBall_mem_nhds 0 one_pos)] with n hxn
    rw [Real.dist_0_eq_abs] at hxn
    simp only [Real.norm_eq_abs]
    rw [eval_texp, abs_pow]
    have := Real.exp_bound hxn (n := d + 1) (Nat.succ_pos d)
    simp only [hx] at this ⊢
    push_cast at this ⊢
    linarith [this]
  -- term 3: the monomials of degree `> d`
  have hT3 : (fun n => (texp d (Q n)).eval (δ n * j) -
      ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * δ n ^ i * (j : ℝ) ^ i) =o[atTop] (fun n => δ n ^ d) := by
    have hN : ∀ n, (texp d (Q n)).natDegree < d * D + d + 1 := fun n =>
      Nat.lt_succ_of_le ((natDegree_texp_le d D (Q n) (hdeg n)).trans (Nat.le_add_right _ _))
    have e : ∀ n, (texp d (Q n)).eval (δ n * j) -
        ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * δ n ^ i * (j : ℝ) ^ i =
        ∑ i ∈ Ico (d + 1) (d * D + d + 1), (texp d (Q n)).coeff i * (j : ℝ) ^ i * δ n ^ i := by
      intro n
      rw [eval_eq_sum_range' (hN n), ← Finset.sum_range_add_sum_Ico _ (show d + 1 ≤ d * D + d + 1 by omega)]
      have : ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * (δ n * j) ^ i =
          ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * δ n ^ i * (j : ℝ) ^ i :=
        sum_congr rfl fun i _ => by rw [mul_pow]; ring
      rw [this, add_sub_cancel_left]
      refine sum_congr rfl fun i _ => by rw [mul_pow]; ring
    rw [show (fun n => (texp d (Q n)).eval (δ n * j) -
        ∑ i ∈ range (d + 1), (texp d (Q n)).coeff i * δ n ^ i * (j : ℝ) ^ i) =
        fun n => ∑ i ∈ Ico (d + 1) (d * D + d + 1), (texp d (Q n)).coeff i * (j : ℝ) ^ i * δ n ^ i from funext e]
    refine IsLittleO.sum fun i hi => ?_
    have hi' : d < i := by simp only [mem_Ico] at hi; omega
    exact bdd_mul_isLittleO ((hP i).mul_const ((j : ℝ) ^ i)) (pow_isLittleO_pow hδ0 hi')
  have := (hT1.add hT2).add hT3
  refine this.congr_left fun n => ?_
  ring

/-! ## the Hermite limit: `k!·[y^k] Σ_{m≤d}(−y²)^m/m! = c_k` -/

lemma cH_even (m : ℕ) : GORZ.cH (2 * m) = (-1) ^ m * ((2 * m).factorial : ℝ) / (m.factorial : ℝ) := by
  induction m with
  | zero => simp [GORZ.cH_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, GORZ.cH_add_two, ih]
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ (2 * m),
      Nat.factorial_succ m]
    push_cast
    field_simp
    ring

lemma coeff_negX2_pow (m k : ℕ) : ((-X ^ 2 : ℝ[X]) ^ m).coeff k = if k = 2 * m then (-1) ^ m else 0 := by
  rw [neg_pow, ← pow_mul, show (-1 : ℝ[X]) ^ m = C ((-1) ^ m) by simp, coeff_C_mul_X_pow]

lemma factorial_mul_coeff_texp_negX2 {d k : ℕ} (hk : k ≤ d) :
    (k.factorial : ℝ) * (texp d (-X ^ 2)).coeff k = GORZ.cH k := by
  simp only [texp, finsetSum_coeff, coeff_C_mul, coeff_negX2_pow]
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm' : k = 2 * m := by omega
    subst hm'
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, cH_even]; field_simp
    · intro b _ hb; rw [if_neg (by omega), mul_zero]
    · intro hmr; exfalso; exact hmr (Finset.mem_range.mpr (by omega))
  · have : GORZ.cH k = 0 := by rw [hm]; exact GORZ.cH_odd m
    rw [this]
    rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (by omega), mul_zero], mul_zero]

/-! ## Theorem 3 -/

/-- from the polynomial form to `γ_k → c_k` (`E = e^{A}`). -/
theorem tendsto_gk_of_poly {α A δ : ℕ → ℝ} {d D : ℕ} (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδne : ∀ᶠ n in atTop, δ n ≠ 0) (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (Q : ℕ → ℝ[X]) (hdeg : ∀ n, (Q n).natDegree ≤ D) (h0 : ∀ᶠ n in atTop, (Q n).coeff 0 = 0)
    (hQ : CoeffTo Q (-X ^ 2))
    (hφ : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) - A n * j - (Q n).eval (δ n * j))
      =o[atTop] (fun n => δ n ^ d)) :
    ∀ k ≤ d, Tendsto (fun n => gk α (fun n => Real.exp (A n)) δ n k) atTop (𝓝 (GORZ.cH k)) := by
  obtain ⟨hP, herr⟩ := exp_poly_expansion (d := d) hδ0 Q (-X ^ 2) hdeg h0 hQ
    (fun n j => Real.log (α (n + j) / α n) - A n * j) hφ
  have hw : ∀ j, ∀ᶠ n in atTop, wr α (fun n => Real.exp (A n)) n j =
      Real.exp (Real.log (α (n + j) / α n) - A n * j) := by
    intro j
    obtain ⟨N, hN⟩ := eventually_atTop.mp hαpos
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 := hN n hn
    have h2 := hN (n + j) (by omega)
    rw [Real.exp_sub, Real.exp_log (div_pos h2 h1), wr, ← Real.exp_nat_mul, div_eq_mul_inv (α (n + j) / α n)]
    congr 2; ring_nf
  intro k hk
  have := tendsto_gk_of_thm6 (α := α) (E := fun n => Real.exp (A n)) (δ := δ) (d := d)
    (fun i => (texp d (-X ^ 2)).coeff i) (fun i n => (texp d (Q n)).coeff i) hδ0 hδne
    (fun i _ => hP i) (fun j hj => (herr j hj).congr' ((hw j).mono fun n hn => by beta_reduce; rw [hn]) EventuallyEq.rfl) k hk
  rwa [factorial_mul_coeff_texp_negX2 hk] at this

/-- conclusions of Theorem 3 from `γ_k → c_k`. -/
theorem conclusions_of_gk {α E δ : ℕ → ℝ} {d : ℕ} (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hEpos : ∀ᶠ n in atTop, 0 < E n) (hα : ∀ᶠ n in atTop, α n ≠ 0)
    (hγ : ∀ k ≤ d, Tendsto (fun n => gk α E δ n k) atTop (𝓝 (GORZ.cH k))) :
    (∀ i, Tendsto (fun n => (Jhat α E δ d n).coeff i) atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n x => (Jhat α E δ d n).eval x) (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n)) := by
  have hδne : ∀ᶠ n in atTop, δ n ≠ 0 := hδpos.mono fun n h => h.ne'
  refine ⟨fun i => ?_, fun K hK => ?_, eventually_hyperbolic_of_gk hδ0 hδpos hEpos hα hγ⟩
  · rw [← Hgen_cH]; exact tendsto_coeff_Jhat_of_gk hδ0 hδne hγ i
  · rw [← Hgen_cH]; exact tendstoUniformlyOn_Jhat_of_gk hδ0 hδne hγ hK

/-- the polynomial `−X² + Σ_{i=3}^{d} (g_i/δ^i) X^i`. -/
noncomputable def Qg (g : ℕ → ℕ → ℝ) (δ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  -X ^ 2 + ∑ i ∈ Icc 3 d, C (g i n / δ n ^ i) * X ^ i

/-- **GORZ Theorem 3** (form (15) of §5, which contains eq. (4) as `g = 0`) **and its Corollary.** -/
theorem gorz_thm3 (α A δ : ℕ → ℝ) (d : ℕ) (hδ0 : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hαpos : ∀ᶠ n in atTop, 0 < α n) (g : ℕ → ℕ → ℝ)
    (hg : ∀ i ∈ Icc 3 d, (fun n => g i n) =o[atTop] (fun n => δ n ^ i))
    (h : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) -
        (A n * j - δ n ^ 2 * (j : ℝ) ^ 2 + ∑ i ∈ Icc 3 d, g i n * (j : ℝ) ^ i)) =o[atTop] (fun n => δ n ^ d)) :
    (∀ i, Tendsto (fun n => (Jhat α (fun n => Real.exp (A n)) δ d n).coeff i) atTop
      (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat α (fun n => Real.exp (A n)) δ d n).eval x) (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n)) := by
  have hδne : ∀ᶠ n in atTop, δ n ≠ 0 := hδpos.mono fun n h => h.ne'
  have hdeg : ∀ n, (Qg g δ d n).natDegree ≤ d + 2 := by
    intro n
    unfold Qg
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_neg, natDegree_X_pow]; omega
    · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]; simp only [mem_Icc] at hi; omega
  have hcoeff : ∀ n m, (Qg g δ d n).coeff m =
      (-X ^ 2 : ℝ[X]).coeff m + ∑ i ∈ Icc 3 d, if m = i then g i n / δ n ^ i else 0 := by
    intro n m
    simp only [Qg, coeff_add, finsetSum_coeff, coeff_C_mul_X_pow]
  have h0 : ∀ᶠ n in atTop, (Qg g δ d n).coeff 0 = 0 := Eventually.of_forall fun n => by
    rw [hcoeff]
    simp only [coeff_neg, coeff_X_pow]
    rw [Finset.sum_eq_zero fun i hi => by simp only [mem_Icc] at hi; rw [if_neg (by omega)]]
    simp
  have hQ : CoeffTo (Qg g δ d) (-X ^ 2) := by
    intro m
    simp_rw [hcoeff]
    have : Tendsto (fun n => ∑ i ∈ Icc 3 d, if m = i then g i n / δ n ^ i else 0) atTop
        (𝓝 (∑ i ∈ Icc 3 d, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i hi => ?_
      split_ifs
      · exact (hg i hi).tendsto_div_nhds_zero
      · exact tendsto_const_nhds
    have h2 := (tendsto_const_nhds (x := (-X ^ 2 : ℝ[X]).coeff m)).add this
    simp only [sum_const_zero, add_zero] at h2
    exact h2
  have heval : ∀ j, ∀ᶠ n in atTop, (Qg g δ d n).eval (δ n * j) =
      -(δ n ^ 2 * (j : ℝ) ^ 2) + ∑ i ∈ Icc 3 d, g i n * (j : ℝ) ^ i := by
    intro j
    filter_upwards [hδne] with n hn
    simp only [Qg, eval_add, eval_neg, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    congr 1
    · ring
    · refine sum_congr rfl fun i _ => ?_
      rw [mul_pow]; field_simp
  have hφ : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) - A n * j - (Qg g δ d n).eval (δ n * j))
      =o[atTop] (fun n => δ n ^ d) := by
    intro j hj
    refine (h j hj).congr' ?_ EventuallyEq.rfl
    filter_upwards [heval j] with n hn
    rw [hn]; ring
  have hγ := tendsto_gk_of_poly (D := d + 2) hδ0 hδne hαpos (Qg g δ d) hdeg h0 hQ hφ
  exact conclusions_of_gk hδ0 hδpos (Eventually.of_forall fun n => Real.exp_pos _)
    (hαpos.mono fun n h => h.ne') hγ

/-- **GORZ Theorem 3, arXiv form (4)**: `log(α(n+j)/α(n)) = A(n) j − δ(n)² j² + o(δ(n)^d)`. -/
theorem gorz_thm3_arxiv (α A δ : ℕ → ℝ) (d : ℕ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (h : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) - (A n * j - δ n ^ 2 * (j : ℝ) ^ 2))
      =o[atTop] (fun n => δ n ^ d)) :
    (∀ i, Tendsto (fun n => (Jhat α (fun n => Real.exp (A n)) δ d n).coeff i) atTop
      (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat α (fun n => Real.exp (A n)) δ d n).eval x) (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n)) :=
  gorz_thm3 α A δ d hδ0 hδpos hαpos (fun _ _ => 0) (fun i _ => isLittleO_zero _ _)
    (fun j hj => by simpa using h j hj)

end GORZXi
