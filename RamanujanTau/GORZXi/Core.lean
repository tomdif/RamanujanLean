/-
# GORZ for a general sequence: the Hermite limit from the limits of normalized forward differences

For an arbitrary real sequence `α`, and real sequences `E` (the exponential scale, `E = e^{A}` in GORZ) and
`δ`, set

* `J^{d,n}_α(X) = Σ_{j≤d} C(d,j) α(n+j) X^j`  (`jensenSeq α d n`, GORZ eq. (2));
* `Ĵ^{d,n}(X) = δ(n)^{-d}/α(n) · J^{d,n}_α((δ(n)X − 1)/E(n))`  (`Jhat α E δ d n`, GORZ eq. (5));
* `w_n(j) = α(n+j)/α(n) · E(n)^{-j}`  (`wr`), and `γ_k(n) = Δ^k w_n(0) / δ(n)^k`  (`gk`).

By the Newton identity (all degrees, `GORZ.newtonId`), `Ĵ^{d,n}(x) = Σ_k C(d,k) γ_k(n) x^{d−k} (δx − 1)^k`.
Hence (**`tendsto_coeff_Jhat_of_gk`**): if `δ → 0` and `γ_k(n) → ℓ_k` for all `k ≤ d`, then the
coefficients of `Ĵ^{d,n}` converge to those of `Hgen ℓ d = Σ_k C(d,k) (−1)^k ℓ_k X^{d−k}`, and
(**`tendstoUniformlyOn_Jhat_of_gk`**) `Ĵ^{d,n} → Hgen ℓ d` uniformly on every compact set.  For `ℓ = cH`
(the derivatives of `e^{−y²}` at `0`) `Hgen cH d = GORZ.H d`, GORZ's `H_d` (eq. (3)), and
(**`eventually_hyperbolic_of_gk`**) `J^{d,n}_α` is hyperbolic for all large `n`.

This is the sequence-independent part of the partition proof in `RamanujanTau/GORZ/`, abstracted.
-/
import RamanujanTau.GORZ.Coeff

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial JensenThreshold

/-- the Jensen polynomial `J^{d,n}_α(X) = Σ_{j≤d} C(d,j) α(n+j) X^j` of an arbitrary real sequence. -/
noncomputable def jensenSeq (α : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j

lemma eval_jensenSeq (α : ℕ → ℝ) (d n : ℕ) (x : ℝ) :
    (jensenSeq α d n).eval x = ∑ j ∈ range (d + 1), (d.choose j : ℝ) * α (n + j) * x ^ j := by
  simp [jensenSeq, eval_finsetSum]

lemma natDegree_jensenSeq_le (α : ℕ → ℝ) (d n : ℕ) : (jensenSeq α d n).natDegree ≤ d := by
  unfold jensenSeq
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]; simpa [Nat.lt_succ_iff] using hj

/-- GORZ's renormalized Jensen polynomial `δ^{-d}/α(n) · J^{d,n}_α((δX − 1)/E)` (eq. (5); `E = exp(A(n))`). -/
noncomputable def Jhat (α E δ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  C ((δ n ^ d * α n)⁻¹) * (jensenSeq α d n).comp (C (E n)⁻¹ * (C (δ n) * X - 1))

/-- the normalized ratios `w_n(j) = α(n+j)/α(n) · E(n)^{-j}`. -/
noncomputable def wr (α E : ℕ → ℝ) (n j : ℕ) : ℝ := α (n + j) / α n * (E n ^ j)⁻¹

/-- `γ_k(n) = Δ^k w_n(0) / δ(n)^k`. -/
noncomputable def gk (α E δ : ℕ → ℝ) (n k : ℕ) : ℝ := GORZ.fd (wr α E n) k / δ n ^ k

/-- the Newton form `Σ_k C(d,k) γ_k X^{d−k} (δX − 1)^k`. -/
noncomputable def Gpoly (α E δ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d + 1), C ((d.choose k : ℝ) * gk α E δ n k) * (X ^ (d - k) * (C (δ n) * X - 1) ^ k)

/-- the limit polynomial `Σ_{k≤d} C(d,k) (−1)^k ℓ_k X^{d−k}`. -/
noncomputable def Hgen (ℓ : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d + 1), C ((d.choose k : ℝ) * ((-1) ^ k * ℓ k)) * X ^ (d - k)

lemma Hgen_cH (d : ℕ) : Hgen GORZ.cH d = GORZ.H d := by
  unfold Hgen GORZ.H
  refine sum_congr rfl fun k _ => ?_
  rw [GORZ.neg_one_pow_mul_cH]

lemma eval_Jhat (α E δ : ℕ → ℝ) (d n : ℕ) (x : ℝ) :
    (Jhat α E δ d n).eval x =
      (δ n ^ d)⁻¹ * ∑ j ∈ range (d + 1), (d.choose j : ℝ) * wr α E n j * (δ n * x - 1) ^ j := by
  simp only [Jhat, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one, eval_jensenSeq, wr]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_pow, inv_pow, mul_inv]
  ring

lemma Jhat_eval_eq (α E δ : ℕ → ℝ) (d n : ℕ) (hδ : δ n ≠ 0) (x : ℝ) :
    (Jhat α E δ d n).eval x = (Gpoly α E δ d n).eval x := by
  rw [eval_Jhat]
  have hN := GORZ.newtonId d (wr α E n) (δ n * x)
  rw [hN]
  simp only [Gpoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, gk,
    GORZ.fd]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have e : δ n ^ d = δ n ^ k * δ n ^ (d - k) := by rw [← pow_add]; congr 1; omega
  rw [e, mul_pow]
  field_simp

theorem Jhat_eq_Gpoly (α E δ : ℕ → ℝ) (d n : ℕ) (hδ : δ n ≠ 0) : Jhat α E δ d n = Gpoly α E δ d n :=
  Polynomial.funext fun x => Jhat_eval_eq α E δ d n hδ x

lemma coeff_Gpoly (α E δ : ℕ → ℝ) (d n i : ℕ) : (Gpoly α E δ d n).coeff i =
    ∑ k ∈ range (d + 1), (d.choose k : ℝ) * gk α E δ n k *
      (if d - k ≤ i then (k.choose (i - (d - k)) : ℝ) * δ n ^ (i - (d - k)) * (-1) ^ (k - (i - (d - k)))
        else 0) := by
  rw [Gpoly, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, coeff_X_pow_mul']
  congr 1
  split_ifs
  · rw [GORZ.coeff_lin_pow]
  · rfl

lemma coeff_Hgen (ℓ : ℕ → ℝ) (d i : ℕ) : (Hgen ℓ d).coeff i =
    ∑ k ∈ range (d + 1), if i = d - k then (d.choose k : ℝ) * ((-1) ^ k * ℓ k) else 0 := by
  rw [Hgen, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul_X_pow]

variable {α E δ : ℕ → ℝ} {d : ℕ} {ℓ : ℕ → ℝ}

/-- **Coefficientwise Hermite limit** from `γ_k(n) → ℓ_k` (`k ≤ d`) and `δ → 0`. -/
theorem tendsto_coeff_Jhat_of_gk (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hγ : ∀ k ≤ d, Tendsto (fun n => gk α E δ n k) atTop (𝓝 (ℓ k))) (i : ℕ) :
    Tendsto (fun n => (Jhat α E δ d n).coeff i) atTop (𝓝 ((Hgen ℓ d).coeff i)) := by
  have hev : ∀ᶠ n : ℕ in atTop, (Gpoly α E δ d n).coeff i = (Jhat α E δ d n).coeff i := by
    filter_upwards [hδne] with n hn
    rw [Jhat_eq_Gpoly α E δ d n hn]
  refine Tendsto.congr' hev ?_
  simp only [coeff_Gpoly, coeff_Hgen]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hlim := (hγ k hk').const_mul (d.choose k : ℝ)
  split_ifs with h1 h2 h2
  · have hm : i - (d - k) = 0 := by omega
    simp only [hm, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    exact (hlim.mul_const ((-1 : ℝ) ^ k)).congr' (Eventually.of_forall fun n => by ring) |>.trans
      (by rw [show (d.choose k : ℝ) * ℓ k * (-1) ^ k = (d.choose k : ℝ) * ((-1) ^ k * ℓ k) by ring])
  · have hm : 0 < i - (d - k) := by omega
    have hδm := (hδ0.pow (i - (d - k))).const_mul ((k.choose (i - (d - k)) : ℝ))
    have := (hlim.mul (hδm.mul_const ((-1 : ℝ) ^ (k - (i - (d - k))))))
    rw [zero_pow hm.ne', mul_zero, zero_mul, mul_zero] at this
    exact this
  · omega
  · exact tendsto_const_nhds.congr fun n => by simp

lemma natDegree_Jhat_le (n : ℕ) : (Jhat α E δ d n).natDegree ≤ d := by
  unfold Jhat
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  have h1 : (C (E n)⁻¹ * (C (δ n) * X - 1)).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans ?_
    simp only [natDegree_one, max_le_iff, zero_le, and_true]
    exact (natDegree_C_mul_le _ _).trans (by simp)
  calc (jensenSeq α d n).natDegree * (C (E n)⁻¹ * (C (δ n) * X - 1)).natDegree ≤ d * 1 :=
        Nat.mul_le_mul (natDegree_jensenSeq_le α d n) h1
    _ = d := mul_one d

lemma natDegree_Hgen_le : (Hgen ℓ d).natDegree ≤ d := by
  unfold Hgen
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]; omega

/-- polynomials of degree `≤ d` whose coefficients converge, converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_of_coeff {P : ℕ → ℝ[X]} {Q : ℝ[X]} (hP : ∀ n, (P n).natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) (hc : ∀ i, Tendsto (fun n => (P n).coeff i) atTop (𝓝 (Q.coeff i)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => (P n).eval x) (fun x => Q.eval x) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsum : Tendsto (fun n => ∑ i ∈ range (d + 1), |(P n).coeff i - Q.coeff i| * |R| ^ i) atTop
      (𝓝 (∑ i ∈ range (d + 1), |Q.coeff i - Q.coeff i| * |R| ^ i)) :=
    tendsto_finsetSum _ fun i _ => (((hc i).sub_const _).abs).mul_const _
  simp only [sub_self, abs_zero, zero_mul, sum_const_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hε)] with n hn x hx
  have hxR : |x| ≤ |R| := by
    have := hR hx; rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self R)
  rw [Real.dist_eq, eval_eq_sum_range' (Nat.lt_succ_of_le hQ), eval_eq_sum_range' (Nat.lt_succ_of_le (hP n)),
    ← sum_sub_distrib]
  refine lt_of_le_of_lt ((abs_sum_le_sum_abs _ _).trans ?_) hn
  refine sum_le_sum fun i _ => ?_
  rw [← sub_mul, abs_mul, abs_sub_comm, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxR i) (abs_nonneg _)

/-- **Uniform Hermite limit on compact sets** (GORZ eq. (5)). -/
theorem tendstoUniformlyOn_Jhat_of_gk (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hγ : ∀ k ≤ d, Tendsto (fun n => gk α E δ n k) atTop (𝓝 (ℓ k))) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => (Jhat α E δ d n).eval x) (fun x => (Hgen ℓ d).eval x) atTop K :=
  tendstoUniformlyOn_of_coeff natDegree_Jhat_le natDegree_Hgen_le
    (tendsto_coeff_Jhat_of_gk hδ0 hδne hγ) hK

theorem tendsto_eval_Jhat_of_gk (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hγ : ∀ k ≤ d, Tendsto (fun n => gk α E δ n k) atTop (𝓝 (ℓ k))) (x : ℝ) :
    Tendsto (fun n => (Jhat α E δ d n).eval x) atTop (𝓝 ((Hgen ℓ d).eval x)) := by
  have h := (tendstoUniformlyOn_Jhat_of_gk hδ0 hδne hγ (isCompact_singleton (x := x))).tendsto_at
    (Set.mem_singleton x)
  exact h

/-- **Eventual hyperbolicity** (GORZ, Corollary to Theorem 3): if `α(n) ≠ 0`, `E(n) > 0`, `δ(n) > 0`
eventually, `δ → 0`, and `γ_k(n) → c_k` (Hermite moments) for `k ≤ d`, then `J^{d,n}_α` is hyperbolic for
all sufficiently large `n`. -/
theorem eventually_hyperbolic_of_gk (hδ0 : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hEpos : ∀ᶠ n in atTop, 0 < E n) (hα : ∀ᶠ n in atTop, α n ≠ 0)
    (hγ : ∀ k ≤ d, Tendsto (fun n => gk α E δ n k) atTop (𝓝 (GORZ.cH k))) :
    ∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n) := by
  obtain ⟨y, hy, hys⟩ := GORZ.H_alternating d
  have hδne : ∀ᶠ n in atTop, δ n ≠ 0 := hδpos.mono fun n h => h.ne'
  have hev : ∀ᶠ n in atTop, ∀ i ∈ range (d + 1), 0 < (-1 : ℝ) ^ (d - i) * (Jhat α E δ d n).eval (y i) := by
    rw [eventually_all_finset]
    intro i hi
    have ht := tendsto_eval_Jhat_of_gk hδ0 hδne hγ (y i)
    rw [Hgen_cH] at ht
    exact (ht.const_mul ((-1 : ℝ) ^ (d - i))).eventually (lt_mem_nhds (hys i (by simp at hi; omega)))
  filter_upwards [hev, hδpos, hEpos, hα] with n hG hδn hEn hαn
  set XX : ℕ → ℝ := fun i => (E n)⁻¹ * (δ n * y i - 1)
  have hJ : ∀ i, (jensenSeq α d n).eval (XX i) = (δ n ^ d * α n) * (Jhat α E δ d n).eval (y i) := by
    intro i
    simp only [Jhat, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one, XX]
    have : δ n ^ d * α n ≠ 0 := mul_ne_zero (pow_ne_zero _ hδn.ne') hαn
    field_simp
  apply hyperbolic_of_alternating (jensenSeq α d n) d (natDegree_jensenSeq_le α d n) XX
  · intro i hi
    have := mul_lt_mul_of_pos_left (hy i hi) hδn
    exact mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hEn)
  · intro i hi
    rw [hJ, hJ]
    have g1 := hG i (by simp; omega)
    have g2 := hG (i + 1) (by simp; omega)
    have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - (i + 1))) := by
      rw [show d - i = (d - (i + 1)) + 1 by omega, pow_succ]; ring
    rw [e] at g1
    have h3 := GORZ.neg_one_pow_sq (d - (i + 1))
    have hGG : (Jhat α E δ d n).eval (y i) * (Jhat α E δ d n).eval (y (i + 1)) < 0 := by
      nlinarith [mul_pos g1 g2]
    have hpos : 0 < (δ n ^ d * α n) ^ 2 := by
      have : δ n ^ d * α n ≠ 0 := mul_ne_zero (pow_ne_zero _ hδn.ne') hαn
      positivity
    calc δ n ^ d * α n * (Jhat α E δ d n).eval (y i) * (δ n ^ d * α n * (Jhat α E δ d n).eval (y (i + 1)))
        = (δ n ^ d * α n) ^ 2 * ((Jhat α E δ d n).eval (y i) * (Jhat α E δ d n).eval (y (i + 1))) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hpos hGG

end GORZXi
