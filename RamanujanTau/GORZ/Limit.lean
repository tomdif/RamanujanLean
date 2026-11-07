/-
# GORZ for the partition function: renormalized Jensen polynomials tend to Hermite, hence are hyperbolic

Notation (all from `JensenThreshold.Tail`): `U₀ = U(n)`, `f(s) = log Mmain(n+s)` (up to a constant),
`A = f'(0)`, `δ² = −f''(0)/2`, `φ(s) = f(s) − f(0) − As`, `w_j = p(n+j) e^{−Aj}/Mmain(n)`,
`γ_k = Δ^k w(0)/δ^k` (`gamv n k`).

* `gam_close` : `|γ_k − gs(Φ)_k(0)| ≤ C₁ δ + C₂ t^{k+2}` (`t = U₀^{-1/2}`), from a Taylor expansion of `e^φ` to
  order `k+1` (`taylor_bounds`), `Δ^k[jⁱ](0) = 0` (`i < k`) and `= k!` (`i = k`), and the Rademacher error
  `|p/Mmain − 1| ≤ 2U³e^{−U/2}/(U−1)` (`rel_err`, from `Rademacher.p_sub_main_le`).
* **`tendsto_gam`** : `γ_k(n) → c_k` (Hermite moments), for every `k`. This is GORZ Theorem 3 for `p(n)`.
* **`tendsto_Gn`** : `Ĵ^{d,n}(x) := J^{d,n}(e^{−A}(δx − 1)) / (Mmain(n) δ^d) → H_d(x/2)` for every real `x`.
* **`jensen_eventually_hyperbolic`** : for every `d`, `J^{d,n}` is hyperbolic for all sufficiently large `n`.
-/
import RamanujanTau.GORZ.Bounds

set_option autoImplicit false

namespace GORZ

open Real Finset Filter Topology Polynomial JensenThreshold JensenThreshold.Tail Rademacher

/-! ## `w_j`, `ε_j` without box hypotheses -/

lemma hU_n' {n : ℕ} (hn : 1 ≤ n) (hU0 : 1 < uk 1 n) (j : ℕ) : 1 < uk 1 (n + j) := by
  rw [← Us_uk hn j hU0]; exact one_lt_Us hU0 (by positivity)

lemma wv_eq' {n : ℕ} (hn : 1 ≤ n) (hU0 : 1 < uk 1 n) (j : ℕ) :
    wv n j = Real.exp (φv (uk 1 n) 0 j) * (1 + εv n j) := by
  have hj := hU_n' hn hU0 j
  unfold wv εv φv
  simp only [if_true]
  have e1 : fch (uk 1 n) 0 (j : ℝ) = Fn (uk 1 (n + j)) := by
    simp [fch, Us_uk hn j hU0]
  have e0 : fch (uk 1 n) 0 0 = Fn (uk 1 n) := by simp [fch, Us_zero hU0]
  rw [e1, e0, Real.exp_sub, Real.exp_sub, Mmain_eq_exp hj, Mmain_eq_exp hU0]
  have hK := Kc_pos
  have : Real.exp (Av (uk 1 n) * j) = (Real.exp (-(Av (uk 1 n)) * j))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [this]
  field_simp
  ring

lemma eps_le {n : ℕ} (hn : 2 ≤ n) (hU0 : 12 ≤ uk 1 n) (j M : ℕ) :
    |εv n j| ≤ 4 * ((M + 2).factorial : ℝ) * 2 ^ (M + 2) * t0v (uk 1 n) ^ (2 * M) := by
  have hU1 : 1 < uk 1 n := by linarith
  set U := uk 1 (n + j) with hUdef
  have hUge : uk 1 n ≤ U := by
    have := U0_le_Us hU1 (show (0 : ℝ) ≤ j by positivity); rwa [Us_uk (by omega) j hU1] at this
  have h := rel_err (m := n + j) (by omega) (hU_n' (by omega) hU1 j)
  have h' : |εv n j| ≤ 2 * U ^ 3 / (U - 1) * Real.exp (-(U / 2)) := by
    simpa [εv, pc, HardyRamanujan.p] using h
  have hU : 12 ≤ U := le_trans hU0 hUge
  have he := exp_neg_le_pow (x := U / 2) (by linarith) (M + 2)
  have h1 : 2 * U ^ 3 / (U - 1) ≤ 4 * U ^ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hU0' : U ≠ 0 := by linarith
  have e : 4 * U ^ 2 * (((M + 2).factorial : ℝ) * ((U / 2) ^ (M + 2))⁻¹) =
      4 * ((M + 2).factorial : ℝ) * 2 ^ (M + 2) * (U⁻¹) ^ M := by
    have h2 : (U / 2) ^ (M + 2) = U ^ M * U ^ 2 / 2 ^ (M + 2) := by rw [div_pow, pow_add]
    rw [h2, inv_div, inv_pow]; field_simp
  have hinv : (U⁻¹) ^ M ≤ ((uk 1 n)⁻¹) ^ M :=
    pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) (inv_anti₀ (by linarith) hUge) M
  calc |εv n j| ≤ 2 * U ^ 3 / (U - 1) * Real.exp (-(U / 2)) := h'
    _ ≤ 4 * U ^ 2 * (((M + 2).factorial : ℝ) * ((U / 2) ^ (M + 2))⁻¹) :=
        mul_le_mul h1 he (Real.exp_pos _).le (by positivity)
    _ = _ := e
    _ ≤ 4 * ((M + 2).factorial : ℝ) * 2 ^ (M + 2) * ((uk 1 n)⁻¹) ^ M := by gcongr
    _ = _ := by rw [Uinv_pow hU0]

/-! ## forward differences of powers -/

lemma alt_pow_sum (k i : ℕ) : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ i =
    (fwdDiff (1 : ℝ))^[k] (fun r : ℝ => r ^ i) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun j _ => ?_
  simp [zsmul_eq_mul]

lemma alt_pow_sum_lt {k i : ℕ} (h : i < k) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ i = 0 := by
  rw [alt_pow_sum, fwdDiff_iter_pow_eq_zero_of_lt h]; rfl

lemma alt_pow_sum_self (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ k = (k.factorial : ℝ) := by
  rw [alt_pow_sum, fwdDiff_iter_eq_factorial]; simp

/-! ## the dominating chain -/

/-- constant majorants of `Φ₀, Φ₁, Φ_m` on `[0, X]`. -/
noncomputable def psi (X : ℝ) : ℕ → ℝ → ℝ := fun i _ =>
  if i = 0 then (aC / 2) ^ 2 * Bm 2 * X ^ 2 / 2 else if i = 1 then X * aC * Bm 2 else 2 ^ i * Bm i

lemma gs_congr_t (φ : ℕ → ℝ → ℝ) (t t' : ℝ) (h : ∀ i, φ i t = φ i t') : ∀ k, gs φ k t = gs φ k t' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp [gs_zero, h 0]
    · rw [gs_succ, gs_succ]
      refine sum_congr rfl fun i hi => ?_
      simp only [mem_range] at hi
      rw [ih (k - i) (by omega), h]

lemma gsΦ_bound {U0 : ℝ} (hU0 : 12 ≤ U0) (K : ℕ) {X s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) :
    |gs (Φv U0) K s| ≤ gs (psi X) K 0 := by
  rw [gs_congr_t (psi X) 0 s (fun i => rfl) K]
  apply gs_abs_le
  · simp only [psi, if_true]; exact Φ0_le hU0 hs hsX
  · intro i h1 _
    simp only [psi, show i ≠ 0 by omega, if_false]
    split_ifs with h
    · subst h; exact Φ1_bound hU0 hs hsX
    · have hb := Φ_bound_ge2 hU0 (m := i) (by omega) hs
      have hp : t0v U0 ^ (i - 2) ≤ 1 := pow_le_one₀ (t_pos hU0).le (t_le_one hU0)
      calc |Φv U0 i s| ≤ 2 ^ i * Bm i * t0v U0 ^ (i - 2) := hb
        _ ≤ 2 ^ i * Bm i * 1 := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity) (Bm_nonneg i))
        _ = _ := by ring

lemma taylor_e {U0 : ℝ} (hU0 : 12 ≤ U0) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxk : x ≤ k) :
    |Real.exp (φv U0 0 x) - ∑ i ∈ range (k + 1), gs (φv U0) i 0 * x ^ i / (i.factorial : ℝ)| ≤
      gs (psi k) (k + 1) 0 * δv U0 ^ (k + 1) * x ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  have hU1 : 1 < U0 := by linarith
  have hδ := δ_pos hU0
  have hchain : ∀ i < k + 1, ∀ t, 0 ≤ t → HasDerivAt (gs (φv U0) i) (gs (φv U0) (i + 1) t) t :=
    fun i hi t ht' => gs_hasDerivAt (φv U0) (k + 2) (fun i _ t ht => φv_chain hU1 i ht) i (by omega) t ht'
  set M := gs (psi k) (k + 1) 0 * δv U0 ^ (k + 1)
  have hb : ∀ t, 0 ≤ t → t ≤ (k : ℝ) → -M ≤ gs (φv U0) (k + 1) t ∧ gs (φv U0) (k + 1) t ≤ M := by
    intro t h1 h2
    have hg := gsΦ_bound hU0 (k + 1) h1 h2
    have e : gs (φv U0) (k + 1) t = gs (Φv U0) (k + 1) t * δv U0 ^ (k + 1) := by
      have : gs (Φv U0) (k + 1) t = gs (fun i t => φv U0 i t / δv U0 ^ i) (k + 1) t := rfl
      rw [this, gs_scale (φv U0) hδ.ne']; field_simp
    rw [e]
    have hp : 0 < δv U0 ^ (k + 1) := by positivity
    have := abs_le.mp hg
    constructor <;> nlinarith [this.1, this.2]
  have := taylor_bounds (gs (φv U0)) (k + 1) hchain hb hx hxk
  rw [gs_zero] at this
  simp only [neg_mul, neg_div] at this
  rw [abs_le]
  exact ⟨this.1, this.2⟩

/-! ## the main estimate -/

/-- `|γ_k − gs(Φ)_k(0)| ≤ C₁ δ + C₂ t^{k+2}`. -/
theorem gam_close {n : ℕ} (hn : 2 ≤ n) (hU0 : 12 ≤ uk 1 n) (k : ℕ) :
    |gamv n k - gs (Φv (uk 1 n)) k 0| ≤
      2 ^ k * gs (psi k) (k + 1) 0 * (k : ℝ) ^ (k + 1) * δv (uk 1 n) +
      2 ^ k * Real.exp (psi k 0 0) * (4 * ((2 * k + 1 + 2).factorial : ℝ) * 2 ^ (2 * k + 1 + 2)) *
        (4 / aC) ^ k * t0v (uk 1 n) ^ (k + 2) := by
  set U0 := uk 1 n with hU0def
  have hU1 : 1 < U0 := by linarith
  have hδ : 0 < δv U0 := δ_pos hU0
  have ht := t_pos hU0
  have ha := aC_pos
  set Mb := gs (psi k) (k + 1) 0
  set E := Real.exp (psi k 0 0)
  set Ce := 4 * ((2 * k + 1 + 2).factorial : ℝ) * 2 ^ (2 * k + 1 + 2)
  have hMb : 0 ≤ Mb := le_trans (abs_nonneg _) (gsΦ_bound hU0 (k + 1) (le_refl 0) (Nat.cast_nonneg k))
  have hE : 0 < E := Real.exp_pos _
  have hCe : 0 ≤ Ce := by positivity
  set P : ℕ → ℝ := fun j => ∑ i ∈ range (k + 1), gs (φv U0) i 0 * (j : ℝ) ^ i / (i.factorial : ℝ)
  set B := Mb * δv U0 ^ (k + 1) * (k : ℝ) ^ (k + 1) + E * (Ce * t0v U0 ^ (2 * (2 * k + 1)))
  have hnode : ∀ j ∈ range (k + 1), |wv n j - P j| ≤ B := by
    intro j hj
    have hjk : j ≤ k := by simp at hj; omega
    have hjR : (j : ℝ) ≤ k := by exact_mod_cast hjk
    rw [wv_eq' (by omega) hU1 j]
    have hT := taylor_e hU0 k (Nat.cast_nonneg j) hjR
    have hεj := eps_le hn hU0 j (2 * k + 1)
    have he0 : Real.exp (φv U0 0 j) ≤ E := by
      apply Real.exp_le_exp.mpr
      have := Φ0_le hU0 (X := k) (Nat.cast_nonneg j) hjR
      simpa [Φv, psi] using this
    have hpow : (j : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ (k : ℝ) ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : (j : ℝ) ^ (k + 1) ≤ (k : ℝ) ^ (k + 1) := pow_le_pow_left₀ (Nat.cast_nonneg j) hjR _
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) (k + 1)]
    have e : Real.exp (φv U0 0 j) * (1 + εv n j) - P j =
        (Real.exp (φv U0 0 j) - P j) + Real.exp (φv U0 0 j) * εv n j := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · calc |Real.exp (φv U0 0 j) - P j| ≤ Mb * δv U0 ^ (k + 1) * (j : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) := hT
        _ = Mb * δv U0 ^ (k + 1) * ((j : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by ring
        _ ≤ Mb * δv U0 ^ (k + 1) * (k : ℝ) ^ (k + 1) := by gcongr
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul he0 hεj (abs_nonneg _) hE.le
  -- the polynomial part
  have hpoly : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * P j = gs (φv U0) k 0 := by
    simp only [P, Finset.mul_sum]
    rw [Finset.sum_comm, sum_eq_single k]
    · have : ∀ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) *
          (gs (φv U0) k 0 * (j : ℝ) ^ k / (k.factorial : ℝ)) =
          gs (φv U0) k 0 / (k.factorial : ℝ) * ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ k) := by
        intro j _; ring
      rw [sum_congr rfl this, ← Finset.mul_sum, alt_pow_sum_self]
      field_simp
    · intro i hi hik
      have hik' : i < k := by simp at hi; omega
      have : ∀ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) *
          (gs (φv U0) i 0 * (j : ℝ) ^ i / (i.factorial : ℝ)) =
          gs (φv U0) i 0 / (i.factorial : ℝ) * ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ i) := by
        intro j _; ring
      rw [sum_congr rfl this, ← Finset.mul_sum, alt_pow_sum_lt hik', mul_zero]
    · intro h; simp at h
  have hΔ : |Δv n k - gs (φv U0) k 0| ≤ 2 ^ k * B := by
    unfold Δv
    rw [← hpoly, ← Finset.sum_sub_distrib]
    have hsum : ∑ j ∈ range (k + 1), (k.choose j : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
    calc |∑ j ∈ range (k + 1), ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * wv n j -
          (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * P j)|
        ≤ ∑ j ∈ range (k + 1), |(-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * wv n j -
          (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * P j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ) * B := by
          refine sum_le_sum fun j hj => ?_
          rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hnode j hj) (Nat.cast_nonneg _)
      _ = 2 ^ k * B := by rw [← Finset.sum_mul, hsum]
  -- divide by δ^k
  have hg : gs (Φv U0) k 0 = gs (φv U0) k 0 / δv U0 ^ k := by
    have : gs (Φv U0) k 0 = gs (fun i t => φv U0 i t / δv U0 ^ i) k 0 := rfl
    rw [this, gs_scale (φv U0) hδ.ne']
  have hδk : 0 < δv U0 ^ k := pow_pos hδ k
  have e : gamv n k - gs (Φv U0) k 0 = (Δv n k - gs (φv U0) k 0) / δv U0 ^ k := by
    rw [hg]; unfold gamv; ring
  rw [e, abs_div, abs_of_pos hδk, div_le_iff₀ hδk]
  have hl : (aC / 4 * t0v U0 ^ 3) ^ k ≤ δv U0 ^ k := pow_le_pow_left₀ (by positivity) (δ_lower hU0) k
  have key : t0v U0 ^ (2 * (2 * k + 1)) ≤ (4 / aC) ^ k * t0v U0 ^ (k + 2) * δv U0 ^ k := by
    have e2 : t0v U0 ^ (2 * (2 * k + 1)) = (4 / aC) ^ k * t0v U0 ^ (k + 2) * (aC / 4 * t0v U0 ^ 3) ^ k := by
      have h4 : (4 / aC) ^ k * (aC / 4) ^ k = 1 := by
        rw [← mul_pow, show 4 / aC * (aC / 4) = 1 by field_simp, one_pow]
      have h5 : t0v U0 ^ (2 * (2 * k + 1)) = t0v U0 ^ (k + 2) * (t0v U0 ^ 3) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [h5, mul_pow]; linear_combination (-(t0v U0 ^ (k + 2) * (t0v U0 ^ 3) ^ k)) * h4
    rw [e2]; gcongr
  calc |Δv n k - gs (φv U0) k 0| ≤ 2 ^ k * B := hΔ
    _ = 2 ^ k * Mb * (k : ℝ) ^ (k + 1) * δv U0 * δv U0 ^ k +
          2 ^ k * E * Ce * t0v U0 ^ (2 * (2 * k + 1)) := by simp only [B]; ring
    _ ≤ 2 ^ k * Mb * (k : ℝ) ^ (k + 1) * δv U0 * δv U0 ^ k +
          2 ^ k * E * Ce * ((4 / aC) ^ k * t0v U0 ^ (k + 2) * δv U0 ^ k) := by gcongr
    _ = _ := by ring

/-! ## limits -/

theorem tendsto_uk : Tendsto (fun n : ℕ => uk 1 n) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (2 / 3 : ℝ) * ((n : ℝ) - 1 / 24)) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have h2 := (Real.tendsto_sqrt_atTop.comp h1).const_mul_atTop Real.pi_pos
  refine h2.congr fun n => ?_
  simp [uk]

theorem tendsto_t0v : Tendsto t0v atTop (𝓝 0) := by
  have := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  exact this

lemma tendsto_t_n : Tendsto (fun n : ℕ => t0v (uk 1 n)) atTop (𝓝 0) := tendsto_t0v.comp tendsto_uk

lemma ev_U12 : ∀ᶠ n : ℕ in atTop, 12 ≤ uk 1 n := tendsto_uk.eventually_ge_atTop 12

theorem tendsto_δ : Tendsto (fun n : ℕ => δv (uk 1 n)) atTop (𝓝 0) := by
  have hC : Tendsto (fun n : ℕ => aC / 2 * (Bm 2 + 1) * t0v (uk 1 n) ^ 3) atTop (𝓝 0) := by
    have := (tendsto_t_n.pow 3).const_mul (aC / 2 * (Bm 2 + 1)); simpa using this
  refine squeeze_zero' ?_ ?_ hC
  · filter_upwards [ev_U12] with n hn using (δ_pos hn).le
  · filter_upwards [ev_U12] with n hn using δ_upper hn

theorem tendsto_gsΦ (k : ℕ) : Tendsto (fun n : ℕ => gs (Φv (uk 1 n)) k 0) atTop (𝓝 (cH k)) := by
  rw [← gs_Φinf k]
  apply gs_tendsto (fun n => Φv (uk 1 n)) Φinf 0 k
  intro i _
  rcases i with _ | _ | _ | i
  · have h : Φinf 0 0 = 0 := by simp [Φinf]
    rw [h]; exact tendsto_const_nhds.congr fun n => Φ0_zero.symm
  · have h : Φinf (0 + 1) 0 = 0 := by simp [Φinf]
    rw [h]; exact tendsto_const_nhds.congr fun n => Φ1_zero.symm
  · have h : Φinf (0 + 1 + 1) 0 = -2 := by simp [Φinf]
    rw [h]
    exact tendsto_const_nhds.congr' (by filter_upwards [ev_U12] with n hn using (Φ2_zero hn).symm)
  · simp only [Φinf, show i + 1 + 1 + 1 ≠ 2 by omega, if_false]
    have hb : Tendsto (fun n : ℕ => 2 ^ (i + 3) * Bm (i + 3) * t0v (uk 1 n) ^ (i + 1)) atTop (𝓝 0) := by
      have := (tendsto_t_n.pow (i + 1)).const_mul (2 ^ (i + 3) * Bm (i + 3)); simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ev_U12] with n hn
    rw [Real.norm_eq_abs]
    exact Φ_bound_ge2 hn (m := i + 3) (by omega) le_rfl

/-- **GORZ Theorem 3 for `p(n)`**: the normalized forward differences `γ_k(n) = Δ^k w(0)/δ^k` converge to the
Hermite moments `c_k`. (Milestone 2a.) -/
theorem tendsto_gam (k : ℕ) : Tendsto (fun n : ℕ => gamv n k) atTop (𝓝 (cH k)) := by
  have hR : Tendsto (fun n : ℕ =>
      2 ^ k * gs (psi k) (k + 1) 0 * (k : ℝ) ^ (k + 1) * δv (uk 1 n) +
      2 ^ k * Real.exp (psi k 0 0) * (4 * ((2 * k + 1 + 2).factorial : ℝ) * 2 ^ (2 * k + 1 + 2)) *
        (4 / aC) ^ k * t0v (uk 1 n) ^ (k + 2)) atTop (𝓝 0) := by
    have := (tendsto_δ.const_mul (2 ^ k * gs (psi k) (k + 1) 0 * (k : ℝ) ^ (k + 1))).add
      ((tendsto_t_n.pow (k + 2)).const_mul (2 ^ k * Real.exp (psi k 0 0) *
        (4 * ((2 * k + 1 + 2).factorial : ℝ) * 2 ^ (2 * k + 1 + 2)) * (4 / aC) ^ k))
    simpa using this
  have hdiff : Tendsto (fun n : ℕ => gamv n k - gs (Φv (uk 1 n)) k 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hR
    filter_upwards [ev_U12, eventually_ge_atTop 2] with n hn hn2
    rw [Real.norm_eq_abs]; exact gam_close hn2 hn k
  have := hdiff.add (tendsto_gsΦ k)
  simpa using this

/-! ## the renormalized Jensen polynomials -/

/-- `Ĝ_{d,n}(x) = Σ_k C(d,k) γ_k x^{d−k} (δx − 1)^k`, so that `J^{d,n}(e^{−A}(δx−1)) = Mmain(n) δ^d Ĝ(x)`. -/
noncomputable def Gn (d n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (d + 1), (d.choose k : ℝ) * gamv n k * x ^ (d - k) * (δv (uk 1 n) * x - 1) ^ k

lemma eval_jensen_eq' (d : ℕ) {n : ℕ} (hn : 2 ≤ n) (hU0 : 12 ≤ uk 1 n) (xr : ℝ) :
    (jensen d n).eval (Real.exp (-(Av (uk 1 n))) * (δv (uk 1 n) * xr - 1)) =
      Mmain n * δv (uk 1 n) ^ d * Gn d n xr := by
  have hU1 : 1 < uk 1 n := by linarith
  have hδ := δ_pos hU0
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU1]; have := Kc_pos; positivity
  rw [eval_jensen]
  have h1 : ∀ j ∈ range (d + 1), (d.choose j : ℝ) * (pc (n + j) : ℝ) *
      (Real.exp (-(Av (uk 1 n))) * (δv (uk 1 n) * xr - 1)) ^ j =
        Mmain n * ((d.choose j : ℝ) * wv n j * (δv (uk 1 n) * xr - 1) ^ j) := by
    intro j _
    unfold wv
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (j : ℝ) * -(Av (uk 1 n)) = -(Av (uk 1 n)) * j := by ring
    rw [this]; field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hN := newtonId d (wv n) (δv (uk 1 n) * xr)
  rw [hN]
  unfold Gn
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hΔ : (∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * wv n j) =
      gamv n k * δv (uk 1 n) ^ k := by
    unfold gamv Δv; field_simp
  rw [hΔ]
  have : δv (uk 1 n) ^ d = δv (uk 1 n) ^ k * δv (uk 1 n) ^ (d - k) := by rw [← pow_add]; congr 1; omega
  rw [this, mul_pow]; ring

/-- **Renormalized Jensen polynomials tend to Hermite** (GORZ Theorem 1, partition case, pointwise form):
`J^{d,n}(e^{−A}(δx−1)) / (Mmain(n) δ^d) → H_d(x/2)`. (Milestone 2b.) -/
theorem tendsto_Gn (d : ℕ) (x : ℝ) : Tendsto (fun n : ℕ => Gn d n x) atTop (𝓝 ((H d).eval x)) := by
  have hlim : Tendsto (fun n : ℕ => Gn d n x) atTop
      (𝓝 (∑ k ∈ range (d + 1), (d.choose k : ℝ) * cH k * x ^ (d - k) * (0 * x - 1) ^ k)) := by
    unfold Gn
    refine tendsto_finsetSum _ fun k _ => ?_
    exact (((tendsto_gam k).const_mul _).mul_const _).mul (((tendsto_δ.mul_const x).sub_const 1).pow k)
  convert hlim using 2
  rw [eval_H]
  refine sum_congr rfl fun k _ => ?_
  rw [zero_mul, zero_sub]
  have := neg_one_pow_mul_cH k
  calc (d.choose k : ℝ) * cH k * x ^ (d - k) = (d.choose k : ℝ) * ((-1) ^ k * cH k) * x ^ (d - k) := by
        rw [this]
    _ = _ := by ring

/-- **GORZ, partition case**: for every degree `d`, the Jensen polynomial `J^{d,n}(X) = Σ_{j≤d} C(d,j) p(n+j) X^j`
is hyperbolic for all sufficiently large `n`. (Milestone 3.) -/
theorem jensen_eventually_hyperbolic (d : ℕ) : ∀ᶠ n in atTop, Hyperbolic (jensen d n) := by
  obtain ⟨y, hy, hys⟩ := H_alternating d
  have hev : ∀ᶠ n in atTop, ∀ i ∈ range (d + 1), 0 < (-1 : ℝ) ^ (d - i) * Gn d n (y i) := by
    rw [eventually_all_finset]
    intro i hi
    exact ((tendsto_Gn d (y i)).const_mul ((-1 : ℝ) ^ (d - i))).eventually
      (lt_mem_nhds (hys i (by simp at hi; omega)))
  filter_upwards [hev, eventually_ge_atTop 2, ev_U12] with n hG hn hU
  have hδ := δ_pos hU
  have hU1 : 1 < uk 1 n := by linarith
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU1]; have := Kc_pos; positivity
  set XX : ℕ → ℝ := fun i => Real.exp (-(Av (uk 1 n))) * (δv (uk 1 n) * y i - 1)
  apply hyperbolic_of_alternating (jensen d n) d (natDegree_jensen_le d n) XX
  · intro i hi
    have := mul_lt_mul_of_pos_left (hy i hi) hδ
    exact mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos _)
  · intro i hi
    simp only [XX]
    rw [eval_jensen_eq' d hn hU, eval_jensen_eq' d hn hU]
    have g1 := hG i (by simp; omega)
    have g2 := hG (i + 1) (by simp; omega)
    have e : (-1 : ℝ) ^ (d - i) = -((-1) ^ (d - (i + 1))) := by
      rw [show d - i = (d - (i + 1)) + 1 by omega, pow_succ]; ring
    rw [e] at g1
    have h3 := neg_one_pow_sq (d - (i + 1))
    have hGG : Gn d n (y i) * Gn d n (y (i + 1)) < 0 := by nlinarith [mul_pos g1 g2]
    have hpos : 0 < (Mmain n * δv (uk 1 n) ^ d) ^ 2 := by positivity
    calc Mmain n * δv (uk 1 n) ^ d * Gn d n (y i) * (Mmain n * δv (uk 1 n) ^ d * Gn d n (y (i + 1)))
        = (Mmain n * δv (uk 1 n) ^ d) ^ 2 * (Gn d n (y i) * Gn d n (y (i + 1))) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hpos hGG

end GORZ
