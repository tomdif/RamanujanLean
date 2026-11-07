/-
# Sanity check: the abstract GORZ Theorem 3 re-derives the partition case

`partition_gorz` : the hypotheses of `gorz_thm3_diff` hold for `α(n) = p(n)` with `δ(n) = δv(U(n))` (the
partition scale of `RamanujanTau/GORZ/`), hence `Ĵ^{d,n}_p → H_d` and `J^{d,n}_p` is eventually hyperbolic —
now as an *instance* of the general theorem (normalized by `p(n)` itself rather than by `Mmain(n)`).

Inputs, all from the existing partition development (not modified): the Taylor model
`p(n+j) = Mmain(n) e^{Aj} e^{φ(j)} (1+ε_j)` (`GORZ.wv_eq'`), the chain bounds `|φ^{(m)}| ≤ δ^m 2^m B_m t^{m−2}`
(`GORZ.Φ_bound_ge2`), `φ''(0) = −2δ²` (`GORZ.Φ2_zero`), the Rademacher error `|ε_j| ≤ C_M t^{2M}`
(`GORZ.eps_le`), and `δ ≥ (a/4) t³` (`GORZ.δ_lower`).  The differences are controlled by `fd_chain_close`.
-/
import RamanujanTau.GORZXi.Diff
import RamanujanTau.GORZ.Limit

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial JensenThreshold JensenThreshold.Tail Rademacher

lemma fd_affine_add (c a : ℝ) (f g : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    GORZ.fd (fun j => c + a * j + f j + g j) k = GORZ.fd f k + GORZ.fd g k := by
  have h0 := apow_lt (show 0 < k by omega)
  have h1 := apow_lt (show 1 < k by omega)
  simp only [apow, pow_zero, mul_one, pow_one] at h0 h1
  simp only [GORZ.fd, mul_add, sum_add_distrib]
  have e0 : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * c = 0 := by
    rw [← sum_mul, h0, zero_mul]
  have e1 : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (a * j) = 0 := by
    rw [show (∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (a * j)) =
      a * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * j by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring, h1, mul_zero]
  rw [e0, e1]; ring

lemma abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x)| ≤ 2 * |x| := by
  have hx' := abs_le.mp hx
  have hy : 0 < 1 + x := by linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  have h2 := Real.one_sub_inv_le_log_of_pos hy
  rw [abs_le]
  constructor
  · have : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [this] at h2
    have h3 : -(2 * |x|) ≤ x / (1 + x) := by
      rw [le_div_iff₀ hy]
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    linarith
  · linarith [le_abs_self x, abs_nonneg x]

lemma abs_fd_le (w : ℕ → ℝ) (k : ℕ) {B : ℝ} (hB : ∀ j ≤ k, |w j| ≤ B) : |GORZ.fd w k| ≤ 2 ^ k * B := by
  unfold GORZ.fd
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (k + 1), |(-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * w j|
      ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ) * B := by
        refine sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hB j (by simp at hj; omega)) (Nat.cast_nonneg _)
    _ = 2 ^ k * B := by rw [← sum_mul, sum_choose_real]

/-- the Taylor-model splitting of `Δ^k log p(n)`. -/
lemma dlog_p_split {n : ℕ} (hn : 2 ≤ n) (hU : 12 ≤ uk 1 n) {k : ℕ} (hk : 2 ≤ k) :
    dlog (fun m => (pc m : ℝ)) n k =
      GORZ.fd (fun j => φv (uk 1 n) 0 j) k + GORZ.fd (fun j => Real.log (1 + εv n j)) k := by
  have hU1 : 1 < uk 1 n := by linarith
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU1]; have := Kc_pos; positivity
  have hrepr : ∀ j : ℕ, Real.log (pc (n + j) : ℝ) =
      Real.log (Mmain n) + Av (uk 1 n) * j + φv (uk 1 n) 0 j + Real.log (1 + εv n j) := by
    intro j
    have hw := GORZ.wv_eq' (by omega) hU1 j
    have hp : (0 : ℝ) < pc (n + j) := by exact_mod_cast pc_pos _
    have hMj : 0 < Mmain (n + j) := by
      rw [Mmain_eq_exp (GORZ.hU_n' (by omega) hU1 j)]; have := Kc_pos; positivity
    have h1e : 0 < 1 + εv n j := by unfold εv; simp only [add_sub_cancel]; positivity
    have hpw : (pc (n + j) : ℝ) = wv n j * Mmain n * Real.exp (Av (uk 1 n) * j) := by
      unfold wv
      rw [show -(Av (uk 1 n)) * (j : ℝ) = -(Av (uk 1 n) * j) by ring, Real.exp_neg]
      field_simp
    rw [hpw, hw, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hM.ne',
      Real.log_mul (Real.exp_pos _).ne' h1e.ne', Real.log_exp, Real.log_exp]
    ring
  unfold dlog
  rw [show (fun j : ℕ => Real.log (pc (n + j) : ℝ)) = fun j : ℕ => Real.log (Mmain n) + Av (uk 1 n) * j +
    φv (uk 1 n) 0 j + Real.log (1 + εv n j) from funext hrepr]
  exact fd_affine_add _ _ _ _ hk

/-- `Δ^k φ(0)/δ^k` is within `C δ` of `Φ_k(0)`. -/
lemma fd_phi_close {n : ℕ} (hU : 12 ≤ uk 1 n) {k : ℕ} (hk : 1 ≤ k) :
    |GORZ.fd (fun j => φv (uk 1 n) 0 j) k / δv (uk 1 n) ^ k - Φv (uk 1 n) k 0| ≤
      2 ^ k * (k : ℝ) ^ (k + 1) * (2 ^ (k + 1) * GORZ.Bm (k + 1)) * δv (uk 1 n) := by
  have hU1 : 1 < uk 1 n := by linarith
  have hδ := GORZ.δ_pos hU
  have ht1 := GORZ.t_le_one hU
  have ht0 := (GORZ.t_pos hU).le
  have hBm := GORZ.Bm_nonneg (k + 1)
  have hb : ∀ t : ℝ, 0 ≤ t → t ≤ (k : ℝ) → |φv (uk 1 n) (k + 1) t| ≤
      δv (uk 1 n) ^ (k + 1) * (2 ^ (k + 1) * GORZ.Bm (k + 1)) := by
    intro t ht _
    have h := GORZ.Φ_bound_ge2 hU (show 2 ≤ k + 1 by omega) ht
    unfold Φv at h
    rw [abs_div, abs_of_pos (pow_pos hδ _), div_le_iff₀ (pow_pos hδ _)] at h
    have htp : t0v (uk 1 n) ^ (k + 1 - 2) ≤ 1 := pow_le_one₀ ht0 ht1
    calc |φv (uk 1 n) (k + 1) t| ≤ 2 ^ (k + 1) * GORZ.Bm (k + 1) * t0v (uk 1 n) ^ (k + 1 - 2) *
          δv (uk 1 n) ^ (k + 1) := h
      _ ≤ 2 ^ (k + 1) * GORZ.Bm (k + 1) * 1 * δv (uk 1 n) ^ (k + 1) := by gcongr
      _ = _ := by ring
  have hc := fd_chain_close (φv (uk 1 n)) k (fun i _ t ht => φv_chain hU1 i ht) hb
  have e : GORZ.fd (fun j => φv (uk 1 n) 0 j) k / δv (uk 1 n) ^ k - Φv (uk 1 n) k 0 =
      (GORZ.fd (fun j => φv (uk 1 n) 0 j) k - φv (uk 1 n) k 0) / δv (uk 1 n) ^ k := by
    unfold Φv; field_simp
  rw [e, abs_div, abs_of_pos (pow_pos hδ k), div_le_iff₀ (pow_pos hδ k)]
  calc _ ≤ _ := hc
    _ = _ := by ring

lemma tendsto_fd_phi {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hΦ : Tendsto (fun n => Φv (uk 1 n) k 0) atTop (𝓝 L)) :
    Tendsto (fun n => GORZ.fd (fun j => φv (uk 1 n) 0 j) k / δv (uk 1 n) ^ k) atTop (𝓝 L) := by
  have hd : Tendsto (fun n => GORZ.fd (fun j => φv (uk 1 n) 0 j) k / δv (uk 1 n) ^ k -
      Φv (uk 1 n) k 0) atTop (𝓝 0) := by
    have hb := GORZ.tendsto_δ.const_mul (2 ^ k * (k : ℝ) ^ (k + 1) * (2 ^ (k + 1) * GORZ.Bm (k + 1)))
    rw [mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [GORZ.ev_U12] with n hU
    rw [Real.norm_eq_abs]; exact fd_phi_close hU hk
  simpa using hd.add hΦ

lemma tendsto_fd_eps {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n => GORZ.fd (fun j => Real.log (1 + εv n j)) k / δv (uk 1 n) ^ k) atTop (𝓝 0) := by
  set C : ℝ := 4 * ((2 * k + 2).factorial : ℝ) * 2 ^ (2 * k + 2) with hC
  have hC0 : 0 < C := by positivity
  have ha := aC_pos
  have hsmall : ∀ᶠ n in atTop, C * t0v (uk 1 n) ^ (2 * (2 * k)) ≤ 1 / 2 := by
    have h := (GORZ.tendsto_t_n.pow (2 * (2 * k))).const_mul C
    rw [zero_pow (by omega), mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hlim : Tendsto (fun n => 2 ^ k * 2 * C * (aC / 4)⁻¹ ^ k * t0v (uk 1 n) ^ k) atTop (𝓝 0) := by
    have h := (GORZ.tendsto_t_n.pow k).const_mul (2 ^ k * 2 * C * (aC / 4)⁻¹ ^ k)
    rwa [zero_pow (by omega), mul_zero] at h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [GORZ.ev_U12, eventually_ge_atTop 2, hsmall] with n hU hn hs
  have ht := GORZ.t_pos hU
  have hδ := GORZ.δ_pos hU
  have hfd : |GORZ.fd (fun j => Real.log (1 + εv n j)) k| ≤ 2 ^ k * (2 * (C * t0v (uk 1 n) ^ (2 * (2 * k)))) := by
    refine abs_fd_le _ k fun j _ => ?_
    have he := GORZ.eps_le hn hU j (2 * k)
    rw [← hC] at he
    exact (abs_log_one_add_le (he.trans hs)).trans (by linarith)
  have hδk : (aC / 4 * t0v (uk 1 n) ^ 3) ^ k ≤ δv (uk 1 n) ^ k :=
    pow_le_pow_left₀ (by positivity) (GORZ.δ_lower hU) k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hδ k), div_le_iff₀ (pow_pos hδ k)]
  calc |GORZ.fd (fun j => Real.log (1 + εv n j)) k| ≤ 2 ^ k * (2 * (C * t0v (uk 1 n) ^ (2 * (2 * k)))) := hfd
    _ = 2 ^ k * 2 * C * (aC / 4)⁻¹ ^ k * t0v (uk 1 n) ^ k * (aC / 4 * t0v (uk 1 n) ^ 3) ^ k := by
        rw [mul_pow, ← pow_mul, inv_pow]
        have : t0v (uk 1 n) ^ (2 * (2 * k)) = t0v (uk 1 n) ^ k * t0v (uk 1 n) ^ (3 * k) := by
          rw [← pow_add]; congr 1; ring
        rw [this]
        field_simp
    _ ≤ _ := by gcongr

/-- **Sanity check: GORZ for `p(n)` as an instance of the abstract Theorem 3** (difference form).
With `δ(n) = δv(U(n))` and `E(n) = p(n+1)/p(n)`: `Ĵ^{d,n}_p → H_d` coefficientwise and uniformly on compacts,
and `J^{d,n}_p` is hyperbolic for all large `n` (Chen–Jia–Wang conjecture / GORZ Theorem 5 for `1/η`). -/
theorem partition_gorz (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat (fun m => (pc m : ℝ)) (fun n => (pc (n + 1) : ℝ) / pc n)
      (fun n => δv (uk 1 n)) d n).coeff i) atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat (fun m => (pc m : ℝ)) (fun n => (pc (n + 1) : ℝ) / pc n)
        (fun n => δv (uk 1 n)) d n).eval x) (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq (fun m => (pc m : ℝ)) d n)) := by
  have hsplit : ∀ k, 2 ≤ k → ∀ᶠ n in atTop, dlog (fun m => (pc m : ℝ)) n k / δv (uk 1 n) ^ k =
      GORZ.fd (fun j => φv (uk 1 n) 0 j) k / δv (uk 1 n) ^ k +
        GORZ.fd (fun j => Real.log (1 + εv n j)) k / δv (uk 1 n) ^ k := by
    intro k hk
    filter_upwards [GORZ.ev_U12, eventually_ge_atTop 2] with n hU hn
    rw [dlog_p_split hn hU hk, add_div]
  refine gorz_thm3_diff (fun m => (pc m : ℝ)) (fun n => δv (uk 1 n)) d GORZ.tendsto_δ
    (GORZ.ev_U12.mono fun n hU => GORZ.δ_pos hU) (Eventually.of_forall fun n => by show (0 : ℝ) < (pc n : ℝ); exact_mod_cast pc_pos n)
    ?_ ?_
  · have h2 := tendsto_fd_phi (k := 2) (by norm_num) (L := -2)
      (tendsto_const_nhds.congr' (GORZ.ev_U12.mono fun n hU => (GORZ.Φ2_zero hU).symm))
    have := h2.add (tendsto_fd_eps (k := 2) (by norm_num))
    rw [add_zero] at this
    exact this.congr' ((hsplit 2 le_rfl).mono fun n hn => hn.symm)
  · intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    have hΦ : Tendsto (fun n => Φv (uk 1 n) k 0) atTop (𝓝 0) := by
      have hb := (GORZ.tendsto_t_n.pow (k - 2)).const_mul (2 ^ k * GORZ.Bm k)
      rw [zero_pow (by omega), mul_zero] at hb
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [GORZ.ev_U12] with n hU
      rw [Real.norm_eq_abs]; exact GORZ.Φ_bound_ge2 hU (by omega) le_rfl
    have := (tendsto_fd_phi (by omega) hΦ).add (tendsto_fd_eps (k := k) (by omega))
    rw [add_zero] at this
    exact this.congr' ((hsplit k (by omega)).mono fun n hn => hn.symm)

end GORZXi
