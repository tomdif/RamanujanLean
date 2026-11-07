/-
# GORZ Theorem 1 for the Riemann Ξ-function, conditional on one named kernel hypothesis

Riemann's formula (GORZ §4, eqs. (11)–(13)): with `θ₀(t) = Σ_{k≥1} e^{−πk²t} = (θ(t) − 1)/2`
(`θ = HurwitzZeta.evenKernel 0`, Mathlib's Jacobi theta function `Σ_{n∈ℤ} e^{−πn²t}`) and

  `F(m) = ∫_1^∞ (log t)^m t^{−3/4} θ₀(t) dt`,   `B(n) = 32·C(2n,2)·F(2n−2) − F(2n)`,

the Taylor coefficients `γ(n)` of `(−1 + 4z²) Λ(1/2 + z) = Σ γ(n) z^{2n}/n!` are

  `γ(n) = n!/(2n)! · 2^{1−2n} · B(n)`   (`n ≥ 1`)                                         (GORZ (13)).

Here `γ` is *defined* by the right-hand side (`gammaXi`); the identification with the Taylor coefficients
of Mathlib's `completedRiemannZeta` is milestone M2 (see `docs/GORZ_XI.md`; checked numerically for
`n ≤ 4`, and against GORZ's table at `n = 10, 100`).

**Named hypothesis** `XiKernelHyp`: `B(n) > 0` eventually, and for every `k ≥ 2`,
`n^{k/2} · Δ^k[log B](n) → 0`.  (True numerically; e.g. `n·Δ²log B(n) = 0.58, 0.53, 0.48` at
`n = 25, 50, 100`, decaying like `1/log n`; the higher ones decay like `n^{1−k/2}`.  It follows from the
saddle-point analysis of GORZ Theorem 7.)

**`xi_gorz`** : under `XiKernelHyp`, for every `d`, with `δ(n) = (2n)^{−1/2}` and `E(n) = γ(n+1)/γ(n)`,
`Ĵ^{d,n}_γ → H_d` coefficientwise and uniformly on compacts, and `J^{d,n}_γ` is hyperbolic for all large `n`
(GORZ Theorem 1).  The factorial factor `n!/(2n)! 2^{1−2n}` is handled unconditionally
(`dlog_a_two`, `dlog_a_bound`).
-/
import RamanujanTau.GORZXi.Diff

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial Asymptotics JensenThreshold

/-! ## forward-difference algebra -/

lemma fd_add (f g : ℕ → ℝ) (k : ℕ) : GORZ.fd (fun j => f j + g j) k = GORZ.fd f k + GORZ.fd g k := by
  simp only [GORZ.fd, mul_add, sum_add_distrib]

lemma fd_neg (f : ℕ → ℝ) (k : ℕ) : GORZ.fd (fun j => -f j) k = -GORZ.fd f k := by
  simp only [GORZ.fd, mul_neg, sum_neg_distrib]

lemma fd_const (c : ℝ) {k : ℕ} (hk : 0 < k) : GORZ.fd (fun _ => c) k = 0 := by
  have h := apow_lt hk
  simp only [apow, pow_zero, mul_one] at h
  simp only [GORZ.fd, ← Finset.sum_mul, h, zero_mul]

lemma fd_succ (w : ℕ → ℝ) (k : ℕ) : GORZ.fd w (k + 1) = GORZ.fd (fun j => w (j + 1) - w j) k := by
  rw [← GORZ.fwdDiff_eq_fd, ← GORZ.fwdDiff_eq_fd, Function.iterate_succ_apply]
  rfl

/-! ## the factorial factor `a(n) = n!/(2n)! · 2^{1−2n}` -/

noncomputable def aXi (n : ℕ) : ℝ := (n.factorial : ℝ) / ((2 * n).factorial : ℝ) * 2 / 4 ^ n

lemma aXi_pos (n : ℕ) : 0 < aXi n := by unfold aXi; positivity

lemma aXi_succ (n : ℕ) : aXi (n + 1) = aXi n / (8 * (2 * n + 1)) := by
  unfold aXi
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n),
    Nat.factorial_succ n, pow_succ]
  push_cast
  field_simp
  ring

lemma dlog_aXi_succ (n k : ℕ) (hk : 0 < k) :
    dlog aXi n (k + 1) = -GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) k := by
  unfold dlog
  rw [fd_succ]
  have e : (fun j => Real.log (aXi (n + (j + 1))) - Real.log (aXi (n + j))) =
      fun j => -(Real.log 8 + Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) := by
    funext j
    rw [show n + (j + 1) = (n + j) + 1 by ring, aXi_succ, Real.log_div (aXi_pos _).ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    push_cast; ring
  rw [e, fd_neg, fd_add, fd_const _ hk, zero_add]

/-! ## the derivative chain of `u(x) = log(2x+1)` -/

/-- `G 0 t = log(2(x₀+t)+1)`, `G (i+1) t = (−1)^i i! 2^{i+1} (2(x₀+t)+1)^{−(i+1)}`. -/
noncomputable def uch (x0 : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => Real.log (2 * (x0 + t) + 1)
  | i + 1 => fun t => (-1) ^ i * (i.factorial : ℝ) * 2 ^ (i + 1) * ((2 * (x0 + t) + 1) ^ (i + 1))⁻¹

lemma uch_chain {x0 : ℝ} (hx0 : 0 ≤ x0) (i : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (uch x0 i) (uch x0 (i + 1) t) t := by
  have hpos : 0 < 2 * (x0 + t) + 1 := by linarith
  have hlin : HasDerivAt (fun t => 2 * (x0 + t) + 1) 2 t := by
    have := ((hasDerivAt_id t).const_add x0).const_mul 2 |>.add_const 1
    simpa using this
  cases i with
  | zero =>
    have := hlin.log hpos.ne'
    simp only [uch]
    convert this using 1
    simp; field_simp
  | succ i =>
    have hp := (hlin.pow (i + 1)).inv (pow_ne_zero _ hpos.ne')
    have := hp.const_mul ((-1 : ℝ) ^ i * (i.factorial : ℝ) * 2 ^ (i + 1))
    convert this using 1
    simp only [uch, Pi.pow_apply, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma uch_zero (x0 t : ℝ) : uch x0 0 t = Real.log (2 * (x0 + t) + 1) := rfl

lemma abs_uch_succ_le {x0 : ℝ} (hx0 : 0 ≤ x0) (i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |uch x0 (i + 1) t| ≤ (i.factorial : ℝ) * 2 ^ (i + 1) * ((2 * x0 + 1) ^ (i + 1))⁻¹ := by
  simp only [uch]
  have hpos : 0 < 2 * x0 + 1 := by linarith
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    abs_pow, abs_two, abs_inv, abs_pow, abs_of_pos (by linarith : 0 < 2 * (x0 + t) + 1)]
  gcongr
  linarith

/-- `|Δ^K u(n)| ≤ C_K/(2n+1)^K` for `K ≥ 1`. -/
lemma fd_u_bound (K : ℕ) (hK : 0 < K) : ∃ C : ℝ, ∀ n : ℕ,
    |GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) K| ≤ C * ((2 * (n : ℝ) + 1) ^ K)⁻¹ := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  refine ⟨(K'.factorial : ℝ) * 2 ^ (K' + 1) + 2 ^ (K' + 1) * ((K' + 1 : ℕ) : ℝ) ^ (K' + 1 + 1) *
    ((K' + 1).factorial * 2 ^ (K' + 1 + 1)), fun n => ?_⟩
  have hx0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 < 2 * (n : ℝ) + 1 := by linarith
  have hc := fd_chain_close (uch n) (K' + 1) (fun i _ t ht => uch_chain hx0 i t ht)
    (B := ((K' + 1).factorial : ℝ) * 2 ^ (K' + 1 + 1) * ((2 * (n : ℝ) + 1) ^ (K' + 1 + 1))⁻¹)
    (fun t ht _ => abs_uch_succ_le hx0 (K' + 1) ht)
  have he : (fun j : ℕ => uch n 0 j) = fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1) := by
    funext j; simp [uch_zero]
  rw [he] at hc
  have h0 := abs_uch_succ_le hx0 K' (le_refl (0 : ℝ))
  have hinv : ((2 * (n : ℝ) + 1) ^ (K' + 1 + 1))⁻¹ ≤ ((2 * (n : ℝ) + 1) ^ (K' + 1))⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hu0 : uch (n : ℝ) (K' + 1) 0 = uch (n : ℝ) (K' + 1) 0 := rfl
  calc |GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) (K' + 1)|
      ≤ |uch (n : ℝ) (K' + 1) 0| + |GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) (K' + 1) -
          uch (n : ℝ) (K' + 1) 0| := by
        have := abs_add_le (uch (n : ℝ) (K' + 1) 0)
          (GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) (K' + 1) - uch (n : ℝ) (K' + 1) 0)
        simpa using this
    _ ≤ (K'.factorial : ℝ) * 2 ^ (K' + 1) * ((2 * (n : ℝ) + 1) ^ (K' + 1))⁻¹ +
        2 ^ (K' + 1) * ((K' + 1 : ℕ) : ℝ) ^ (K' + 1 + 1) *
          (((K' + 1).factorial : ℝ) * 2 ^ (K' + 1 + 1) * ((2 * (n : ℝ) + 1) ^ (K' + 1 + 1))⁻¹) :=
        add_le_add h0 hc
    _ ≤ (K'.factorial : ℝ) * 2 ^ (K' + 1) * ((2 * (n : ℝ) + 1) ^ (K' + 1))⁻¹ +
        2 ^ (K' + 1) * ((K' + 1 : ℕ) : ℝ) ^ (K' + 1 + 1) *
          (((K' + 1).factorial : ℝ) * 2 ^ (K' + 1 + 1) * ((2 * (n : ℝ) + 1) ^ (K' + 1))⁻¹) := by
        gcongr
    _ = _ := by ring

/-- `Δu(n) = log((2n+3)/(2n+1))`, and `2n·Δu(n) → 2`. -/
lemma tendsto_two_n_fd_u :
    Tendsto (fun n : ℕ => 2 * (n : ℝ) * GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) 1)
      atTop (𝓝 2) := by
  -- `|Δu(n) − 2/(2n+1)| ≤ 2 · 1 · 4/(2n+1)²`
  have hc : ∀ n : ℕ, |GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) 1 - 2 / (2 * (n : ℝ) + 1)| ≤
      8 * ((2 * (n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n
    have hx0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := fd_chain_close (uch n) 1 (fun i _ t ht => uch_chain hx0 i t ht)
      (B := (1 : ℝ) * 2 ^ 2 * ((2 * (n : ℝ) + 1) ^ 2)⁻¹)
      (fun t ht _ => by simpa using abs_uch_succ_le hx0 1 ht)
    have he : (fun j : ℕ => uch n 0 j) = fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1) := by
      funext j; simp [uch_zero]
    rw [he] at h
    have hu : uch (n : ℝ) 1 0 = 2 / (2 * (n : ℝ) + 1) := by simp [uch]; ring
    rw [hu] at h
    calc _ ≤ _ := h
      _ = 8 * ((2 * (n : ℝ) + 1) ^ 2)⁻¹ := by ring
  have hmain : Tendsto (fun n : ℕ => 2 * (n : ℝ) * (2 / (2 * (n : ℝ) + 1))) atTop (𝓝 2) := by
    have : Tendsto (fun n : ℕ => 2 - 2 / (2 * (n : ℝ) + 1)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp; ring
  have herr : Tendsto (fun n : ℕ => 2 * (n : ℝ) *
      (GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) 1 - 2 / (2 * (n : ℝ) + 1))) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => 2 * (n : ℝ) * (8 * ((2 * (n : ℝ) + 1) ^ 2)⁻¹)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
      have h2 := (h1.inv_tendsto_atTop).const_mul 8
      rw [mul_zero] at h2
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
      have hp : (0 : ℝ) < 2 * n + 1 := by positivity
      rw [show 2 * (n : ℝ) * (8 * ((2 * (n : ℝ) + 1) ^ 2)⁻¹) =
          8 * (2 * (n : ℝ) + 1)⁻¹ * (2 * (n : ℝ) / (2 * (n : ℝ) + 1)) by field_simp]
      have : 2 * (n : ℝ) / (2 * (n : ℝ) + 1) ≤ 1 := by rw [div_le_one hp]; linarith
      calc 8 * (2 * (n : ℝ) + 1)⁻¹ * (2 * (n : ℝ) / (2 * (n : ℝ) + 1)) ≤ 8 * (2 * (n : ℝ) + 1)⁻¹ * 1 := by
            gcongr
        _ = _ := by simp
    refine squeeze_zero_norm (fun n => ?_) hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hc n) (by positivity)
  have := hmain.add herr
  rw [add_zero] at this
  exact this.congr fun n => by ring

/-! ## the Ξ data -/

/-- `θ₀(t) = (θ(t) − 1)/2 = Σ_{k≥1} e^{−πk²t}`, with `θ = HurwitzZeta.evenKernel 0`. -/
noncomputable def theta0 (t : ℝ) : ℝ := (HurwitzZeta.evenKernel 0 t - 1) / 2

/-- `F(m) = ∫_1^∞ (log t)^m t^{−3/4} θ₀(t) dt` (GORZ (12)). -/
noncomputable def FXi (m : ℕ) : ℝ := ∫ t in Set.Ioi (1 : ℝ), Real.log t ^ m * t ^ (-(3 / 4 : ℝ)) * theta0 t

/-- `B(n) = 32 C(2n,2) F(2n−2) − F(2n)`. -/
noncomputable def BXi (n : ℕ) : ℝ := 32 * ((2 * n).choose 2 : ℝ) * FXi (2 * n - 2) - FXi (2 * n)

/-- GORZ (13): `γ(n) = n!/(2n)! · 2^{1−2n} · B(n)`. -/
noncomputable def gammaXi (n : ℕ) : ℝ := aXi n * BXi n

/-- **The named kernel hypothesis** (the saddle-point input of GORZ Theorem 7, in difference form). -/
def XiKernelHyp : Prop :=
  (∀ᶠ n in atTop, 0 < BXi n) ∧
    ∀ k, 2 ≤ k → Tendsto (fun n : ℕ => Real.sqrt n ^ k * dlog BXi n k) atTop (𝓝 0)

/-- the GORZ scale `δ(n) = (2n)^{−1/2}`. -/
noncomputable def δXi (n : ℕ) : ℝ := (Real.sqrt (2 * n))⁻¹

lemma δXi_pow (n k : ℕ) : δXi n ^ k = ((Real.sqrt 2 ^ k) * Real.sqrt n ^ k)⁻¹ := by
  rw [δXi, inv_pow, Real.sqrt_mul (by norm_num), mul_pow]

/-- **GORZ Theorem 1 for Ξ (conditional on `XiKernelHyp`).** -/
theorem xi_gorz (hyp : XiKernelHyp) (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat gammaXi (fun n => gammaXi (n + 1) / gammaXi n) δXi d n).coeff i) atTop
      (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat gammaXi (fun n => gammaXi (n + 1) / gammaXi n) δXi d n).eval x)
      (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq gammaXi d n)) := by
  obtain ⟨hBpos, hB⟩ := hyp
  have hδ0 : Tendsto δXi atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Real.sqrt (2 * n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    exact this.inv_tendsto_atTop
  have hδpos : ∀ᶠ n in atTop, 0 < δXi n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < 2 * n := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
    exact inv_pos.mpr (Real.sqrt_pos.mpr this)
  have hαpos : ∀ᶠ n in atTop, 0 < gammaXi n := hBpos.mono fun n h => mul_pos (aXi_pos n) h
  -- `dlog γ = dlog a + dlog B`
  have hsplit : ∀ k, ∀ᶠ n in atTop, dlog gammaXi n k = dlog aXi n k + dlog BXi n k := by
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.mp hBpos
    filter_upwards [eventually_ge_atTop N] with n hn
    unfold dlog
    rw [← fd_add]
    congr 1
    funext j
    rw [gammaXi, Real.log_mul (aXi_pos _).ne' (hN (n + j) (by omega)).ne']
  have hratio : ∀ k, ∀ᶠ n in atTop, dlog gammaXi n k / δXi n ^ k =
      Real.sqrt 2 ^ k * (Real.sqrt n ^ k * dlog aXi n k) + Real.sqrt 2 ^ k * (Real.sqrt n ^ k * dlog BXi n k) := by
    intro k
    filter_upwards [hsplit k] with n hn
    rw [hn, δXi_pow, div_inv_eq_mul]; ring
  -- the `B` part
  have hBk : ∀ k, 2 ≤ k → Tendsto (fun n : ℕ => Real.sqrt 2 ^ k * (Real.sqrt n ^ k * dlog BXi n k)) atTop (𝓝 0) :=
    fun k hk => by simpa using (hB k hk).const_mul (Real.sqrt 2 ^ k)
  -- the `a` part, `k = 2`
  have ha2 : Tendsto (fun n : ℕ => Real.sqrt 2 ^ 2 * (Real.sqrt n ^ 2 * dlog aXi n 2)) atTop (𝓝 (-2)) := by
    have h := tendsto_two_n_fd_u.neg
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    rw [dlog_aXi_succ n 1 one_pos, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  -- the `a` part, `k ≥ 3`
  have hak : ∀ k, 3 ≤ k → Tendsto (fun n : ℕ => Real.sqrt 2 ^ k * (Real.sqrt n ^ k * dlog aXi n k)) atTop (𝓝 0) := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨C, hC⟩ := fd_u_bound k' (by omega)
    -- `|√n^{k'+1} Δ^{k'} u(n)| ≤ C √n^{k'+1}/(2n+1)^{k'} ≤ C (2n+1)^{(k'+1)/2 − k'}`
    have hbound : ∀ n : ℕ, |Real.sqrt n ^ (k' + 1) * dlog aXi n (k' + 1)| ≤ C * (Real.sqrt (2 * n + 1))⁻¹ := by
      intro n
      rw [dlog_aXi_succ n k' (by omega), abs_mul, abs_neg, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hp : (0 : ℝ) < 2 * n + 1 := by positivity
      have hs : Real.sqrt n ≤ Real.sqrt (2 * n + 1) := Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have hC0 : 0 ≤ C := by
        have := (abs_nonneg _).trans (hC 0); simpa using this
      have hss : Real.sqrt (2 * n + 1) ^ 2 = 2 * n + 1 := Real.sq_sqrt hp.le
      have hsp : 0 < Real.sqrt (2 * n + 1) := Real.sqrt_pos.mpr hp
      have hs1 : 1 ≤ Real.sqrt (2 * n + 1) := by
        rw [Real.one_le_sqrt]; linarith [Nat.cast_nonneg (α := ℝ) n]
      set S := Real.sqrt (2 * n + 1) with hS
      have key : S ^ (k' + 1) * ((S ^ 2) ^ k')⁻¹ ≤ S⁻¹ := by
        rw [← pow_mul]
        have h2 : S ^ (k' + 2) ≤ S ^ (2 * k') := pow_le_pow_right₀ hs1 (by omega)
        calc S ^ (k' + 1) * (S ^ (2 * k'))⁻¹ = S ^ (k' + 2) * (S ^ (2 * k'))⁻¹ * S⁻¹ := by
              field_simp; ring
          _ ≤ S ^ (2 * k') * (S ^ (2 * k'))⁻¹ * S⁻¹ := by gcongr
          _ = S⁻¹ := by field_simp
      calc Real.sqrt n ^ (k' + 1) * |GORZ.fd (fun j => Real.log (2 * ((n + j : ℕ) : ℝ) + 1)) k'|
          ≤ S ^ (k' + 1) * (C * ((2 * (n : ℝ) + 1) ^ k')⁻¹) :=
            mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _) (hC n) (abs_nonneg _) (by positivity)
        _ = C * (S ^ (k' + 1) * ((S ^ 2) ^ k')⁻¹) := by rw [hss]; ring
        _ ≤ C * S⁻¹ := by gcongr
    have hlim : Tendsto (fun n : ℕ => C * (Real.sqrt (2 * n + 1))⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => Real.sqrt (2 * n + 1)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp
          (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
      simpa using this.inv_tendsto_atTop.const_mul C
    have h0 : Tendsto (fun n : ℕ => Real.sqrt n ^ (k' + 1) * dlog aXi n (k' + 1)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hlim
    simpa using h0.const_mul (Real.sqrt 2 ^ (k' + 1))
  refine gorz_thm3_diff gammaXi δXi d hδ0 hδpos hαpos ?_ ?_
  · have := ha2.add (hBk 2 le_rfl)
    rw [add_zero] at this
    exact this.congr' ((hratio 2).mono fun n hn => hn.symm)
  · intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    have := (hak k hk3).add (hBk k (by omega))
    rw [add_zero] at this
    exact this.congr' ((hratio k).mono fun n hn => hn.symm)

end GORZXi
