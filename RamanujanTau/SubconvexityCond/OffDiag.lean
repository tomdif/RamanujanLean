/-
# The off-diagonal: one shift `h`, via Abel summation against the SCS hypothesis

For coefficients `aₙ = λ(n) g(n)` with `|g(n)| ≤ K n^{−1/2}`, `|g(n) − g(n+1)| ≤ K n^{−3/2}` and
`g(n) = 0` for `n > N`, and parameters `1 ≤ ρ ≤ H`:

    |S_h| ≤ K² ( 2C N^{2+B} (3+|T|N) e^{−ρ²/64}
               + [hH ≤ Nρ] · 2C h^B (hH/ρ)^{−η} ((2+|T|ρ/H)(1+log N) + 1) )        (`offS_bound`)

whenever `|A_h(n)| ≤ C (n+h)^{1−η} h^B` for all `n`.  The first term is the region `n < hH/ρ`
(where the Gaussian factor is `≤ e^{−ρ²/64}`), the second the band `n ≥ hH/ρ`.
-/
import RamanujanTau.SubconvexityCond.Kernel

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset

/-- Size / variation / support hypotheses on the smooth weight `g`. -/
structure GBound (g : ℕ → ℝ) (K : ℝ) (N : ℕ) : Prop where
  nonneg : 0 ≤ K
  size : ∀ n : ℕ, 1 ≤ n → |g n| ≤ K / Real.sqrt n
  diff : ∀ n : ℕ, 1 ≤ n → |g n - g (n + 1)| ≤ K / (n * Real.sqrt n)
  vanish : ∀ n : ℕ, N < n → g n = 0

lemma abs_mul_le_of {x y p q : ℝ} (hx : |x| ≤ p) (hy : |y| ≤ q) : |x * y| ≤ p * q := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

namespace GBound

variable {g : ℕ → ℝ} {K : ℝ} {N : ℕ}

lemma size' (hg : GBound g K N) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |g m| ≤ K / Real.sqrt n := by
  refine (hg.size m (by omega)).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left hg.nonneg (Real.sqrt_pos.2 hn0)
    (Real.sqrt_le_sqrt (by exact_mod_cast hnm))

lemma diff' (hg : GBound g K N) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |g m - g (m + 1)| ≤ K / (n * Real.sqrt n) := by
  refine (hg.diff m (by omega)).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine div_le_div_of_nonneg_left hg.nonneg (by positivity) ?_
  exact mul_le_mul hm (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _) (by linarith)

lemma u_le (hg : GBound g K N) (h : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |g (n + h) * g n| ≤ K ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (abs_mul_le_of (hg.size' hn (by omega)) (hg.size' hn le_rfl)).trans_eq ?_
  rw [div_mul_div_comm, Real.mul_self_sqrt hn0.le, sq]

lemma u_diff (hg : GBound g K N) (h : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |g (n + h) * g n - g (n + 1 + h) * g (n + 1)| ≤ 2 * K ^ 2 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : g (n + h) * g n - g (n + 1 + h) * g (n + 1) =
      g (n + h) * (g n - g (n + 1)) + g (n + 1) * (g (n + h) - g (n + h + 1)) := by
    rw [show n + 1 + h = n + h + 1 by omega]; ring
  rw [e]
  have h1 := abs_mul_le_of (hg.size' (m := n + h) hn (by omega)) (hg.diff' hn le_rfl)
  have h2 := abs_mul_le_of (hg.size' (m := n + 1) hn (by omega))
    (hg.diff' (m := n + h) hn (by omega))
  have e2 : K / Real.sqrt n * (K / (n * Real.sqrt n)) = K ^ 2 / (n : ℝ) ^ 2 := by
    rw [div_mul_div_comm, show Real.sqrt n * (n * Real.sqrt n) = (n : ℝ) ^ 2 by
      rw [mul_left_comm, Real.mul_self_sqrt hn0.le, sq], sq K]
  rw [e2] at h1 h2
  refine (abs_add_le _ _).trans ?_
  have : 2 * K ^ 2 / (n : ℝ) ^ 2 = K ^ 2 / (n : ℝ) ^ 2 + K ^ 2 / (n : ℝ) ^ 2 := by ring
  linarith

end GBound

/-- The weight `G_h(n) = g(n+h) g(n) E_h(n) cos(T ℓ_h(n))`. -/
noncomputable def Gw (g : ℕ → ℝ) (H T : ℝ) (h n : ℕ) : ℝ :=
  g (n + h) * g n * (Ef H h n * Real.cos (ell h n * T))

/-- The variation bound `φ_h(n)`. -/
noncomputable def phiB (H T : ℝ) (h n : ℕ) : ℝ :=
  2 * Ef H h (n + 1) / (n : ℝ) ^ 2 + (Ef H h (n + 1) - Ef H h n) / n +
    Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3

lemma phiB_nonneg {H : ℝ} (hH : 0 ≤ H) (T : ℝ) (h : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ phiB H T h n := by
  have := Ef_mono hH (h := h) hn
  have := Ef_pos H h (n + 1)
  have : 0 ≤ Ef H h (n + 1) - Ef H h n := by linarith
  unfold phiB; positivity

lemma Gw_diff {g : ℕ → ℝ} {K : ℝ} {N : ℕ} (hg : GBound g K N) {H : ℝ} (hH : 0 ≤ H) (T : ℝ)
    (h : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |Gw g H T h n - Gw g H T h (n + 1)| ≤ K ^ 2 * phiB H T h n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set E0 := Ef H h n
  set E1 := Ef H h (n + 1)
  have hE0 : 0 < E0 := Ef_pos H h n
  have hE01 : E0 ≤ E1 := Ef_mono hH hn
  set c0 := Real.cos (ell h n * T)
  set c1 := Real.cos (ell h (n + 1) * T)
  set u0 := g (n + h) * g n
  set u1 := g (n + 1 + h) * g (n + 1)
  have e : Gw g H T h n - Gw g H T h (n + 1) = (u0 - u1) * (E0 * c0) +
      u1 * ((E0 - E1) * c0 + E1 * (c0 - c1)) := by
    simp only [Gw, u0, u1, E0, E1, c0, c1]; ring
  rw [e]
  have hu := hg.u_diff h hn
  have hu1 : |u1| ≤ K ^ 2 / n := by
    refine (hg.u_le h (n := n + 1) (by omega)).trans ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by push_cast; linarith)
  have hw0 : |E0 * c0| ≤ E1 := by
    rw [abs_mul, abs_of_pos hE0]
    calc E0 * |c0| ≤ E0 * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hE0.le
      _ ≤ E1 := by linarith
  have hcc : |c0 - c1| ≤ |T| * h / (n : ℝ) ^ 2 := by
    refine (abs_cos_sub_cos_le _ _).trans ?_
    rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith [ell_succ_le (h := h) hn]), mul_comm,
      mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (ell_sub_succ_le hn) (abs_nonneg _)
  have hw : |(E0 - E1) * c0 + E1 * (c0 - c1)| ≤ (E1 - E0) + E1 * (|T| * h / (n : ℝ) ^ 2) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonpos (by linarith)]
      calc -(E0 - E1) * |c0| ≤ -(E0 - E1) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by linarith)
        _ = E1 - E0 := by ring
    · rw [abs_mul, abs_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_left hcc (by linarith)
  refine (abs_add_le _ _).trans ?_
  have t1 := abs_mul_le_of hu hw0
  have t2 := abs_mul_le_of hu1 hw
  unfold phiB
  have e3 : 2 * K ^ 2 / (n : ℝ) ^ 2 * E1 + K ^ 2 / n * (E1 - E0 + E1 * (|T| * h / (n : ℝ) ^ 2)) =
      K ^ 2 * (2 * E1 / (n : ℝ) ^ 2 + (E1 - E0) / n + E1 * |T| * h / (n : ℝ) ^ 3) := by
    field_simp; ring
  linarith

/-- `S_h` written as a sum of `λ(n)λ(n+h) G_h(n)`. -/
lemma offS_eq (g : ℕ → ℝ) (H T : ℝ) (N h : ℕ) :
    offS (fun n => lam n * g n) H T N h = ∑ n ∈ Icc 1 N, (lam n * lam (n + h)) * Gw g H T h n := by
  unfold offS Gw
  refine sum_congr rfl fun n _ => ?_
  rw [kw_shift]; ring

set_option maxHeartbeats 800000 in
/-- **The off-diagonal bound for one shift `h`.** -/
theorem offS_bound {η B C K H ρ T : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hC0 : 0 ≤ C)
    (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {g : ℕ → ℝ} {N h : ℕ} (hg : GBound g K N) (hh : 1 ≤ h)
    (hhN : h ≤ N) (hA : ∀ n : ℕ, |shiftSum h n| ≤ C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B) :
    |offS (fun n => lam n * g n) H T N h| ≤
      K ^ 2 * (2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * Real.exp (-ρ ^ 2 / 64) +
        (if (h : ℝ) * H ≤ N * ρ then
          2 * C * (h : ℝ) ^ B * ((h : ℝ) * H / ρ) ^ (-η) *
            ((2 + |T| * ρ / H) * (1 + Real.log N) + 1) else 0)) := by
  have hH0 : 0 < H := by linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hh.trans hhN)
  have hhNr : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hK := hg.nonneg
  set ε0 := Real.exp (-ρ ^ 2 / 64)
  have hε0 : 0 < ε0 := Real.exp_pos _
  -- Abel summation
  rw [offS_eq, abel_Icc]
  have hG : Gw g H T h (N + 1) = 0 := by simp [Gw, hg.vanish (N + 1) (by omega)]
  rw [hG, mul_zero, zero_add]
  set α : ℕ → ℝ := fun n => C * ((n : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B with hα
  have hα0 : ∀ n : ℕ, 0 ≤ α n := fun n => by simp only [hα]; positivity
  have step1 : |∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, lam k * lam (k + h)) *
      (Gw g H T h n - Gw g H T h (n + 1))| ≤ K ^ 2 * ∑ n ∈ Icc 1 N, α n * phiB H T h n := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    rw [abs_mul]
    have h1 : |∑ k ∈ Icc 1 n, lam k * lam (k + h)| ≤ α n := hA n
    have h2 := Gw_diff hg hH0.le T h hn1
    have := phiB_nonneg hH0.le T h hn1
    calc |∑ k ∈ Icc 1 n, lam k * lam (k + h)| * |Gw g H T h n - Gw g H T h (n + 1)|
        ≤ α n * (K ^ 2 * phiB H T h n) := mul_le_mul h1 h2 (abs_nonneg _) (hα0 n)
      _ = K ^ 2 * (α n * phiB H T h n) := by ring
  refine step1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg K))
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n : ℕ => (n : ℝ) * ρ < h * H)]
  refine add_le_add ?_ ?_
  · -- region 1: the Gaussian factor is tiny
    have hterm : ∀ n ∈ (Icc 1 N).filter (fun n : ℕ => (n : ℝ) * ρ < h * H),
        α n * phiB H T h n ≤ 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hnρ⟩ := hn
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
      have hsm := Ef_small hρ hρH hh hn1 hnρ
      have hE0 := Ef_pos H h n
      have hEm := Ef_mono hH0.le (h := h) hn1
      have ha : α n ≤ C * (2 * N) * (N : ℝ) ^ B := by
        simp only [hα]
        have h1 : ((n : ℝ) + h) ^ (1 - η) ≤ 2 * N := by
          calc ((n : ℝ) + h) ^ (1 - η) ≤ ((n : ℝ) + h) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ ≤ 2 * N := by rw [Real.rpow_one]; linarith
        have h2 : (h : ℝ) ^ B ≤ (N : ℝ) ^ B := Real.rpow_le_rpow (by linarith) hhNr hB
        gcongr
      have hp : phiB H T h n ≤ (3 + |T| * N) * ε0 := by
        unfold phiB
        have a1 : 2 * Ef H h (n + 1) / (n : ℝ) ^ 2 ≤ 2 * ε0 := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          nlinarith
        have a2 : (Ef H h (n + 1) - Ef H h n) / n ≤ ε0 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        have a3 : Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3 ≤ ε0 * |T| * N := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1r
          have hT := abs_nonneg T
          have b1 : Ef H h (n + 1) * |T| * h ≤ ε0 * |T| * N := by
            have := mul_le_mul hsm hhNr (by linarith) hε0.le
            nlinarith
          have : 0 ≤ ε0 * |T| * N := by positivity
          nlinarith
        nlinarith
      have hp0 := phiB_nonneg hH0.le T h hn1
      calc α n * phiB H T h n ≤ (C * (2 * N) * (N : ℝ) ^ B) * ((3 + |T| * N) * ε0) :=
            mul_le_mul ha hp hp0 (by positivity)
        _ = 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by ring
    refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
    have hc : (((Icc 1 N).filter (fun n : ℕ => (n : ℝ) * ρ < h * H)).card : ℝ) ≤ N := by
      have := card_filter_le (Icc 1 N) (fun n : ℕ => (n : ℝ) * ρ < h * H)
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : _ ≤ N)
    have : 0 ≤ 2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by positivity
    calc _ ≤ (N : ℝ) * (2 * C * (N : ℝ) * (N : ℝ) ^ B * (3 + |T| * N) * ε0) :=
          mul_le_mul_of_nonneg_right hc this
      _ = 2 * C * (N : ℝ) ^ 2 * (N : ℝ) ^ B * (3 + |T| * N) * ε0 := by ring
  · -- region 2: the band `n ≥ hH/ρ`
    split_ifs with hband
    · set n0 : ℝ := (h : ℝ) * H / ρ with hn0def
      have hn0pos : 0 < n0 := by positivity
      set Q : ℝ := 2 + |T| * ρ / H
      have hterm : ∀ n ∈ (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H),
          α n * phiB H T h n ≤ 2 * C * (h : ℝ) ^ B * n0 ^ (-η) *
            (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) := by
        intro n hn
        rw [mem_filter, mem_Icc, not_lt] at hn
        obtain ⟨⟨hn1, _⟩, hnρ⟩ := hn
        have hn0r : (0 : ℝ) < n := by exact_mod_cast hn1
        have hnn0 : n0 ≤ n := by rw [hn0def, div_le_iff₀ (by linarith)]; linarith
        have hhn : (h : ℝ) ≤ n := by
          have : (h : ℝ) * ρ ≤ h * H := mul_le_mul_of_nonneg_left hρH (by linarith)
          nlinarith
        have hE0 := Ef_pos H h n
        have hEm := Ef_mono hH0.le (h := h) hn1
        have hE1 := Ef_le_one H h (n + 1)
        -- `(n+h)^{1−η} ≤ 2 n · n^{−η}`
        have ha : ((n : ℝ) + h) ^ (1 - η) ≤ 2 * (n : ℝ) * (n : ℝ) ^ (-η) := by
          calc ((n : ℝ) + h) ^ (1 - η) ≤ (2 * (n : ℝ)) ^ (1 - η) :=
                Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
            _ = (2 : ℝ) ^ (1 - η) * ((n : ℝ) * (n : ℝ) ^ (-η)) := by
                rw [Real.mul_rpow (by norm_num) hn0r.le, sub_eq_add_neg, Real.rpow_add hn0r,
                  Real.rpow_one]
            _ ≤ 2 * ((n : ℝ) * (n : ℝ) ^ (-η)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                calc (2 : ℝ) ^ (1 - η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  _ = 2 := Real.rpow_one 2
            _ = 2 * (n : ℝ) * (n : ℝ) ^ (-η) := by ring
        have hpow : (n : ℝ) ^ (-η) ≤ n0 ^ (-η) :=
          Real.rpow_le_rpow_of_nonpos hn0pos hnn0 (by linarith)
        have hnphi : (n : ℝ) * phiB H T h n ≤ Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n) := by
          unfold phiB
          have hT := abs_nonneg T
          have b1 : (n : ℝ) * (2 * Ef H h (n + 1) / (n : ℝ) ^ 2) ≤ 2 * (1 / (n : ℝ)) := by
            rw [show (n : ℝ) * (2 * Ef H h (n + 1) / (n : ℝ) ^ 2) = 2 * Ef H h (n + 1) / n by
              field_simp]
            rw [div_le_iff₀ hn0r]; field_simp; linarith
          have b2 : (n : ℝ) * ((Ef H h (n + 1) - Ef H h n) / n) = Ef H h (n + 1) - Ef H h n := by
            field_simp
          have b3 : (n : ℝ) * (Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3) ≤
              |T| * ρ / H * (1 / (n : ℝ)) := by
            rw [show (n : ℝ) * (Ef H h (n + 1) * |T| * h / (n : ℝ) ^ 3) =
              Ef H h (n + 1) * (|T| * h / (n : ℝ) ^ 2) by field_simp]
            have c1 : |T| * h / (n : ℝ) ^ 2 ≤ |T| * ρ / H * (1 / (n : ℝ)) := by
              rw [div_le_iff₀ (by positivity)]
              have : (h : ℝ) * H ≤ n * ρ := hnρ
              have e5 : |T| * ρ / H * (1 / (n : ℝ)) * (n : ℝ) ^ 2 = |T| * (n * ρ) / H := by
                field_simp
              rw [e5, le_div_iff₀ hH0]
              have := mul_le_mul_of_nonneg_left hnρ (abs_nonneg T)
              linarith
            have : 0 ≤ |T| * h / (n : ℝ) ^ 2 := by positivity
            calc Ef H h (n + 1) * (|T| * h / (n : ℝ) ^ 2) ≤ 1 * (|T| * h / (n : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_right hE1 this
              _ ≤ _ := by linarith
          have : Q * (1 / (n : ℝ)) = 2 * (1 / (n : ℝ)) + |T| * ρ / H * (1 / (n : ℝ)) := by ring
          rw [mul_add, mul_add, b2, this]
          linarith
        have hp0 := phiB_nonneg hH0.le T h hn1
        have hbr : 0 ≤ Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n) := by
          have : 0 ≤ Q := by positivity
          have : 0 ≤ Ef H h (n + 1) - Ef H h n := by linarith
          positivity
        calc α n * phiB H T h n = C * (h : ℝ) ^ B * (((n : ℝ) + h) ^ (1 - η) * phiB H T h n) := by
              simp only [hα]; ring
          _ ≤ C * (h : ℝ) ^ B * (2 * (n : ℝ) ^ (-η) * ((n : ℝ) * phiB H T h n)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have := mul_le_mul_of_nonneg_right ha hp0
              nlinarith
          _ ≤ C * (h : ℝ) ^ B * (2 * n0 ^ (-η) *
                (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : 0 ≤ (n : ℝ) * phiB H T h n := by positivity
              have := mul_le_mul hpow hnphi this (by positivity)
              nlinarith
          _ = _ := by ring
      refine (sum_le_sum hterm).trans ?_
      have hsub : ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H),
          2 * C * (h : ℝ) ^ B * n0 ^ (-η) * (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) ≤
          ∑ n ∈ Icc 1 N,
          2 * C * (h : ℝ) ^ B * n0 ^ (-η) * (Q * (1 / (n : ℝ)) + (Ef H h (n + 1) - Ef H h n)) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => ?_
        have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
        have := Ef_mono hH0.le (h := h) hn1
        have : 0 ≤ Q := by positivity
        have : 0 ≤ Ef H h (n + 1) - Ef H h n := by linarith
        positivity
      refine hsub.trans ?_
      rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_telescope]
      have hHN : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
        have := RamanujanTau.MeanSquare.H_le_one_add_log N
        unfold RamanujanTau.MeanSquare.H at this; exact this
      have hQ : 0 ≤ Q := by positivity
      have hE1 := Ef_le_one H h (N + 1)
      have hE0 := Ef_pos H h 1
      have : 0 ≤ 2 * C * (h : ℝ) ^ B * n0 ^ (-η) := by positivity
      refine mul_le_mul_of_nonneg_left ?_ this
      have := mul_le_mul_of_nonneg_left hHN hQ
      linarith
    · -- empty band
      have hempty : (Icc 1 N).filter (fun n : ℕ => ¬ (n : ℝ) * ρ < h * H) = ∅ := by
        refine filter_eq_empty_iff.2 fun n hn => ?_
        rw [not_not]
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.1 hn).2
        have : (n : ℝ) * ρ ≤ N * ρ := mul_le_mul_of_nonneg_right hnN (by linarith)
        push Not at hband
        linarith
      rw [hempty, sum_empty]

end RamanujanTau.SubconvexityCond
