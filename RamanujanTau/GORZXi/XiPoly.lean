/-
# Small-coefficient polynomials in `j` and forward differences of `log` (for `XiKernelHyp`)

`SP K η C N p f` : on `j ≤ K`, `f j = Σ_{i∈ι} a_i j^{d_i}` with `#ι ≤ N`, `d_i ≥ p`, `|a_i| ≤ C η^{d_i}`.
The class is closed under `+`, `·`, powers and scalars, and

* `abs_fd_SP` : `|Δ^k f(0)| ≤ N C 2^k (kη)^k`  (`Δ^k j^d = 0` for `d < k`);
* **`abs_fd_log_SP`** : if `q` is `SP` with all degrees `≥ 1` and `η` is small, then
  `|Δ^k[log(1 + q)](0)| ≤ Λ η^k`, with `Λ` depending only on `k, K, N, C` (truncated `log` series +
  Mathlib's remainder bound `Real.abs_log_sub_add_sum_range_le`).
* **`abs_dlog_of_SP`** : the same for `β(n+j) = P Q^j (w₀ + q(j))`, `w₀ ≥ 1/2`, `k ≥ 2`.
-/
import RamanujanTau.GORZXi.XiMain

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter

/-- small-coefficient polynomial representation on `j ≤ K`. -/
def SP (K : ℕ) (η C : ℝ) (N p : ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (d : ι → ℕ), Fintype.card ι ≤ N ∧ (∀ i, p ≤ d i) ∧
    (∀ i, |a i| ≤ C * η ^ d i) ∧ ∀ j ≤ K, f j = ∑ i, a i * (j : ℝ) ^ d i

namespace SP

variable {K : ℕ} {η C C' : ℝ} {N M p p' : ℕ} {f g : ℕ → ℝ}

lemma mono (h : SP K η C N p f) {C₁ : ℝ} {N₁ p₁ : ℕ} (hC : C ≤ C₁) (hN : N ≤ N₁) (hp : p₁ ≤ p)
    (hη : 0 ≤ η) : SP K η C₁ N₁ p₁ f := by
  obtain ⟨ι, _, a, d, h1, h2, h3, h4⟩ := h
  exact ⟨ι, inferInstance, a, d, h1.trans hN, fun i => hp.trans (h2 i),
    fun i => (h3 i).trans (mul_le_mul_of_nonneg_right hC (pow_nonneg hη _)), h4⟩

lemma congr (h : SP K η C N p f) (hfg : ∀ j ≤ K, f j = g j) : SP K η C N p g := by
  obtain ⟨ι, _, a, d, h1, h2, h3, h4⟩ := h
  exact ⟨ι, inferInstance, a, d, h1, h2, h3, fun j hj => (hfg j hj).symm.trans (h4 j hj)⟩

lemma const (r : ℝ) (hr : |r| ≤ C) : SP K η C 1 0 (fun _ => r) :=
  ⟨Unit, inferInstance, fun _ => r, fun _ => 0, by simp, fun _ => le_rfl, fun _ => by simpa using hr,
    fun j _ => by simp⟩

lemma monom (r : ℝ) (e : ℕ) (hr : |r| ≤ C * η ^ e) : SP K η C 1 e (fun j => r * (j : ℝ) ^ e) :=
  ⟨Unit, inferInstance, fun _ => r, fun _ => e, by simp, fun _ => le_rfl, fun _ => hr,
    fun j _ => by simp⟩

lemma add {N' : ℕ} (hf : SP K η C N p f) (hg : SP K η C N' p g) :
    SP K η C (N + N') p (fun j => f j + g j) := by
  obtain ⟨ι, _, a, d, h1, h2, h3, h4⟩ := hf
  obtain ⟨κ, _, b, e, h1', h2', h3', h4'⟩ := hg
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim a b, Sum.elim d e, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]; omega
  · rintro (i | i) <;> simp [h2, h2']
  · rintro (i | i) <;> simp [h3, h3']
  · intro j hj; rw [Fintype.sum_sum_type]; simp only [h4 j hj, h4' j hj, Sum.elim_inl, Sum.elim_inr]

lemma mul (hf : SP K η C N p f) (hg : SP K η C' M p' g) :
    SP K η (C * C') (N * M) (p + p') (fun j => f j * g j) := by
  obtain ⟨ι, _, a, d, h1, h2, h3, h4⟩ := hf
  obtain ⟨κ, _, b, e, h1', h2', h3', h4'⟩ := hg
  refine ⟨ι × κ, inferInstance, fun x => a x.1 * b x.2, fun x => d x.1 + e x.2, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_prod]; exact Nat.mul_le_mul h1 h1'
  · intro x; have := h2 x.1; have := h2' x.2; show p + p' ≤ d x.1 + e x.2; omega
  · intro x
    rw [abs_mul, pow_add]
    calc |a x.1| * |b x.2| ≤ (C * η ^ d x.1) * (C' * η ^ e x.2) :=
          mul_le_mul (h3 _) (h3' _) (abs_nonneg _) ((abs_nonneg _).trans (h3 _))
      _ = _ := by ring
  · intro j hj
    dsimp only
    rw [h4 j hj, h4' j hj, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
    rw [pow_add]; ring

lemma smul (hf : SP K η C N p f) (r : ℝ) {R : ℝ} (hr : |r| ≤ R) :
    SP K η (R * C) N p (fun j => r * f j) := by
  have := (const (K := K) (η := η) r hr).mul hf
  simpa using this

lemma one : SP K η 1 1 0 (fun _ => 1) := const 1 (by simp)

lemma pow (hf : SP K η C N p f) : ∀ r : ℕ, SP K η (C ^ r) (N ^ r) (p * r) (fun j => f j ^ r)
  | 0 => by simpa using (one (K := K) (η := η))
  | r + 1 => by
    have := (pow hf r).mul hf
    simpa [pow_succ, Nat.mul_succ] using this

lemma neg (hf : SP K η C N p f) : SP K η C N p (fun j => -f j) := by
  have := hf.smul (-1) (R := 1) (by simp)
  simpa using this

/-- removing the constant term. -/
lemma sub_zero' (hf : SP K η C N 0 f) (hC : 0 ≤ C) (hη : 0 ≤ η) :
    SP K η C N 1 (fun j => f j - f 0) := by
  obtain ⟨ι, _, a, d, h1, _, h3, h4⟩ := hf
  classical
  refine ⟨ι, inferInstance, fun i => if d i = 0 then 0 else a i, fun i => if d i = 0 then 1 else d i,
    h1, fun i => by dsimp only; split_ifs with h <;> omega, fun i => ?_, fun j hj => ?_⟩
  · dsimp only
    split_ifs with h
    · simpa using mul_nonneg hC hη
    · exact h3 i
  · dsimp only
    rw [h4 j hj, h4 0 (Nat.zero_le _), ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp [h]
    · simp [zero_pow h]

end SP

/-! ## forward differences -/

lemma fd_sum' {ι : Type} (s : Finset ι) (w : ι → ℕ → ℝ) (k : ℕ) :
    GORZ.fd (fun j => ∑ i ∈ s, w i j) k = ∑ i ∈ s, GORZ.fd (w i) k := by
  simp only [GORZ.fd, mul_sum]; rw [sum_comm]

lemma fd_mul_const (w : ℕ → ℝ) (r : ℝ) (k : ℕ) : GORZ.fd (fun j => r * w j) k = r * GORZ.fd w k := by
  simp only [GORZ.fd, mul_sum]; exact sum_congr rfl fun _ _ => by ring

lemma fd_congr {w v : ℕ → ℝ} {k : ℕ} (h : ∀ j ≤ k, w j = v j) : GORZ.fd w k = GORZ.fd v k := by
  unfold GORZ.fd
  exact sum_congr rfl fun j hj => by rw [h j (by simp at hj; omega)]

lemma abs_fd_le (w : ℕ → ℝ) (k : ℕ) {B : ℝ} (hB : ∀ j ≤ k, |w j| ≤ B) : |GORZ.fd w k| ≤ 2 ^ k * B := by
  unfold GORZ.fd
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (k + 1), |(-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * w j|
      ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ) * B := by
        refine sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hB j (by simp at hj; omega)) (Nat.cast_nonneg _)
    _ = 2 ^ k * B := by rw [← Finset.sum_mul, sum_choose_real]

lemma abs_apow_le (k d : ℕ) : |apow k d| ≤ 2 ^ k * (k : ℝ) ^ d := by
  have := abs_fd_le (fun j => (j : ℝ) ^ d) k (B := (k : ℝ) ^ d) (fun j hj => by
    rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hj) _)
  simpa [GORZ.fd, apow] using this

lemma fd_linear (a b : ℝ) {k : ℕ} (hk : 2 ≤ k) : GORZ.fd (fun j => a + b * (j : ℝ)) k = 0 := by
  rw [fd_add, fd_const _ (by omega), fd_mul_const]
  have : GORZ.fd (fun j => (j : ℝ)) k = apow k 1 := by simp [GORZ.fd, apow]
  rw [this, apow_lt (by omega)]; ring

/-- `|Δ^k f(0)| ≤ N C 2^k (kη)^k`. -/
lemma abs_fd_SP {K : ℕ} {η C : ℝ} {N p : ℕ} {f : ℕ → ℝ} (hf : SP K η C N p f) {k : ℕ} (hk : k ≤ K)
    (hη : 0 ≤ η) (hkη : (k : ℝ) * η ≤ 1) (hC : 0 ≤ C) :
    |GORZ.fd f k| ≤ N * C * 2 ^ k * ((k : ℝ) * η) ^ k := by
  obtain ⟨ι, _, a, d, h1, _, h3, h4⟩ := hf
  have e : GORZ.fd f k = ∑ i, a i * apow k (d i) := by
    rw [fd_congr (v := fun j => ∑ i, a i * (j : ℝ) ^ d i) (fun j hj => h4 j (hj.trans hk)), fd_sum']
    refine sum_congr rfl fun i _ => ?_
    rw [fd_mul_const]; simp [GORZ.fd, apow]
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i, |a i * apow k (d i)| ≤ C * 2 ^ k * ((k : ℝ) * η) ^ k := by
    intro i
    rcases lt_or_ge (d i) k with hlt | hge
    · rw [apow_lt hlt, mul_zero, abs_zero]; positivity
    · rw [abs_mul]
      calc |a i| * |apow k (d i)| ≤ (C * η ^ d i) * (2 ^ k * (k : ℝ) ^ d i) :=
            mul_le_mul (h3 i) (abs_apow_le _ _) (abs_nonneg _) ((abs_nonneg _).trans (h3 i))
        _ = C * 2 ^ k * ((k : ℝ) * η) ^ d i := by rw [mul_pow]; ring
        _ ≤ C * 2 ^ k * ((k : ℝ) * η) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hkη hge) (by positivity)
  calc ∑ i, |a i * apow k (d i)| ≤ ∑ _i : ι, C * 2 ^ k * ((k : ℝ) * η) ^ k := sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * (C * 2 ^ k * ((k : ℝ) * η) ^ k) := by simp
    _ ≤ N * (C * 2 ^ k * ((k : ℝ) * η) ^ k) := by gcongr
    _ = _ := by ring

/-- `|f j| ≤ N C (Kη)^p` on `j ≤ K`. -/
lemma abs_SP_le {K : ℕ} {η C : ℝ} {N p : ℕ} {f : ℕ → ℝ} (hf : SP K η C N p f)
    (hη : 0 ≤ η) (hKη : (K : ℝ) * η ≤ 1) (hC : 0 ≤ C) {j : ℕ} (hj : j ≤ K) :
    |f j| ≤ N * C * ((K : ℝ) * η) ^ p := by
  obtain ⟨ι, _, a, d, h1, h2, h3, h4⟩ := hf
  rw [h4 j hj]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hterm : ∀ i, |a i * (j : ℝ) ^ d i| ≤ C * ((K : ℝ) * η) ^ p := by
    intro i
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) ^ d i)]
    calc |a i| * (j : ℝ) ^ d i ≤ (C * η ^ d i) * (K : ℝ) ^ d i :=
          mul_le_mul (h3 i) (pow_le_pow_left₀ (Nat.cast_nonneg _) hjK _) (by positivity)
            ((abs_nonneg _).trans (h3 i))
      _ = C * ((K : ℝ) * η) ^ d i := by rw [mul_pow]; ring
      _ ≤ C * ((K : ℝ) * η) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hKη (h2 i)) hC
  calc ∑ i, |a i * (j : ℝ) ^ d i| ≤ ∑ _i : ι, C * ((K : ℝ) * η) ^ p := sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * (C * ((K : ℝ) * η) ^ p) := by simp
    _ ≤ N * (C * ((K : ℝ) * η) ^ p) := by gcongr
    _ = _ := by ring

/-- the constant of `abs_fd_log_SP`. -/
noncomputable def logConst (k K N : ℕ) (C : ℝ) : ℝ :=
  (∑ i ∈ range (k - 1), (N : ℝ) ^ (i + 1) * C ^ (i + 1) * 2 ^ k * (k : ℝ) ^ k) +
    2 ^ k * (2 * ((N : ℝ) * C * K) ^ k)

/-- **`|Δ^k[log(1+q)](0)| ≤ Λ η^k`** for `q` small-coefficient with degrees `≥ 1`. -/
theorem abs_fd_log_SP {K : ℕ} {η C : ℝ} {N : ℕ} {q : ℕ → ℝ} (hq : SP K η C N 1 q) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ K) (hη : 0 ≤ η) (hC : 0 ≤ C) (hKη : (K : ℝ) * η ≤ 1)
    (hsmall : (N : ℝ) * C * ((K : ℝ) * η) ≤ 1 / 2) :
    |GORZ.fd (fun j => Real.log (1 + q j)) k| ≤ logConst k K N C * η ^ k := by
  have hkη : (k : ℝ) * η ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hη).trans hKη
  have hqb : ∀ j ≤ K, |q j| ≤ (N : ℝ) * C * ((K : ℝ) * η) := fun j hj => by
    simpa using abs_SP_le hq hη hKη hC hj
  -- log(1+x) = -(Σ_{i<k-1} (-x)^{i+1}/(i+1)) + E
  set E : ℕ → ℝ := fun j => Real.log (1 + q j) + ∑ i ∈ range (k - 1), (-q j) ^ (i + 1) / (i + 1) with hE
  have hsplit : (fun j => Real.log (1 + q j)) =
      fun j => (∑ i ∈ range (k - 1), (-(1 / ((i : ℝ) + 1))) * (-q j) ^ (i + 1)) + E j := by
    funext j; simp only [hE]; rw [← sub_eq_zero]
    rw [show ∑ i ∈ range (k - 1), (-q j) ^ (i + 1) / ((i : ℝ) + 1) =
      -∑ i ∈ range (k - 1), (-(1 / ((i : ℝ) + 1))) * (-q j) ^ (i + 1) by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring]
    ring
  have hEb : ∀ j ≤ k, |E j| ≤ 2 * ((N : ℝ) * C * K) ^ k * η ^ k := by
    intro j hj
    have hq1 := hqb j (hj.trans hk)
    have hx : |(-q j)| < 1 := by rw [abs_neg]; linarith
    have h := Real.abs_log_sub_add_sum_range_le hx (k - 1)
    rw [sub_neg_eq_add, show k - 1 + 1 = k by omega, abs_neg] at h
    have h' : |E j| ≤ |q j| ^ k / (1 - |q j|) := by
      simp only [hE]; rw [add_comm]; exact h
    have hden : 1 / 2 ≤ 1 - |q j| := by linarith
    calc |E j| ≤ |q j| ^ k / (1 - |q j|) := h'
      _ ≤ |q j| ^ k / (1 / 2) := by gcongr
      _ = 2 * |q j| ^ k := by ring
      _ ≤ 2 * ((N : ℝ) * C * ((K : ℝ) * η)) ^ k := by gcongr
      _ = _ := by ring
  rw [hsplit, fd_add, fd_sum']
  have hpow : ∀ i ∈ range (k - 1), |GORZ.fd (fun j => (-(1 / ((i : ℝ) + 1))) * (-q j) ^ (i + 1)) k| ≤
      (N : ℝ) ^ (i + 1) * C ^ (i + 1) * 2 ^ k * (k : ℝ) ^ k * η ^ k := by
    intro i _
    rw [fd_mul_const, abs_mul]
    have hsp := (hq.neg).pow (i + 1)
    have h1 := abs_fd_SP hsp hk hη hkη (pow_nonneg hC _)
    have hc : |(-(1 / ((i : ℝ) + 1)))| ≤ 1 := by
      rw [abs_neg, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    calc |(-(1 / ((i : ℝ) + 1)))| * |GORZ.fd (fun j => (-q j) ^ (i + 1)) k|
        ≤ 1 * (((N ^ (i + 1) : ℕ) : ℝ) * C ^ (i + 1) * 2 ^ k * ((k : ℝ) * η) ^ k) :=
          mul_le_mul hc h1 (abs_nonneg _) zero_le_one
      _ = _ := by push_cast; rw [mul_pow]; ring
  have hEfd := abs_fd_le E k hEb
  calc |∑ i ∈ range (k - 1), GORZ.fd (fun j => (-(1 / ((i : ℝ) + 1))) * (-q j) ^ (i + 1)) k + GORZ.fd E k|
      ≤ ∑ i ∈ range (k - 1), |GORZ.fd (fun j => (-(1 / ((i : ℝ) + 1))) * (-q j) ^ (i + 1)) k| +
          |GORZ.fd E k| := (abs_add_le _ _).trans (by gcongr; exact abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ range (k - 1), (N : ℝ) ^ (i + 1) * C ^ (i + 1) * 2 ^ k * (k : ℝ) ^ k * η ^ k +
          2 ^ k * (2 * ((N : ℝ) * C * K) ^ k * η ^ k) := add_le_add (sum_le_sum hpow) hEfd
    _ = logConst k K N C * η ^ k := by
        rw [logConst, add_mul, Finset.sum_mul]; ring

/-- **`|Δ^k log β(n+·)| ≤ Λ η^k`** when `β(n+j) = P Q^j (w₀ + q(j))` on `j ≤ k`. -/
theorem abs_dlog_of_SP (β : ℕ → ℝ) (n : ℕ) {K : ℕ} {η C : ℝ} {N : ℕ} {q : ℕ → ℝ} (hq : SP K η C N 1 q)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ K) {P Q w0 : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hw0 : 1 / 2 ≤ w0)
    (hβ : ∀ j ≤ k, β (n + j) = P * Q ^ j * (w0 + q j))
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hKη : (K : ℝ) * η ≤ 1) (hsmall : (N : ℝ) * (2 * C) * ((K : ℝ) * η) ≤ 1 / 2) :
    |dlog β n k| ≤ logConst k K N (2 * C) * η ^ k := by
  have hw0p : 0 < w0 := by linarith
  have hq' : SP K η (2 * C) N 1 (fun j => w0⁻¹ * q j) :=
    hq.smul w0⁻¹ (R := 2) (by rw [abs_of_pos (inv_pos.mpr hw0p)]; rw [inv_le_comm₀ hw0p two_pos]; linarith)
  have hval : ∀ j ≤ k, |w0⁻¹ * q j| ≤ (N : ℝ) * (2 * C) * ((K : ℝ) * η) := fun j hj => by
    simpa using abs_SP_le hq' hη hKη (by linarith) (hj.trans hk)
  have hlog : ∀ j ≤ k, Real.log (β (n + j)) =
      (Real.log P + Real.log w0) + Real.log Q * (j : ℝ) + Real.log (1 + w0⁻¹ * q j) := by
    intro j hj
    have h1 : 0 < 1 + w0⁻¹ * q j := by
      have := hval j hj; have := neg_abs_le (w0⁻¹ * q j); linarith
    rw [hβ j hj, show w0 + q j = w0 * (1 + w0⁻¹ * q j) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul hw0p.ne' h1.ne', Real.log_pow]
    ring
  unfold dlog
  rw [fd_congr hlog, fd_add, fd_linear _ _ hk2, zero_add]
  exact abs_fd_log_SP hq' (by omega) hk hη (by linarith) hKη hsmall

end GORZXi
