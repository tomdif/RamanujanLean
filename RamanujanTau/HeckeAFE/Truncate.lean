/-
# The truncated approximate functional equation on the critical line

From `tauL_afe_line` and the uniform decay `V_decay`:

* `tail_bound`: `‖Σ_{n≥N} τ(n) n^{−s} V_t(2πn/X)‖ ≤ C_A ((1+|t|)X)^A N^{−(A−3/4)}`, `A ≥ 3/4`,
  using only `Σ|τ(n)| n^{−27/4} < ∞` (Rankin–Selberg / Cauchy–Schwarz, `HeckeConvex`);
* **`tauL_afe_truncated_unbalanced`**: two lengths `N₁, N₂` and any `X > 0`:
  `|L(6+it) − S₁ − ε S₂| ≤ C_A [((1+|t|)X)^A N₁^{−(A−3/4)} + ((1+|t|)/X)^A N₂^{−(A−3/4)}]`;
* **`tauL_afe_truncated`**: `X = 1`, `N ≥ (1+|t|)^{1+η}` gives error `≤ C (1+|t|)^{−B}`;
* **`norm_tauL_le_afe`**: `|L(6+it)| ≤ |S₁(N)| + |S₂(N)| + C (1+|t|)^{−B}`.
-/
import RamanujanTau.HeckeAFE.Decay

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE

open Complex MeasureTheory Set Filter Topology Finset RamanujanTau.HeckeL
open scoped Real

/-- the AFE summand `τ(n) n^{−(6+it)} V(6+it, 2πn/X)`. -/
noncomputable def afeTerm (t X : ℝ) (n : ℕ) : ℂ :=
  tauC n * (n : ℂ) ^ (-(6 + t * I)) * V (6 + t * I) (2 * π * n / X)

lemma norm_afeTerm_le {A C₀ : ℝ} (hA : 0 < A) (hC₀0 : 0 ≤ C₀)
    (hC₀ : ∀ t ξ : ℝ, 0 < ξ → ‖V (6 + t * I) ξ‖ ≤ C₀ * ((1 + |t|) / ξ) ^ A)
    (t X : ℝ) (hX : 0 < X) (n : ℕ) :
    ‖afeTerm t X n‖ ≤ C₀ * ((1 + |t|) * X) ^ A * (|(tau n : ℝ)| / (n : ℝ) ^ (6 + A)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [afeTerm, tauC_zero, tau_zero]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
  have h1t : 0 < 1 + |t| := by positivity
  unfold afeTerm
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hnpos]
  have hτ : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
  rw [hτ]
  have hre : (-(6 + (t : ℂ) * I)).re = -6 := by simp
  rw [hre]
  have hV := hC₀ t (2 * π * n / X) (by positivity)
  have hξ : (1 + |t|) / (2 * π * n / X) ≤ (1 + |t|) * X / n := by
    rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hn']
    have : (1:ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h0 : 0 ≤ (1 + |t|) * X * n := by positivity
    nlinarith
  have hV' : ‖V (6 + t * I) (2 * π * n / X)‖ ≤ C₀ * (((1 + |t|) * X) ^ A / (n : ℝ) ^ A) := by
    refine hV.trans ?_
    rw [← Real.div_rpow (by positivity) hn'.le]
    gcongr
  have hpow : (n : ℝ) ^ (-6 : ℝ) * (1 / (n : ℝ) ^ A) = 1 / (n : ℝ) ^ (6 + A) := by
    rw [Real.rpow_add hn', Real.rpow_neg hn'.le]; field_simp
  calc |(tau n : ℝ)| * (n : ℝ) ^ (-6 : ℝ) * ‖V (6 + t * I) (2 * π * n / X)‖
      ≤ |(tau n : ℝ)| * (n : ℝ) ^ (-6 : ℝ) * (C₀ * (((1 + |t|) * X) ^ A / (n : ℝ) ^ A)) := by
        gcongr
    _ = C₀ * ((1 + |t|) * X) ^ A * |(tau n : ℝ)| * ((n : ℝ) ^ (-6 : ℝ) * (1 / (n : ℝ) ^ A)) := by
        ring
    _ = _ := by rw [hpow]; ring

/-- **Tail bound** for the AFE sums, uniform in `t`, `X`, `N`. -/
theorem tail_bound {A : ℝ} (hA : 3 / 4 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t X : ℝ) (N : ℕ), 0 < X → 1 ≤ N →
      Summable (afeTerm t X) ∧
      ‖∑' n, afeTerm t X n - ∑ n ∈ range N, afeTerm t X n‖ ≤
        C * ((1 + |t|) * X) ^ A * (N : ℝ) ^ (-(A - 3 / 4)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := V_decay (A := A) (by linarith)
  have hh : Summable fun n : ℕ => |(tau n : ℝ)| / (n : ℝ) ^ (27 / 4 : ℝ) :=
    RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by norm_num)
  set H : ℝ := ∑' n : ℕ, |(tau n : ℝ)| / (n : ℝ) ^ (27 / 4 : ℝ)
  have hH0 : 0 ≤ H := tsum_nonneg fun n => by positivity
  refine ⟨C₀ * H, by positivity, fun t X N hX hN => ?_⟩
  set K : ℝ := C₀ * ((1 + |t|) * X) ^ A
  have hK0 : 0 ≤ K := by positivity
  have hg : Summable fun n : ℕ => K * (|(tau n : ℝ)| / (n : ℝ) ^ (6 + A)) :=
    (RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by linarith)).mul_left K
  have hb := norm_afeTerm_le (by linarith) hC₀0 hC₀ t X hX
  have hs : Summable (afeTerm t X) := Summable.of_norm_bounded hg hb
  refine ⟨hs, ?_⟩
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : ∑' n, afeTerm t X n - ∑ n ∈ range N, afeTerm t X n =
      ∑' i, afeTerm t X (i + N) := by rw [← hsplit]; ring
  rw [htail]
  have hgN : Summable fun i : ℕ => K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (6 + A)) :=
    (summable_nat_add_iff N).2 hg
  have hhN : Summable fun i : ℕ => |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) :=
    (summable_nat_add_iff N).2 hh
  have h1 : ‖∑' i, afeTerm t X (i + N)‖ ≤
      ∑' i : ℕ, K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (6 + A)) :=
    tsum_of_norm_bounded hgN.hasSum fun i => hb (i + N)
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h2 : ∀ i : ℕ, K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (6 + A)) ≤
      K * (N : ℝ) ^ (-(A - 3 / 4)) *
        (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ)) := by
    intro i
    have hm : (N : ℝ) ≤ ((i + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N i
    have hm0 : (0:ℝ) < ((i + N : ℕ) : ℝ) := lt_of_lt_of_le hNpos hm
    have hsp : ((i + N : ℕ) : ℝ) ^ (6 + A) =
        ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) * ((i + N : ℕ) : ℝ) ^ (A - 3 / 4) := by
      rw [← Real.rpow_add hm0]; ring_nf
    have hmono : ((i + N : ℕ) : ℝ) ^ (-(A - 3 / 4)) ≤ (N : ℝ) ^ (-(A - 3 / 4)) :=
      Real.rpow_le_rpow_of_nonpos hNpos hm (by linarith)
    have e : |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (6 + A) =
        |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) *
          ((i + N : ℕ) : ℝ) ^ (-(A - 3 / 4)) := by
      rw [hsp, Real.rpow_neg hm0.le]; field_simp
    rw [e]
    have : 0 ≤ |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) := by positivity
    calc K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) *
          ((i + N : ℕ) : ℝ) ^ (-(A - 3 / 4)))
        ≤ K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) *
          (N : ℝ) ^ (-(A - 3 / 4))) := by gcongr
      _ = _ := by ring
  have h3 : ∑' i : ℕ, K * (|(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (6 + A)) ≤
      K * (N : ℝ) ^ (-(A - 3 / 4)) *
        ∑' i : ℕ, |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) := by
    rw [← tsum_mul_left]; exact Summable.tsum_le_tsum h2 hgN (hhN.mul_left _)
  have h4 : ∑' i : ℕ, |(tau (i + N) : ℝ)| / ((i + N : ℕ) : ℝ) ^ (27 / 4 : ℝ) ≤ H := by
    have := hh.sum_add_tsum_nat_add N
    have hnn : 0 ≤ ∑ i ∈ range N, |(tau i : ℝ)| / (i : ℝ) ^ (27 / 4 : ℝ) :=
      Finset.sum_nonneg fun i _ => by positivity
    simp only [H]; linarith
  have hKN : 0 ≤ K * (N : ℝ) ^ (-(A - 3 / 4)) := by positivity
  calc ‖∑' i, afeTerm t X (i + N)‖ ≤ _ := h1
    _ ≤ _ := h3
    _ ≤ K * (N : ℝ) ^ (-(A - 3 / 4)) * H := by gcongr
    _ = _ := by simp only [K]; ring

/-- the first AFE sum of length `N`. -/
noncomputable def S1 (t X : ℝ) (N : ℕ) : ℂ := ∑ n ∈ range N, afeTerm t X n

lemma afe_line_eq (t : ℝ) {X : ℝ} (hX : 0 < X) :
    tauL (6 + t * I) = ∑' n, afeTerm t X n + eps (6 + t * I) * ∑' n, afeTerm (-t) X⁻¹ n := by
  rw [tauL_afe_line t hX]
  unfold afeTerm
  congr 3; ext n
  rw [div_inv_eq_mul]

/-- **Truncated AFE with two lengths** (`X > 0` arbitrary): with
`S₁ = Σ_{n<N₁} τ(n) n^{−s} V_t(2πn/X)`, `S₂ = Σ_{n<N₂} τ(n) n^{−s̄} V_{−t}(2πnX)`,
`|L(6+it) − S₁ − ε(6+it) S₂| ≤ C_A [((1+|t|)X)^A N₁^{−(A−3/4)} + ((1+|t|)/X)^A N₂^{−(A−3/4)}]`. -/
theorem tauL_afe_truncated_unbalanced {A : ℝ} (hA : 3 / 4 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t X : ℝ) (N₁ N₂ : ℕ), 0 < X → 1 ≤ N₁ → 1 ≤ N₂ →
      ‖tauL (6 + t * I) - (S1 t X N₁ + eps (6 + t * I) * S1 (-t) X⁻¹ N₂)‖ ≤
        C * (((1 + |t|) * X) ^ A * (N₁ : ℝ) ^ (-(A - 3 / 4)) +
          ((1 + |t|) / X) ^ A * (N₂ : ℝ) ^ (-(A - 3 / 4))) := by
  obtain ⟨C, hC0, hC⟩ := tail_bound hA
  refine ⟨C, hC0, fun t X N₁ N₂ hX h1 h2 => ?_⟩
  obtain ⟨-, hb1⟩ := hC t X N₁ hX h1
  obtain ⟨-, hb2⟩ := hC (-t) X⁻¹ N₂ (inv_pos.2 hX) h2
  rw [abs_neg, ← div_eq_mul_inv] at hb2
  rw [afe_line_eq t hX]
  unfold S1
  have e : ∑' n, afeTerm t X n + eps (6 + t * I) * ∑' n, afeTerm (-t) X⁻¹ n -
      (∑ n ∈ range N₁, afeTerm t X n + eps (6 + t * I) * ∑ n ∈ range N₂, afeTerm (-t) X⁻¹ n) =
      (∑' n, afeTerm t X n - ∑ n ∈ range N₁, afeTerm t X n) +
        eps (6 + t * I) * (∑' n, afeTerm (-t) X⁻¹ n - ∑ n ∈ range N₂, afeTerm (-t) X⁻¹ n) := by
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_eps_line, one_mul]
  calc _ ≤ C * ((1 + |t|) * X) ^ A * (N₁ : ℝ) ^ (-(A - 3 / 4)) +
        C * ((1 + |t|) / X) ^ A * (N₂ : ℝ) ^ (-(A - 3 / 4)) := add_le_add hb1 hb2
    _ = _ := by ring

/-- **Truncated symmetric AFE** (`X = 1`): for `η > 0`, `B ≥ 0` there is `C` with
`|L(6+it) − S₁ − ε(6+it) S₂| ≤ C (1+|t|)^{−B}` whenever `N ≥ (1+|t|)^{1+η}`, where
`S₁ = Σ_{n<N} τ(n) n^{−6−it} V_t(2πn)` and `S₂ = Σ_{n<N} τ(n) n^{−6+it} V_{−t}(2πn)`. -/
theorem tauL_afe_truncated {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (N : ℕ), (1 + |t|) ^ (1 + η) ≤ N →
      ‖tauL (6 + t * I) - (S1 t 1 N + eps (6 + t * I) * S1 (-t) 1 N)‖ ≤
        C * (1 + |t|) ^ (-B) := by
  set A : ℝ := (B + 3 / 4 * (1 + η)) / η + 3 / 4 with hAdef
  have hA0 : 0 ≤ (B + 3 / 4 * (1 + η)) / η := by positivity
  have hA : 3 / 4 ≤ A := by linarith
  obtain ⟨C, hC0, hC⟩ := tauL_afe_truncated_unbalanced hA
  refine ⟨2 * C, by positivity, fun t N hN => ?_⟩
  have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h1t0 : 0 < 1 + |t| := by linarith
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN1 : 1 ≤ N := by
    have : (1:ℝ) ≤ (1 + |t|) ^ (1 + η) := Real.one_le_rpow h1t (by linarith)
    exact_mod_cast this.trans hN
  have h := hC t 1 N N one_pos hN1 hN1
  rw [inv_one] at h
  simp only [mul_one, div_one] at h
  refine h.trans ?_
  have hkey : (1 + |t|) ^ A * (N : ℝ) ^ (-(A - 3 / 4)) ≤ (1 + |t|) ^ (-B) := by
    have hm : (N : ℝ) ^ (-(A - 3 / 4)) ≤ ((1 + |t|) ^ (1 + η)) ^ (-(A - 3 / 4)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hN (by linarith)
    rw [← Real.rpow_mul h1t0.le] at hm
    calc (1 + |t|) ^ A * (N : ℝ) ^ (-(A - 3 / 4))
        ≤ (1 + |t|) ^ A * (1 + |t|) ^ ((1 + η) * -(A - 3 / 4)) := by gcongr
      _ = (1 + |t|) ^ (A + (1 + η) * -(A - 3 / 4)) := by rw [← Real.rpow_add h1t0]
      _ ≤ (1 + |t|) ^ (-B) := by
          apply Real.rpow_le_rpow_of_exponent_le h1t
          have : η * ((B + 3 / 4 * (1 + η)) / η) = B + 3 / 4 * (1 + η) := by
            field_simp
          nlinarith
  calc C * ((1 + |t|) ^ A * (N : ℝ) ^ (-(A - 3 / 4)) + (1 + |t|) ^ A * (N : ℝ) ^ (-(A - 3 / 4)))
      ≤ C * ((1 + |t|) ^ (-B) + (1 + |t|) ^ (-B)) := by gcongr
    _ = _ := by ring

/-- **Pointwise consequence**: `|L(6+it)| ≤ |S₁(N)| + |S₂(N)| + C (1+|t|)^{−B}` for
`N ≥ (1+|t|)^{1+η}` (`|ε| = 1`). -/
theorem norm_tauL_le_afe {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (N : ℕ), (1 + |t|) ^ (1 + η) ≤ N →
      ‖tauL (6 + t * I)‖ ≤ ‖S1 t 1 N‖ + ‖S1 (-t) 1 N‖ + C * (1 + |t|) ^ (-B) := by
  obtain ⟨C, hC0, hC⟩ := tauL_afe_truncated hη hB
  refine ⟨C, hC0, fun t N hN => ?_⟩
  have h := hC t N hN
  have h2 := norm_le_norm_add_norm_sub' (tauL (6 + t * I)) (S1 t 1 N + eps (6 + t * I) * S1 (-t) 1 N)
  have h3 := norm_add_le (S1 t 1 N) (eps (6 + t * I) * S1 (-t) 1 N)
  rw [norm_mul, norm_eps_line, one_mul] at h3
  linarith

end RamanujanTau.HeckeAFE
