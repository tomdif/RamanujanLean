/-
# Positive proportion of each sign, from a Ramanujan bound up to `N`

All results here are unconditional theorems; the Ramanujan-type input is a *finitary* hypothesis
on the primes below `N` (checkable numerically for any given `N`), or, for the last corollaries,
the repo's `[DeligneBound]` class.

* `S1_small`: `∑_{p<N} λ(p) log p = o(N)` (from `TauPNTError.tau_PNT_error_uncond`).
* `signed_mass_of_bound_upto`: for every `M > 0` there is `N₀` such that for `N ≥ N₀`, if
  `|λ(p)| ≤ M` for all primes `p < N`, then `∑_{p<N, ελ(p)>0} log p ≥ N/(3M²)`.
* `tau_pos_mass_of_bound_upto`, `tau_neg_mass_of_bound_upto`: the same for `τ(p) > 0`, `τ(p) < 0`.
* `tau_pos_mass_deligne`, `tau_neg_mass_deligne` (`[DeligneBound]`): `∑_{p<N, ±τ(p)>0} log p ≥ N/12`
  for `N ≥ N₀`; `tau_pos_count_deligne`, `tau_neg_count_deligne`: `#{p<N : ±τ(p) > 0} · log N ≥ N/12`.

Proof.  Pointwise, `|λ| ≤ M` gives `λ²/M + ελ ≤ 2M·[ελ > 0]`.  Multiply by `log p`, sum over
`p < N`, and use `∑ λ² log p ≥ 5N/6` (`rs_prime_PNT`) and `|∑ λ log p| ≤ N/(6M)` (`S1_small`).
-/
import RamanujanTau.TauSignsQuant.Count
import RamanujanTau.TauPNTError.Uncond
import RamanujanTau.TauPNTUncond.RSPNT

set_option autoImplicit false

namespace RamanujanTau.TauSignsQuant

open Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT RamanujanTau.TauPNTUncond

/-- **`∑_{p<N} λ(p) log p = o(N)`**, unconditionally. -/
lemma S1_small {η : ℝ} (hη : 0 < η) : ∀ᶠ N : ℕ in atTop,
    |∑ p ∈ Finset.range N with p.Prime, lam p * Real.log p| ≤ η * N := by
  obtain ⟨b, hb, -, K, hK, hE⟩ := TauPNTError.tau_PNT_error_uncond
  have ht : Tendsto (fun M : ℕ => K * Real.exp (-b * Real.sqrt (Real.log M))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => Real.sqrt (Real.log M)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 := (Real.tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg (neg_lt_zero.mpr hb)))
    simpa using h2.const_mul K
  have hev := (tendsto_order.1 ht).2 η hη
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨M0 + 4, fun N hN => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := hE M (by omega)
  have hm := (hM0 M (by omega)).le
  have hM0' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMN : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
  calc |∑ p ∈ Finset.range (M + 1) with p.Prime, lam p * Real.log p|
      ≤ K * M * Real.exp (-b * Real.sqrt (Real.log M)) := h
    _ = (K * Real.exp (-b * Real.sqrt (Real.log M))) * M := by ring
    _ ≤ η * M := mul_le_mul_of_nonneg_right hm hM0'
    _ ≤ η * ((M + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hMN hη.le

lemma pointwise (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {M l L : ℝ} (hM : 0 < M) (hl : |l| ≤ M)
    (hL : 0 ≤ L) :
    (l ^ 2 * L) / M + ε * (l * L) ≤ 2 * M * (if 0 < ε * l then L else 0) := by
  have hεl : |ε * l| = |l| := by rcases hε with rfl | rfl <;> simp
  have hsq : l ^ 2 / M ≤ |l| := by
    rw [div_le_iff₀ hM, ← sq_abs]; nlinarith [abs_nonneg l]
  have e : (l ^ 2 * L) / M + ε * (l * L) = (l ^ 2 / M + ε * l) * L := by ring
  rw [e]
  split_ifs with h
  · have : |l| = ε * l := by rw [← hεl, abs_of_pos h]
    have : l ^ 2 / M + ε * l ≤ 2 * M := by linarith
    nlinarith
  · push Not at h
    have : |l| = -(ε * l) := by rw [← hεl, abs_of_nonpos h]
    have : l ^ 2 / M + ε * l ≤ 0 := by linarith
    nlinarith

/-- **Positive proportion of `ελ(p) > 0`, from a Ramanujan bound up to `N`.** -/
theorem signed_mass_of_bound_upto (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {M : ℝ} (hM : 0 < M) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (∀ p : ℕ, p < N → p.Prime → |lam p| ≤ M) →
      (N : ℝ) / (3 * M ^ 2) ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ 0 < ε * lam p), Real.log p := by
  have h2 := (tendsto_order.1 rs_prime_PNT).1 (5 / 6) (by norm_num)
  have h1 := S1_small (η := 1 / (6 * M)) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨N0 + 1, fun N hN hR => ?_⟩
  obtain ⟨hS1, hS2⟩ := hN0 N (by omega)
  have hN0' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [lt_div_iff₀ hN0'] at hS2
  set s := (Finset.range N).filter Nat.Prime
  set S2 := ∑ p ∈ s, lam p ^ 2 * Real.log p
  set S1 := ∑ p ∈ s, lam p * Real.log p
  set T := ∑ p ∈ s, (if 0 < ε * lam p then Real.log p else 0)
  have hT : ∑ p ∈ Finset.range N with (p.Prime ∧ 0 < ε * lam p), Real.log p = T := by
    rw [← Finset.filter_filter, Finset.sum_filter]
  rw [hT]
  have hsum : S2 / M + ε * S1 ≤ 2 * M * T := by
    have : ∑ p ∈ s, ((lam p ^ 2 * Real.log p) / M + ε * (lam p * Real.log p)) ≤
        ∑ p ∈ s, 2 * M * (if 0 < ε * lam p then Real.log p else 0) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp' := Finset.mem_filter.mp hp
      exact pointwise ε hε hM (hR p (Finset.mem_range.mp hp'.1) hp'.2)
        (Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le))
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum] at this
    exact this
  have hεS : -(1 / (6 * M) * N) ≤ ε * S1 := by
    have : |ε * S1| = |S1| := by rcases hε with rfl | rfl <;> simp
    have := neg_abs_le (ε * S1)
    linarith
  have hS2M : 5 / 6 * N / M ≤ S2 / M := div_le_div_of_nonneg_right (by linarith) hM.le
  have key : (2 / 3) * N / M ≤ 2 * M * T := by
    have e : (2 / 3) * (N : ℝ) / M = 5 / 6 * N / M - 1 / (6 * M) * N := by field_simp; ring
    linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hM] at key
  nlinarith

lemma neg_one_mul_pos_iff {p : ℕ} (hp : p.Prime) : 0 < -1 * lam p ↔ tau p < 0 := by
  rw [← lam_neg_iff hp]; constructor <;> intro h <;> linarith

lemma one_mul_pos_iff {p : ℕ} (hp : p.Prime) : 0 < 1 * lam p ↔ 0 < tau p := by
  rw [one_mul, lam_pos_iff hp]

lemma filter_congr_pos (N : ℕ) :
    (Finset.range N).filter (fun p => p.Prime ∧ 0 < 1 * lam p) =
      (Finset.range N).filter (fun p => p.Prime ∧ 0 < tau p) :=
  Finset.filter_congr fun p _ => by
    constructor
    · rintro ⟨hp, h⟩; exact ⟨hp, (one_mul_pos_iff hp).mp h⟩
    · rintro ⟨hp, h⟩; exact ⟨hp, (one_mul_pos_iff hp).mpr h⟩

lemma filter_congr_neg (N : ℕ) :
    (Finset.range N).filter (fun p => p.Prime ∧ 0 < -1 * lam p) =
      (Finset.range N).filter (fun p => p.Prime ∧ tau p < 0) :=
  Finset.filter_congr fun p _ => by
    constructor
    · rintro ⟨hp, h⟩; exact ⟨hp, (neg_one_mul_pos_iff hp).mp h⟩
    · rintro ⟨hp, h⟩; exact ⟨hp, (neg_one_mul_pos_iff hp).mpr h⟩

/-- **`τ(p) > 0` for a positive log-proportion of `p < N`**, if `|τ(p)| ≤ M p^{11/2}` for `p < N`. -/
theorem tau_pos_mass_of_bound_upto {M : ℝ} (hM : 0 < M) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (∀ p : ℕ, p < N → p.Prime → |lam p| ≤ M) →
      (N : ℝ) / (3 * M ^ 2) ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ 0 < tau p), Real.log p := by
  obtain ⟨N0, h⟩ := signed_mass_of_bound_upto 1 (Or.inl rfl) hM
  exact ⟨N0, fun N hN hR => by rw [← filter_congr_pos]; exact h N hN hR⟩

/-- **`τ(p) < 0` for a positive log-proportion of `p < N`**, if `|τ(p)| ≤ M p^{11/2}` for `p < N`. -/
theorem tau_neg_mass_of_bound_upto {M : ℝ} (hM : 0 < M) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (∀ p : ℕ, p < N → p.Prime → |lam p| ≤ M) →
      (N : ℝ) / (3 * M ^ 2) ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ tau p < 0), Real.log p := by
  obtain ⟨N0, h⟩ := signed_mass_of_bound_upto (-1) (Or.inr rfl) hM
  exact ⟨N0, fun N hN hR => by rw [← filter_congr_neg]; exact h N hN hR⟩

lemma log_sum_le_card {s : Finset ℕ} {N : ℕ} (hs : ∀ p ∈ s, p < N ∧ p.Prime) :
    ∑ p ∈ s, Real.log p ≤ s.card * Real.log N := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  have h := hs p hp
  exact Real.log_le_log (by exact_mod_cast h.2.pos) (by exact_mod_cast h.1.le)

section Deligne

variable [DeligneBound]

/-- **Deligne ⟹ `∑_{p<N, τ(p)>0} log p ≥ N/12`** for large `N`. -/
theorem tau_pos_mass_deligne : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / 12 ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ 0 < tau p), Real.log p := by
  obtain ⟨N0, h⟩ := tau_pos_mass_of_bound_upto (M := 2) (by norm_num)
  exact ⟨N0, fun N hN => by
    have := h N hN fun p _ hp => abs_lam_le_two hp
    norm_num at this ⊢; linarith⟩

/-- **Deligne ⟹ `∑_{p<N, τ(p)<0} log p ≥ N/12`** for large `N`. -/
theorem tau_neg_mass_deligne : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / 12 ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ tau p < 0), Real.log p := by
  obtain ⟨N0, h⟩ := tau_neg_mass_of_bound_upto (M := 2) (by norm_num)
  exact ⟨N0, fun N hN => by
    have := h N hN fun p _ hp => abs_lam_le_two hp
    norm_num at this ⊢; linarith⟩

/-- **Deligne ⟹ `#{p < N : τ(p) > 0} · log N ≥ N/12`** for large `N`. -/
theorem tau_pos_count_deligne : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / 12 ≤ ((Finset.range N).filter (fun p => p.Prime ∧ 0 < tau p)).card * Real.log N := by
  obtain ⟨N0, h⟩ := tau_pos_mass_deligne
  exact ⟨N0, fun N hN => (h N hN).trans (log_sum_le_card fun p hp => by
    have := Finset.mem_filter.mp hp; exact ⟨Finset.mem_range.mp this.1, this.2.1⟩)⟩

/-- **Deligne ⟹ `#{p < N : τ(p) < 0} · log N ≥ N/12`** for large `N`. -/
theorem tau_neg_count_deligne : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / 12 ≤ ((Finset.range N).filter (fun p => p.Prime ∧ tau p < 0)).card * Real.log N := by
  obtain ⟨N0, h⟩ := tau_neg_mass_deligne
  exact ⟨N0, fun N hN => (h N hN).trans (log_sum_le_card fun p hp => by
    have := Finset.mem_filter.mp hp; exact ⟨Finset.mem_range.mp this.1, this.2.1⟩)⟩

end Deligne

end RamanujanTau.TauSignsQuant
