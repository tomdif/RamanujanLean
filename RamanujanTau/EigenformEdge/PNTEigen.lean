/-
# Smoothed PNT, sign changes and PNT for a normalized eigenform `f`

Specializes `PNT.lean` / `PNTSigns.lean` to `eigenData f hf`.  Hypotheses:

* `hf : IsNormalizedEigenform f` (true structural properties of eigenforms);
* `h0 : fL f ((k+1)/2) ≠ 0` — the real edge value (needed for continuity of `−L'/L` at the
  real point; supplied for `Δ` by `fL_edge_real_ne_zero_of_imagAxis_nonneg`);
* `[DeligneBoundF f]` — Deligne's bound `a_f(p)² ≤ 4p^{k−1}` (named class, never an axiom),
  only for the sign changes and the PNT.

Wiener–Ikehara is the proved `WienerIkehara.wienerIkehara`, not a hypothesis.
-/
import RamanujanTau.EigenformEdge.PNTSigns
import RamanujanTau.EigenformEdge.RealPoint

set_option autoImplicit false

namespace RamanujanTau.EigenformEdge

open Complex Filter Topology
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- **Deligne's bound for `f`** (Deligne 1974; named hypothesis, never an axiom):
`a_f(p)² ≤ 4 p^{k−1}`, i.e. `|a_f(p)| ≤ 2p^{(k−1)/2}`. -/
class DeligneBoundF (f : CuspForm 𝒮ℒ (k : ℤ)) : Prop where
  bound : ∀ p : ℕ, p.Prime → (coef f p).re ^ 2 ≤ 4 * (p : ℝ) ^ (k - 1)

/-- The repo's `DeligneBound` (for `τ`) gives `DeligneBoundF Δ`. -/
instance [DeligneBound] : DeligneBoundF (k := 12) DeltaF where
  bound p hp := by
    rw [coef_discriminant]
    have h := DeligneBound.bound p hp
    have h' : ((tau p : ℤ) : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 11 := by exact_mod_cast h
    simpa [tauC] using h'

lemma nrm_eq_rpow (hk : 1 ≤ k) (n : ℕ) : nrm k n = (n : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  rw [nrm, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; push_cast [Nat.cast_sub hk]; ring

lemma nlam_pos_iff (f : CuspForm 𝒮ℒ (k : ℤ)) (p : ℕ) (hp : p ≠ 0) :
    0 < nlam f p ↔ 0 < (coef f p).re := by
  rw [nlam]; exact div_pos_iff_of_pos_right (nrm_pos k hp)

lemma nlam_neg_iff (f : CuspForm 𝒮ℒ (k : ℤ)) (p : ℕ) (hp : p ≠ 0) :
    nlam f p < 0 ↔ (coef f p).re < 0 := by
  have hpos := nrm_pos k hp
  rw [nlam]
  constructor
  · intro h; by_contra hc; push Not at hc; exact absurd h (not_lt.mpr (div_nonneg hc hpos.le))
  · intro h; exact div_neg_of_neg_of_pos h hpos

section

variable {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f)
  (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0)
include hf h0

lemma realEdge_eigen : @RealEdge (eigenData f hf) := by
  letI := eigenData f hf
  refine ⟨?_⟩
  change Lf f 1 ≠ 0
  rwa [Lf, show (1 : ℂ) + ((k : ℂ) - 1) / 2 = ((k : ℂ) + 1) / 2 by ring]

/-- **Smoothed PNT for `f`** (no Deligne): `∑_p λ_f(p) log p · p^{−σ}` has a finite limit as
`σ → 1⁺`, where `λ_f(p) = a_f(p)/p^{(k−1)/2}` (`nlam`). -/
theorem eigen_PNT_smoothed : ∃ C : ℝ,
    Tendsto (fun σ : ℝ => ∑' p : Nat.Primes, nlam f p * Real.log p * (p : ℝ) ^ (-σ))
      (𝓝[>] 1) (𝓝 C) := by
  letI := eigenData f hf
  haveI := realEdge_eigen hf h0
  exact ⟨_, primeSum_tendsto⟩

/-- `−L'/L(f, s + (k−1)/2)` is continuous on `Re s ≥ 1` and equals `∑ Λ_f(n) n^{−s}` there. -/
theorem eigen_negLogDeriv_continuousOn :
    ContinuousOn (fun s => -deriv (Lf f) s / Lf f s) {s | 1 ≤ s.re} := by
  letI := eigenData f hf
  haveI := realEdge_eigen hf h0
  exact continuousOn_negLogDeriv

variable [DeligneBoundF f]

lemma deligneData_eigen : @DeligneData (eigenData f hf) := by
  letI := eigenData f hf
  refine ⟨fun p hp => ?_⟩
  change nlam f p ^ 2 ≤ 4
  have hpos := nrm_pos k hp.ne_zero
  rw [nlam, div_pow, nrm_sq, div_le_iff₀ (pow_pos (by exact_mod_cast hp.pos) _)]
  exact DeligneBoundF.bound p hp

/-- **Sign changes of `a_f(p)` over primes** (Deligne for `f`). -/
theorem eigen_prime_sign_changes :
    (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ 0 < (coef f p).re) ∧
      (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ (coef f p).re < 0) := by
  letI := eigenData f hf
  haveI := realEdge_eigen hf h0
  haveI := deligneData_eigen hf h0
  obtain ⟨h1, h2⟩ := lam_prime_sign_changes
  refine ⟨fun N => ?_, fun N => ?_⟩
  · obtain ⟨p, hN, hp, hpos⟩ := h1 N
    exact ⟨p, hN, hp, (nlam_pos_iff f p hp.ne_zero).mp hpos⟩
  · obtain ⟨p, hN, hp, hneg⟩ := h2 N
    exact ⟨p, hN, hp, (nlam_neg_iff f p hp.ne_zero).mp hneg⟩

/-- **PNT for `f`, normalized**: `∑_{p<N} λ_f(p) log p = o(N)`. -/
theorem eigen_PNT_lam :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, nlam f p * Real.log p) / N)
      atTop (𝓝 0) := by
  letI := eigenData f hf
  haveI := realEdge_eigen hf h0
  haveI := deligneData_eigen hf h0
  exact lam_PNT

/-- **PNT for `f`**: `∑_{p<N} a_f(p) log p = o(N^{(k+1)/2})`. -/
theorem eigen_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, (coef f p).re * Real.log p) /
      (N : ℝ) ^ (((k : ℝ) + 1) / 2)) atTop (𝓝 0) := by
  letI := eigenData f hf
  have hk := hf.one_le
  have hk12 := hf.twelve_le
  set r : ℝ := ((k : ℝ) - 1) / 2
  have hr : 0 < r := by
    have : (12 : ℝ) ≤ k := by exact_mod_cast hk12
    simp only [r]; linarith
  set a : ℕ → ℝ := fun n => if n.Prime then nlam f n * Real.log n else 0
  have ha : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 0) := by
    refine (eigen_PNT_lam hf h0).congr fun N => ?_
    simp only [a]; rw [Finset.sum_filter]
  have hw := weighted_littleO hr ha
  have e : r + 1 = ((k : ℝ) + 1) / 2 := by simp only [r]; ring
  rw [e] at hw
  refine hw.congr fun N => ?_
  simp only [a]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [nlam, ← nrm_eq_rpow hk]
    have := (nrm_pos k h.ne_zero).ne'
    field_simp
  · simp

end

/-! ## `Δ`: the τ results recovered -/

/-- The real edge value for `Δ`. -/
theorem fL_discriminant_edge_real : fL (k := 12) DeltaF ((((12 : ℕ) : ℂ) + 1) / 2) ≠ 0 :=
  fL_edge_real_ne_zero_of_imagAxis_nonneg isNormalizedEigenform_discriminant
    discriminant_imagAxis_nonneg

/-- **`∑_{p<N} τ(p) log p = o(N^{13/2})`**, recovered from `eigen_PNT` (Deligne only). -/
theorem tau_PNT_recovered [DeligneBound] :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p) /
      (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0) := by
  have h := eigen_PNT isNormalizedEigenform_discriminant fL_discriminant_edge_real
  have e : (((12 : ℕ) : ℝ) + 1) / 2 = 13 / 2 := by norm_num
  rw [e] at h
  refine h.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coef_discriminant]; simp [tauC]

end RamanujanTau.EigenformEdge
