/-
# The prime number theorem for `τ`, conditional on Wiener–Ikehara (and Deligne)

`WienerIkeharaHyp` is a pure analysis statement (no number theory): the Wiener–Ikehara
Tauberian theorem in the form proved in PrimeNumberTheoremAnd (`WienerIkeharaTheorem''`,
file `PrimeNumberTheoremAnd/Wiener.lean`, on a different toolchain).

Apply it to the nonnegative sequences (Deligne: `|Λ_Δ(n)| ≤ 2Λ(n)`)

  `a±(n) = 2Λ(n) ± Λ_Δ(n)`,  `∑ a±(n) n^{−s} = 2/(s−1) + [2(−ζ'/ζ − 1/(s−1)) ± (−L'/L)]`,

where the bracket is continuous on `Re s ≥ 1` (Mathlib's `continuousOn_LFunctionResidueClassAux`
for `ζ`; `continuousOn_negLogDeriv`, i.e. edge non-vanishing, for `L`).  Both averages tend
to `2`; subtracting gives `∑_{n<N} Λ_Δ(n) = o(N)`.  The prime powers contribute
`≤ 2(ψ − θ)(N) ≤ 4√N log N` (Mathlib's Chebyshev bound).  Result:

  `∑_{p<N} τ(p) p^{−11/2} log p = o(N)`.
-/
import RamanujanTau.TauPNT.Signs
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL
open ArithmeticFunction (vonMangoldt)

/-- **Wiener–Ikehara Tauberian theorem** (named hypothesis; pure analysis).
If `f ≥ 0`, `∑ f(n) n^{−σ}` converges for `σ > 1`, and `∑ f(n)n^{−s} − A/(s−1)` extends
continuously to `Re s ≥ 1`, then `(∑_{n<N} f(n))/N → A`.
Proved in PrimeNumberTheoremAnd as `WienerIkeharaTheorem''`. -/
def WienerIkeharaHyp : Prop :=
  ∀ (f : ℕ → ℝ) (A : ℝ) (G : ℂ → ℂ), (∀ n, 0 ≤ f n) →
    (∀ σ' : ℝ, 1 < σ' → LSeriesSummable (fun n => (f n : ℂ)) σ') →
    ContinuousOn G {s | 1 ≤ s.re} →
    Set.EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - A / (s - 1)) {s | 1 < s.re} →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / N) atTop (𝓝 A)

/-- `−ζ'/ζ(s) − 1/(s−1)`, continuous on `Re s ≥ 1` (Mathlib, `q = 1`). -/
noncomputable abbrev zetaAux : ℂ → ℂ := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (q := 1) 1

lemma residueClass_one : ArithmeticFunction.vonMangoldt.residueClass (q := 1) 1 = fun n => vonMangoldt n := by
  funext n
  simp only [ArithmeticFunction.vonMangoldt.residueClass]
  rw [Set.indicator_of_mem]
  exact Subsingleton.elim _ _

lemma zetaAux_eqOn : Set.EqOn zetaAux
    (fun s => LSeries (fun n => (vonMangoldt n : ℂ)) s - 1 / (s - 1)) {s | 1 < s.re} := by
  intro s hs
  have h := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) (a := 1) isUnit_one hs
  unfold zetaAux
  rw [h, residueClass_one]
  simp

lemma zetaAux_continuousOn : ContinuousOn zetaAux {s | 1 ≤ s.re} :=
  ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (q := 1) 1

section Deligne

variable [DeligneBound]

/-- `|Λ_Δ(n)| ≤ 2Λ(n)` (Deligne). -/
lemma abs_vM_le (n : ℕ) : |vM n| ≤ 2 * vonMangoldt n := by
  by_cases h : IsPrimePow n
  · have hp : n.minFac.Prime := Nat.minFac_prime h.ne_one
    rw [vM, if_pos h, ArithmeticFunction.vonMangoldt_apply, if_pos h, abs_mul,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact mul_le_mul_of_nonneg_right (abs_AA_le_two hp _)
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  · rw [vM_of_not h]; simp [ArithmeticFunction.vonMangoldt_apply, h]

/-- `a±(n) = 2Λ(n) ± Λ_Δ(n) ≥ 0`. -/
noncomputable def aPM (ε : ℝ) (n : ℕ) : ℝ := 2 * vonMangoldt n + ε * vM n

omit [DeligneBound] in
lemma aPM_coe (ε : ℝ) :
    (fun n => (aPM ε n : ℂ)) = (2 : ℂ) • (fun n => (vonMangoldt n : ℂ)) +
      (ε : ℂ) • (fun n => (vM n : ℂ)) := by
  funext n; simp [aPM]

lemma aPM_nonneg {ε : ℝ} (hε : |ε| = 1) (n : ℕ) : 0 ≤ aPM ε n := by
  have h := abs_vM_le n
  have : |ε * vM n| ≤ 2 * vonMangoldt n := by rw [abs_mul, hε, one_mul]; exact h
  have := neg_abs_le (ε * vM n)
  simp only [aPM]; linarith

omit [DeligneBound] in
lemma aPM_summable (ε : ℝ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (aPM ε n : ℂ)) s := by
  rw [aPM_coe]
  exact ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul _).add
    ((LSeriesSummable_vM hs).smul _)

omit [DeligneBound] in
lemma aPM_eqOn (ε : ℝ) : Set.EqOn (fun s => 2 * zetaAux s + ε * negLogDeriv s)
    (fun s => LSeries (fun n => (aPM ε n : ℂ)) s - 2 / (s - 1)) {s | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  simp only
  rw [zetaAux_eqOn hs, negLogDeriv_eq_LSeries hs', aPM_coe,
    LSeries_add ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs').smul _)
      ((LSeriesSummable_vM hs').smul _), LSeries_smul, LSeries_smul]
  ring

omit [DeligneBound] in
lemma aPM_continuousOn (ε : ℝ) :
    ContinuousOn (fun s => 2 * zetaAux s + ε * negLogDeriv s) {s | 1 ≤ s.re} :=
  (continuousOn_const.mul zetaAux_continuousOn).add (continuousOn_const.mul continuousOn_negLogDeriv)

/-- **`∑_{n<N} Λ_Δ(n) = o(N)`** (Wiener–Ikehara + Deligne). -/
theorem psiDelta_littleO (hWI : WienerIkeharaHyp) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, vM n) / N) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, aPM ε n) / N) atTop (𝓝 2) := fun ε hε =>
    hWI (aPM ε) 2 _ (aPM_nonneg hε) (fun σ' hσ' => aPM_summable ε (by simpa using hσ'))
      (aPM_continuousOn ε) (aPM_eqOn ε)
  have hp := key 1 (by norm_num)
  have hm := key (-1) (by norm_num)
  have := (hp.sub hm).div_const 2
  simp only [sub_self, zero_div] at this
  refine this.congr fun N => ?_
  simp only [aPM]
  have e : ∑ x ∈ Finset.range N, ((2 * vonMangoldt x + 1 * vM x) - (2 * vonMangoldt x + -1 * vM x)) =
      2 * ∑ x ∈ Finset.range N, vM x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [← sub_div, ← Finset.sum_sub_distrib, e]
  ring

/-- The prime powers `p^k`, `k ≥ 2`, contribute `≤ 4√N log N`. -/
lemma nonprime_part_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Finset.range N with ¬ n.Prime, vM n| ≤ 4 * Real.sqrt N * Real.log N := by
  have h1 : |∑ n ∈ Finset.range N with ¬ n.Prime, vM n| ≤
      ∑ n ∈ Finset.range N with ¬ n.Prime, 2 * vonMangoldt n :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => abs_vM_le n)
  have h2 : ∑ n ∈ Finset.range N with ¬ n.Prime, vonMangoldt n ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ with ¬ n.Prime, vonMangoldt n := by
    rw [Nat.floor_natCast]
    have hsub : (Finset.range N).filter (fun n => ¬ n.Prime) ⊆
        insert 0 ((Finset.Ioc 0 N).filter (fun n => ¬ n.Prime)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpos, hn.1.le⟩, hn.2⟩)
    calc ∑ n ∈ Finset.range N with ¬ n.Prime, vonMangoldt n
        ≤ ∑ n ∈ insert 0 ((Finset.Ioc 0 N).filter (fun n => ¬ n.Prime)), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      _ = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ n.Prime), vonMangoldt n := by
          rw [Finset.sum_insert (by simp)]; simp
  have h3 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime] at h3
  have h4 := le_abs_self (∑ n ∈ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ with ¬ n.Prime, vonMangoldt n)
  rw [← Finset.mul_sum] at h1
  linarith

omit [DeligneBound] in
lemma sqrt_log_littleO :
    Tendsto (fun N : ℕ => 4 * Real.sqrt N * Real.log N / N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  have h' := (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  rw [mul_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [Real.sqrt_eq_rpow]
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  conv_rhs => arg 2; rw [← hsq]
  field_simp

/-- **The prime number theorem for `τ`** (conditional on `WienerIkeharaHyp` and `DeligneBound`):
`∑_{p<N} τ(p) p^{−11/2} log p = o(N)`. -/
theorem tau_PNT (hWI : WienerIkeharaHyp) :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, lam p * Real.log p) / N)
      atTop (𝓝 0) := by
  have h1 := psiDelta_littleO hWI
  have hsplit : ∀ N : ℕ, ∑ p ∈ Finset.range N with p.Prime, lam p * Real.log p =
      ∑ n ∈ Finset.range N, vM n - ∑ n ∈ Finset.range N with ¬ n.Prime, vM n := by
    intro N
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) Nat.Prime (fun n => vM n)]
    simp only [add_sub_cancel_right]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact (vM_prime (Finset.mem_filter.mp hp).2).symm
  have h2 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N with ¬ n.Prime, vM n) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ sqrt_log_littleO
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (nonprime_part_le N hN) (by positivity)
  have := h1.sub h2
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  rw [hsplit, sub_div]

end Deligne

end RamanujanTau.TauPNT
