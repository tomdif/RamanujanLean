/-
# Smoothed PNT for `τ` (unconditional): `∑_p λ(p) log p · p^{−σ}` has a finite limit as `σ → 1⁺`

`∑_n Λ_Δ(n) n^{−σ} = −L'/L(σ) → −L'/L(1)` (continuity, `L(1) ≠ 0`), and the prime-power tail
`T(σ) = ∑_{p, k ≥ 2} Λ_Δ(p^k) p^{−kσ}` is dominated uniformly on `σ ≥ 1`:

* `k = 2`: `|A_2| = |λ² − 2| ≤ λ² + 2`, and `∑_p λ(p)² p^{−7/4} < ∞` (Rankin–Selberg, `rs_summable`);
* `k ≥ 3`: `|A_k| ≤ 2‖α‖^k ≤ 2p^{k/2}` (Satake bound `‖α‖² ≤ p`, no Deligne).

Hence (dominated convergence) the prime sum itself converges to `−L'/L(1) − T(1)`.
In contrast `∑_p log p · p^{−σ} ∼ 1/(σ−1)`: the `λ(p)` have mean zero in the smoothed sense.
-/
import RamanujanTau.TauPNT.LogDeriv

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

/-- The smoothed prime sum `∑_p λ(p) log p · p^{−σ}`. -/
noncomputable def primeSum (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, lam p * Real.log p * (p : ℝ) ^ (-σ)

/-- The map `(p, k) ↦ p^{k+2}`. -/
def ppow2 (q : Nat.Primes × ℕ) : ℕ := (q.1 : ℕ) ^ (q.2 + 2)

lemma ppow2_injective : Function.Injective ppow2 := by
  have h : ppow2 = ppow ∘ fun q : Nat.Primes × ℕ => (q.1, q.2 + 1) := by
    funext q; simp [ppow2, ppow]
  rw [h]
  refine ppow_injective.comp fun a b hab => ?_
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.1 (by omega)

/-- The ratio `r = 2^{−1/2}`. -/
noncomputable def rr2 : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))

lemma rr2_pos : 0 < rr2 := Real.rpow_pos_of_pos (by norm_num) _

lemma rr2_lt_one : rr2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The dominating function for the tail. -/
noncomputable def Mb (q : Nat.Primes × ℕ) : ℝ :=
  (if q.2 = 0 then 4 * (lam q.1 ^ 2 + 2) * (q.1 : ℝ) ^ (-(7 / 4 : ℝ)) else 0) +
    (8 / rr2) * (q.1 : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ q.2

lemma summable_lam_sq {a : ℝ} (ha : 1 < a) :
    Summable fun p : Nat.Primes => lam p ^ 2 * (p : ℝ) ^ (-a) := by
  have h := (rs_summable (s := (a : ℂ)) (by simpa using ha)).norm.comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  refine h.congr fun p => ?_
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [Function.comp_apply, norm_term_eq, hp.ne_zero, if_false, ofReal_re]
  have e : rsb (p : ℕ) = lam p ^ 2 := by
    have := rsb_pow hp 1; rw [pow_one] at this; rw [this]; rfl
  rw [rsB, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rsb_nonneg _), e,
    Real.rpow_neg hp0.le, div_eq_mul_inv]

lemma summable_Mb : Summable Mb := by
  have hB1 : Summable fun q : Nat.Primes × ℕ =>
      if q.2 = 0 then 4 * (lam q.1 ^ 2 + 2) * (q.1 : ℝ) ^ (-(7 / 4 : ℝ)) else 0 := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p, 0)) := fun a b h => by
      simpa using h
    refine (hinj.summable_iff (fun q hq => ?_)).mp ?_
    · split_ifs with h
      · exact absurd ⟨q.1, by ext <;> simp [h]⟩ hq
      · rfl
    · simp only [Function.comp_def, if_true]
      have h1 := (summable_lam_sq (a := 7 / 4) (by norm_num)).mul_left 4
      have h2 := (summable_primes_rpow (a := 7 / 4) (by norm_num)).mul_left 8
      refine (h1.add h2).congr fun p => ?_
      ring
  have hB2 : Summable fun q : Nat.Primes × ℕ => (8 / rr2) * (q.1 : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ q.2 := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => (8 / rr2) * (p : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => rr2 ^ k) ((summable_primes_rpow (a := 5 / 4) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one rr2_pos.le rr2_lt_one) ?_ ?_
    · intro p; simp only [Pi.zero_apply]; have := rr2_pos; positivity
    · intro k; simp only [Pi.zero_apply]; have := rr2_pos; positivity
  exact hB1.add hB2

lemma norm_sa_le_sqrt {p : ℕ} (hp : p.Prime) : ‖sa p‖ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsq : ((p : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have := norm_sa_sq_le hp
  rw [← hsq] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp this

lemma log_le_quarter {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 4)
  linarith [show x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) by ring]

/-- **Uniform domination of the tail on `σ ≥ 1`.** -/
lemma norm_term_vM_ppow2_le {σ : ℝ} (hσ : 1 ≤ σ) (q : Nat.Primes × ℕ) :
    ‖term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q)‖ ≤ Mb q := by
  obtain ⟨p, k⟩ := q
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog := log_le_quarter hp0.le
  simp only [ppow2, Mb]
  rw [norm_term_eq, if_neg (pow_ne_zero _ hp.ne_zero), ofReal_re, vM_pow hp (k + 1),
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0]
  set N : ℝ := ((p ^ (k + 2) : ℕ) : ℝ)
  have hN : N = (p : ℝ) ^ (k + 2) := by simp [N]
  have hN1 : 1 ≤ N := by rw [hN]; exact one_le_pow₀ hp1
  have hNσ : N ≤ N ^ σ := Real.self_le_rpow_of_one_le hN1 hσ
  have hNpos : 0 < N := by linarith
  have step1 : |AA p (k + 1 + 1)| * Real.log p / N ^ σ ≤ |AA p (k + 2)| * Real.log p / N :=
    div_le_div_of_nonneg_left (by positivity) hNpos hNσ
  refine step1.trans ?_
  have hB2 : 0 ≤ 8 / rr2 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ k := by
    have := rr2_pos; positivity
  have h74 : (p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hp0]; norm_num
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [if_true, zero_add]
    have hA : |AA p 2| ≤ lam p ^ 2 + 2 := by
      rw [AA_two, abs_le]; constructor <;> nlinarith [sq_nonneg (lam p)]
    have : |AA p 2| * Real.log p / N ≤ 4 * (lam p ^ 2 + 2) * (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
      rw [hN, ← h74, div_le_iff₀ (by positivity)]
      have e : 4 * (lam p ^ 2 + 2) * ((p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ 2) * (p : ℝ) ^ 2 =
          (lam p ^ 2 + 2) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) := by field_simp
      rw [e]
      exact mul_le_mul hA hlog hlog0 (by positivity)
    linarith
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [hk0, if_false, zero_add]
    set t : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
    have ht0 : 0 ≤ t := by positivity
    have htr : t ≤ rr2 := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have hat : ‖sa p‖ / p ≤ t := by
      rw [div_le_iff₀ hp0]
      have : t * p = (p : ℝ) ^ (1 / 2 : ℝ) := by
        simp only [t]
        rw [show (p : ℝ) ^ (-(1 / 2 : ℝ)) * p = (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hp0]
        norm_num
      rw [this]; exact norm_sa_le_sqrt hp
    have hA : |AA p (k + 2)| / N ≤ 2 * t ^ (k + 2) := by
      rw [hN, div_le_iff₀ (by positivity)]
      calc |AA p (k + 2)| ≤ 2 * ‖sa p‖ ^ (k + 2) := abs_AA_le p (k + 2)
        _ = 2 * (‖sa p‖ / p) ^ (k + 2) * (p : ℝ) ^ (k + 2) := by
          rw [div_pow]; field_simp
        _ ≤ 2 * t ^ (k + 2) * (p : ℝ) ^ (k + 2) := by
          gcongr
    have ht3 : t ^ 3 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      simp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    have htk : t ^ (k + 2) ≤ t ^ 3 * rr2 ^ (k - 1) := by
      have : t ^ (k + 2) = t ^ 3 * t ^ (k - 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 htr _) (by positivity)
    have hrk : rr2 ^ k = rr2 * rr2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have h54 : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) = (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hp0]; norm_num
    have hr0 := rr2_pos
    calc |AA p (k + 2)| * Real.log p / N = (|AA p (k + 2)| / N) * Real.log p := by ring
      _ ≤ (2 * t ^ (k + 2)) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hA hlog hlog0 (by positivity)
      _ ≤ (2 * (t ^ 3 * rr2 ^ (k - 1))) * (4 * (p : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * ((p : ℝ) ^ (1 / 4 : ℝ) * t ^ 3) * rr2 ^ (k - 1) := by ring
      _ = 8 / rr2 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * rr2 ^ k := by
          rw [ht3, h54, hrk]; field_simp

/-- The prime-power tail `T(σ) = ∑_{p,k≥2} Λ_Δ(p^k) p^{−kσ}`. -/
noncomputable def tail (σ : ℝ) : ℂ :=
  ∑' q : Nat.Primes × ℕ, term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q)

lemma tendsto_tail : Tendsto tail (𝓝[>] 1) (𝓝 (tail 1)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := Mb) summable_Mb (fun q => ?_) ?_
  · have hn : ppow2 q ≠ 0 := pow_ne_zero _ q.1.2.ne_zero
    have hc : Continuous fun σ : ℝ => term (fun n => (vM n : ℂ)) (σ : ℂ) (ppow2 q) := by
      simp only [term_of_ne_zero hn]
      refine continuous_const.div ?_ fun σ => ?_
      · exact continuous_ofReal.const_cpow (.inl (by exact_mod_cast hn))
      · rw [Ne, cpow_eq_zero_iff]
        exact fun h => (by exact_mod_cast hn : ((ppow2 q : ℕ) : ℂ) ≠ 0) h.1
    exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ) q
    exact norm_term_vM_ppow2_le hσ.le q

/-- `∑ Λ_Δ(n) n^{−σ} = (prime sum) + (tail)` for `σ > 1`. -/
lemma LSeries_vM_split {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => (vM n : ℂ)) σ = (primeSum σ : ℂ) + tail σ := by
  set f := term (fun n => (vM n : ℂ)) (σ : ℂ)
  have hf : Summable f := LSeriesSummable_vM (by simpa using hσ)
  have hsupp : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    apply hn
    simp only [f, term_def, vM_of_not h]; simp
  have h := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hf hsupp
  have hprod : Summable fun q : Nat.Primes × ℕ => f (ppow2 q) := hf.comp_injective ppow2_injective
  have e2 : ∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 2)) = tail σ := by
    rw [tail, hprod.tsum_prod]; rfl
  have e1 : ∑' p : Nat.Primes, f p = (primeSum σ : ℂ) := by
    rw [primeSum, Complex.ofReal_tsum]
    congr 1; funext p
    have hp := p.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [f, term_of_ne_zero hp.ne_zero, vM_prime hp]
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    push_cast
    rw [Complex.ofReal_cpow hp0.le]
    push_cast; rfl
  rw [LSeries, h, e1, e2]

/-- **Smoothed prime number theorem for `τ` (unconditional).**
`∑_p τ(p) p^{−11/2} log p · p^{−σ}` converges to a finite limit as `σ → 1⁺`
(whereas `∑_p log p · p^{−σ} ∼ 1/(σ−1)`). -/
theorem primeSum_tendsto : Tendsto primeSum (𝓝[>] 1) (𝓝 ((negLogDeriv 1 - tail 1).re)) := by
  have hL : Tendsto (fun σ : ℝ => negLogDeriv σ) (𝓝[>] 1) (𝓝 (negLogDeriv 1)) := by
    have h := (continuousAt_negLogDeriv (s := 1) (by simp)).tendsto.comp
      (continuous_ofReal.tendsto 1)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun σ : ℝ => (primeSum σ : ℂ)) (𝓝[>] 1) (𝓝 (negLogDeriv 1 - tail 1)) := by
    refine (hL.sub tendsto_tail).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [negLogDeriv_eq_LSeries (by simpa using hσ), LSeries_vM_split hσ]
    ring
  have := (Complex.continuous_re.tendsto _).comp hc
  simpa [Function.comp_def] using this

/-- In particular the smoothed prime sum is bounded as `σ → 1⁺`: it is `o(1/(σ−1))`. -/
theorem primeSum_bounded : ∃ M : ℝ, ∀ᶠ σ in 𝓝[>] (1 : ℝ), |primeSum σ| ≤ M :=
  ⟨|(negLogDeriv 1 - tail 1).re| + 1,
    (primeSum_tendsto.abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le⟩

end RamanujanTau.TauPNT
