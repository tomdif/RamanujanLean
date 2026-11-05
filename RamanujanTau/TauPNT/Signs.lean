/-
# Sign changes of `τ(p)` over primes (conditional on `DeligneBound`)

Under Deligne's bound `|λ(p)| ≤ 2`:

* `norm_sa_eq_one`: `‖α_p‖ = ‖β_p‖ = 1`, hence `|A_k(p)| ≤ 2`;
* `zetaRS_eq_exp`: `ζ(2σ)R(σ) = exp X(σ)` with `X(σ) = ∑_p ∑_k A_k(p)² p^{−kσ}/k`
  (local factor `((1−Y)²(1−α²Y)(1−β²Y))⁻¹ = exp ∑_k A_k² Y^k/k`), and
  `X(σ) ≤ ∑_p λ(p)²p^{−σ} + 32 ∑_p p^{−2}`;
* `tendsto_sum_lam_sq`: `∑_p λ(p)² p^{−σ} → ∞` as `σ → 1⁺` (pole of `R`, `rsc > 0`);
* `tau_prime_sign_changes`: infinitely many primes with `τ(p) > 0` and infinitely many with
  `τ(p) < 0`.  If `ελ(p) ≥ 0` for all `p ≥ P` then `λ² ≤ 2ελ` there, so
  `log 2 · ∑ λ²p^{−σ} ≤ 2ε·primeSum(σ) + O_P(1)`, bounded by the unconditional
  `PrimeSum.primeSum_tendsto` — contradicting the divergence.
-/
import RamanujanTau.TauPNT.PrimeSum
import RamanujanTau.Deligne
import RamanujanTau.RankinSelbergGeneral.Positive
import RamanujanTau.RankinSelbergGeneral.Main
import RamanujanTau.LandauSigns.Signs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.TauPNT

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.HeckeL

lemma rsc_pos : 0 < rsc := by
  have h := RankinSelbergGeneral.petNormSqF_pos (k := 12) _ LandauSigns.discriminant_ne_zero'
  rw [RankinSelbergGeneral.petNormSqF_discriminant] at h
  unfold rsc
  have := Real.pi_pos
  positivity

lemma rr_pos {p : ℕ} (hp : p.Prime) : 0 < rr p := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold rr; positivity

lemma lam_pos_iff {p : ℕ} (hp : p.Prime) : 0 < lam p ↔ 0 < tau p := by
  have h := rr_pos hp
  simp only [lam, uu, pow_one]
  constructor
  · intro h1; exact_mod_cast (pos_of_mul_pos_left h1 h.le : (0 : ℝ) < (tau p : ℝ))
  · intro h1; exact mul_pos (by exact_mod_cast h1) h

lemma lam_neg_iff {p : ℕ} (hp : p.Prime) : lam p < 0 ↔ tau p < 0 := by
  have h := rr_pos hp
  simp only [lam, uu, pow_one]
  constructor
  · intro h1
    have : (tau p : ℝ) < 0 := by
      by_contra hc; push Not at hc; nlinarith
    exact_mod_cast this
  · intro h1; exact mul_neg_of_neg_of_pos (by exact_mod_cast h1) h

/-- The real prime terms of `∑ Λ_Δ(n) n^{−σ}`. -/
lemma summable_primeSum_terms {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => lam p * Real.log p * (p : ℝ) ^ (-σ) := by
  have hf := (LSeriesSummable_vM (s := (σ : ℂ)) (by simpa using hσ)).comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  refine Complex.summable_ofReal.mp (hf.congr fun p => ?_)
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [Function.comp_apply, term_of_ne_zero hp.ne_zero, vM_prime hp]
  rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
  push_cast
  rw [Complex.ofReal_cpow hp0.le]
  push_cast; rfl

section Deligne

variable [DeligneBound]

lemma lam_sq_le_four {p : ℕ} (hp : p.Prime) : lam p ^ 2 ≤ 4 := by
  have h := DeligneBound.bound p hp
  have h' : ((tau p : ℝ)) ^ 2 ≤ 4 * (p : ℝ) ^ 11 := by exact_mod_cast h
  have hr := rr_sq hp
  simp only [lam, uu, pow_one]
  calc ((tau p : ℝ) * rr p) ^ 2 = (tau p : ℝ) ^ 2 * rr p ^ 2 := by ring
    _ ≤ 4 * (p : ℝ) ^ 11 * rr p ^ 2 := mul_le_mul_of_nonneg_right h' (sq_nonneg _)
    _ = 4 := by linear_combination 4 * hr

lemma abs_lam_le_two {p : ℕ} (hp : p.Prime) : |lam p| ≤ 2 := by
  have := lam_sq_le_four hp
  rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith

/-- Under Deligne, the Satake parameters lie on the unit circle. -/
lemma norm_sa_eq_one {p : ℕ} (hp : p.Prime) : ‖sa p‖ = 1 := by
  obtain ⟨hab, hs, h1, h2⟩ := sab p
  have hl := lam_sq_le_four hp
  have hβ : sb p = (lam p : ℂ) - sa p := by linear_combination hs
  rw [hβ] at hab
  have hre := congrArg Complex.re hab
  have him := congrArg Complex.im hab
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im] at hre him
  set a := (sa p).re
  set b := (sa p).im
  set l := lam p
  have key : a ^ 2 + b ^ 2 = 1 := by
    have hm : b * (l - 2 * a) = 0 := by linarith
    rcases mul_eq_zero.mp hm with hb | hl2
    · rw [hb] at hre
      have e : (2 * a - l) ^ 2 = l ^ 2 - 4 := by nlinarith
      have e2 : 2 * a - l = 0 := by
        have : (2 * a - l) ^ 2 ≤ 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
      rw [hb]; nlinarith
    · have : l = 2 * a := by linarith
      rw [this] at hre; nlinarith
  have hn : ‖sa p‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have h0 := norm_nonneg (sa p)
  nlinarith

lemma norm_sb_eq_one {p : ℕ} (hp : p.Prime) : ‖sb p‖ = 1 := by
  have h := congrArg norm (sab p).1
  rw [norm_mul, norm_sa_eq_one hp, one_mul, norm_one] at h
  exact h

lemma abs_AA_le_two {p : ℕ} (hp : p.Prime) (k : ℕ) : |AA p k| ≤ 2 := by
  have := abs_AA_le p k
  rwa [norm_sa_eq_one hp, one_pow, mul_one] at this

/-- The local exponent `g_p(σ) = ∑_k A_k(p)² p^{−kσ}/k` of `ζ(2σ)R(σ)`. -/
noncomputable def gR (σ : ℝ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, AA p k ^ 2 * ((p : ℝ) ^ (-σ)) ^ k / k

lemma y_le_half {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) : (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by norm_num

lemma local_R {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    HasSum (fun k : ℕ => AA p k ^ 2 * ((p : ℝ) ^ (-σ)) ^ k / k) (gR σ p) ∧
      fR (σ : ℂ) p = ((Real.exp (gR σ p) : ℝ) : ℂ) := by
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hα1 := norm_sa_eq_one hp
  have hβ1 := norm_sb_eq_one hp
  have hsR : 1 < (σ : ℂ).re := by simpa using hσ
  have hloc := rs_local hsR hp (sab p).1 (sab p).2.1 (by rw [hα1]; norm_num; exact_mod_cast hp.one_lt.le)
    (sab p).2.2.2
  set y : ℝ := (p : ℝ) ^ (-σ)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by have := y_le_half hσ hp; linarith
  set Y : ℂ := ((p : ℕ) : ℂ) ^ (-(σ : ℂ))
  have hY : Y = (y : ℂ) := by
    simp only [Y, y]; rw [Complex.ofReal_cpow hp0.le]; push_cast; rfl
  have hnY : ‖Y‖ = y := by rw [hY, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
  obtain ⟨h1, h2⟩ := list_log [Y, Y, sa p ^ 2 * Y, sb p ^ 2 * Y] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      simp only [norm_mul, norm_pow, hα1, hβ1, one_pow, one_mul, hnY] <;> exact hy1)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one] at h1 h2
  have hterm : ∀ k : ℕ, (Y ^ k + (Y ^ k + ((sa p ^ 2 * Y) ^ k + (sb p ^ 2 * Y) ^ k))) / k =
      ((AA p k ^ 2 * y ^ k / k : ℝ) : ℂ) := by
    intro k
    have hk : sa p ^ k * sb p ^ k = 1 := by rw [← mul_pow, (sab p).1, one_pow]
    push_cast
    rw [AA_eq, ← hY]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k, pow_mul, pow_mul]
    linear_combination (-2 * Y ^ k) * hk
  simp_rw [hterm] at h1
  have hsum := Complex.summable_ofReal.mp h1.summable
  have hS : (∑' k : ℕ, ((AA p k ^ 2 * y ^ k / k : ℝ) : ℂ)) = ((gR σ p : ℝ) : ℂ) := by
    rw [gR, Complex.ofReal_tsum]
  refine ⟨hsum.hasSum, ?_⟩
  rw [fR, hloc, Complex.ofReal_exp, ← hS, h1.tsum_eq, ← h2]
  congr 1; ring

lemma gR_nonneg {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) : 0 ≤ gR σ p :=
  tsum_nonneg fun k => by
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := by positivity
    positivity

lemma gR_le {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    gR σ p ≤ lam p ^ 2 * (p : ℝ) ^ (-σ) + 32 * ((p : ℝ) ^ (-σ)) ^ 2 := by
  have hp := p.2
  set y : ℝ := (p : ℝ) ^ (-σ)
  have hy0 : 0 ≤ y := by positivity
  have hyh : y ≤ 1 / 2 := y_le_half hσ hp
  have hg : HasSum (fun k : ℕ => (if k = 1 then lam p ^ 2 * y else 0) + 16 * y ^ 2 * (1 / 2) ^ k)
      (lam p ^ 2 * y + 16 * y ^ 2 * 2) :=
    (hasSum_ite_eq 1 (lam p ^ 2 * y)).add (hasSum_geometric_two.mul_left _)
  have hle := hasSum_le (fun k => ?_) (local_R hσ p).1 hg
  · linarith
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp only [pow_zero, Nat.cast_zero, div_zero, zero_ne_one, if_false, zero_add, mul_one]
        positivity
      · simp only [pow_one, Nat.cast_one, div_one, if_true, AA_one]
        have : 0 ≤ 16 * y ^ 2 * (1 / 2) := by positivity
        linarith
    · have hk1 : k ≠ 1 := by omega
      simp only [hk1, if_false, zero_add]
      have hA : AA p k ^ 2 ≤ 4 := by
        have := abs_AA_le_two hp k
        nlinarith [abs_nonneg (AA p k), sq_abs (AA p k)]
      have hkk : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hyk : y ^ k ≤ y ^ 2 * (1 / 2) ^ (k - 2) := by
        have : y ^ k = y ^ 2 * y ^ (k - 2) := by rw [← pow_add]; congr 1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hyh _) (by positivity)
      have h2 : ((1 : ℝ) / 2) ^ k = (1 / 2) ^ 2 * (1 / 2) ^ (k - 2) := by
        rw [← pow_add]; congr 1; omega
      calc AA p k ^ 2 * y ^ k / k ≤ AA p k ^ 2 * y ^ k :=
            div_le_self (by positivity) hkk
        _ ≤ 4 * (y ^ 2 * (1 / 2) ^ (k - 2)) :=
            mul_le_mul hA hyk (by positivity) (by norm_num)
        _ = 16 * y ^ 2 * (1 / 2) ^ k := by rw [h2]; ring

lemma summable_gR {σ : ℝ} (hσ : 1 < σ) : Summable fun p : Nat.Primes => gR σ p := by
  have h1 := summable_lam_sq hσ
  have h2 := (summable_primes_rpow (a := 2 * σ) (by linarith)).mul_left 32
  refine Summable.of_nonneg_of_le (gR_nonneg hσ) (fun p => ?_) (h1.add h2)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have e : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
  have := gR_le hσ p
  rw [e] at this
  exact this

/-- **`ζ(2σ)R(σ) = exp(∑_p g_p(σ))`** (Deligne). -/
lemma zetaRS_eq_exp {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta (2 * (σ : ℂ)) * RS σ = ((Real.exp (∑' p : Nat.Primes, gR σ p) : ℝ) : ℂ) := by
  have hX := (summable_gR hσ).hasSum
  have hE := (hX.rexp).map Complex.ofRealHom Complex.continuous_ofReal
  have hF := fR_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have heq : (Complex.ofRealHom ∘ Real.exp ∘ fun p : Nat.Primes => gR σ p) =
      fun p : Nat.Primes => fR (σ : ℂ) p := by
    funext p; simp [(local_R hσ p).2]
  rw [heq] at hE
  exact hF.unique hE

/-- `ζ(σ) ≥ 1/(2(σ−1))` near `1⁺`. -/
lemma zeta_lower : ∀ᶠ σ : ℝ in 𝓝[>] 1, 1 / (2 * (σ - 1)) ≤ (riemannZeta σ).re := by
  have hφ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast hσ.ne'
  have h := ((Complex.continuous_re.tendsto _).comp (riemannZeta_residue_one.comp hφ))
  simp only [Function.comp_def, Complex.one_re] at h
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with σ hσ (h1 : 1 < σ)
  have e : (((σ : ℂ) - 1) * riemannZeta σ).re = (σ - 1) * (riemannZeta σ).re := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [e] at hσ
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma tendsto_inv_sub_one : Tendsto (fun σ : ℝ => (σ - 1)⁻¹) (𝓝[>] 1) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    simpa using hσ

lemma sum_gR_le {σ : ℝ} (hσ : 1 < σ) (C2 : ℝ) (hC2 : C2 = ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ))) :
    ∑' p : Nat.Primes, gR σ p ≤ (∑' p : Nat.Primes, lam p ^ 2 * (p : ℝ) ^ (-σ)) + 32 * C2 := by
  have h1 := summable_lam_sq hσ
  have h2 := (summable_primes_rpow (a := 2 * σ) (by linarith)).mul_left 32
  have h3 := summable_primes_rpow (a := 2) (by norm_num)
  have hle : ∑' p : Nat.Primes, gR σ p ≤
      ∑' p : Nat.Primes, (lam p ^ 2 * (p : ℝ) ^ (-σ) + 32 * (p : ℝ) ^ (-(2 * σ))) := by
    refine (summable_gR hσ).tsum_le_tsum (fun p => ?_) (h1.add h2)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have e : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
    have := gR_le hσ p; rw [e] at this; exact this
  have hle2 : ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 * σ)) ≤ C2 := by
    rw [hC2]
    refine (summable_primes_rpow (a := 2 * σ) (by linarith)).tsum_le_tsum (fun p => ?_) h3
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rw [h1.tsum_add h2, tsum_mul_left] at hle
  linarith

/-- **Rankin–Selberg over primes** (Deligne): `∑_p λ(p)² p^{−σ} → ∞` as `σ → 1⁺`. -/
theorem tendsto_sum_lam_sq :
    Tendsto (fun σ : ℝ => ∑' p : Nat.Primes, lam p ^ 2 * (p : ℝ) ^ (-σ)) (𝓝[>] 1) atTop := by
  obtain ⟨K, hK0, hK⟩ := rs_sub_zeta_bound
  set z2 := (riemannZeta 2).re
  have hz2 : 0 < z2 := by simpa using riemannZeta_re_pos_of_one_lt (x := 2) (by norm_num)
  -- `ζ(2σ) → ζ(2)`
  have hzc : Tendsto (fun σ : ℝ => (riemannZeta (2 * (σ : ℂ))).re) (𝓝[>] 1) (𝓝 z2) := by
    have hc : Continuous fun σ : ℝ => 2 * (σ : ℂ) := by fun_prop
    have h0 : Tendsto (fun σ : ℝ => 2 * (σ : ℂ)) (𝓝[>] 1) (𝓝 2) := by
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    have h := ((Complex.continuous_re.tendsto _).comp
      ((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp h0))
    simpa [Function.comp_def] using h
  -- the lower bound `exp X(σ) ≥ (z2/2)(rsc/(2(σ−1)) − 5K)`
  set f : ℝ → ℝ := fun σ => z2 / 2 * (rsc / 2 * (σ - 1)⁻¹ - 5 * K)
  have hf : Tendsto f (𝓝[>] 1) atTop := by
    have := ((tendsto_inv_sub_one.const_mul_atTop (by have := rsc_pos; positivity :
      (0 : ℝ) < rsc / 2)).atTop_add (tendsto_const_nhds (x := -(5 * K))))
    refine (this.const_mul_atTop (by positivity : (0 : ℝ) < z2 / 2)).congr fun σ => ?_
    simp only [f]; ring
  have hlow : ∀ᶠ σ : ℝ in 𝓝[>] 1, f σ ≤ Real.exp (∑' p : Nat.Primes, gR σ p) := by
    filter_upwards [zeta_lower, self_mem_nhdsWithin, hzc.eventually (lt_mem_nhds (half_lt_self hz2)),
      Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hζ (hσ : 1 < σ) hz hσ2
    have hσ2' : σ < 2 := hσ2.2
    have he := congrArg Complex.re (zetaRS_eq_exp hσ)
    rw [Complex.ofReal_re] at he
    rw [← he]
    have him : (riemannZeta (2 * (σ : ℂ))).im = 0 := by
      have := riemannZeta_im_eq_zero_of_one_lt (x := 2 * σ) (by linarith)
      simpa using this
    rw [Complex.mul_re, him, zero_mul, sub_zero]
    -- `Re R(σ) ≥ rsc ζ(σ) − 5K`
    have hR := hK σ (by simpa using hσ)
    have hsre : (σ : ℂ).re = σ := by simp
    have hsn : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hsre, hsn] at hR
    have hR5 : K * σ / (σ - 3 / 5) ≤ 5 * K := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hre : rsc * (riemannZeta σ).re - 5 * K ≤ (RS σ).re := by
      have h1 := Complex.abs_re_le_norm (RS σ - rsc * riemannZeta σ)
      have h2 : (RS σ - rsc * riemannZeta σ).re = (RS σ).re - rsc * (riemannZeta σ).re := by
        simp [Complex.sub_re, Complex.re_ofReal_mul]
      rw [h2] at h1
      have := neg_abs_le ((RS σ).re - rsc * (riemannZeta σ).re)
      linarith
    have hζ' : rsc / 2 * (σ - 1)⁻¹ ≤ rsc * (riemannZeta σ).re := by
      have : rsc / 2 * (σ - 1)⁻¹ = rsc * (1 / (2 * (σ - 1))) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hζ rsc_pos.le
    simp only [f]
    rcases le_or_gt (rsc / 2 * (σ - 1)⁻¹ - 5 * K) 0 with hneg | hpos
    · have h0 : 0 ≤ (riemannZeta (2 * (σ : ℂ))).re * (RS σ).re := by
        have hE := (Real.exp_pos (∑' p : Nat.Primes, gR σ p)).le
        rw [← he] at hE
        rwa [Complex.mul_re, him, zero_mul, sub_zero] at hE
      nlinarith
    · calc z2 / 2 * (rsc / 2 * (σ - 1)⁻¹ - 5 * K)
          ≤ (riemannZeta (2 * (σ : ℂ))).re * (rsc / 2 * (σ - 1)⁻¹ - 5 * K) :=
            mul_le_mul_of_nonneg_right hz.le hpos.le
        _ ≤ (riemannZeta (2 * (σ : ℂ))).re * (RS σ).re :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hX : Tendsto (fun σ : ℝ => ∑' p : Nat.Primes, gR σ p) (𝓝[>] 1) atTop := by
    have hE : Tendsto (fun σ : ℝ => Real.exp (∑' p : Nat.Primes, gR σ p)) (𝓝[>] 1) atTop :=
      tendsto_atTop_mono' _ hlow hf
    have := Real.tendsto_log_atTop.comp hE
    simpa [Function.comp_def, Real.log_exp] using this
  -- `X(σ) ≤ ∑ λ²p^{−σ} + 32 ∑ p^{−2}`
  set C2 : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ))
  have hmono : ∀ᶠ σ : ℝ in 𝓝[>] 1, ∑' p : Nat.Primes, gR σ p ≤
      (∑' p : Nat.Primes, lam p ^ 2 * (p : ℝ) ^ (-σ)) + 32 * C2 := by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact sum_gR_le hσ C2 rfl
  have := tendsto_atTop_add_const_right _ (-(32 * C2)) (tendsto_atTop_mono' _ hmono hX)
  exact this.congr fun σ => by ring

/-- No eventual sign: if `ε λ(p) ≥ 0` for all primes `p ≥ P` (`ε = ±1`), contradiction. -/
theorem not_eventually_signed (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (P : ℕ)
    (h : ∀ p : ℕ, p.Prime → P ≤ p → 0 ≤ ε * lam p) : False := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨M, hM⟩ := primeSum_bounded
  set s : Finset Nat.Primes := (Finset.range (P + 1)).subtype Nat.Prime
  set KP : ℝ := ∑' p : Nat.Primes, if p ∈ s then 8 * Real.log p else 0
  have hKs : Summable fun p : Nat.Primes => if p ∈ s then 8 * Real.log p else 0 :=
    summable_of_ne_finset_zero (s := s) fun p hp => by simp [hp]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      Real.log 2 * ∑' p : Nat.Primes, lam p ^ 2 * (p : ℝ) ^ (-σ) ≤ 2 * M + KP := by
    filter_upwards [hM, self_mem_nhdsWithin] with σ hMσ (hσ : 1 < σ)
    have hg := summable_primeSum_terms hσ
    have hsq := summable_lam_sq hσ
    -- pointwise: `log 2 · λ² p^{−σ} ≤ 2ε λ log p p^{−σ} + [p ≤ P] 8 log p`
    have hpt : ∀ p : Nat.Primes, Real.log 2 * (lam p ^ 2 * (p : ℝ) ^ (-σ)) ≤
        2 * ε * (lam p * Real.log p * (p : ℝ) ^ (-σ)) + (if p ∈ s then 8 * Real.log p else 0) := by
      intro p
      have hp := p.2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hlp : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      set w : ℝ := Real.log p * (p : ℝ) ^ (-σ)
      have hw0 : 0 ≤ w := mul_nonneg (Real.log_nonneg hp1) (by positivity)
      have hy1 : (p : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
      have hwl : w ≤ Real.log p := mul_le_of_le_one_right (Real.log_nonneg hp1) hy1
      have h2w : Real.log 2 * (lam p ^ 2 * (p : ℝ) ^ (-σ)) ≤ lam p ^ 2 * w := by
        simp only [w]
        have := mul_le_mul_of_nonneg_right hlp
          (mul_nonneg (sq_nonneg (lam p)) (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ (-σ)))
        nlinarith
      have hl := abs_lam_le_two hp
      have hl' := lam_sq_le_four hp
      have hεl : |ε * lam p| ≤ 2 := by rw [abs_mul, hεa, one_mul]; exact hl
      have e : 2 * ε * (lam p * Real.log p * (p : ℝ) ^ (-σ)) = 2 * (ε * lam p) * w := by
        simp only [w]; ring
      rw [e]
      by_cases hps : p ∈ s
      · simp only [hps, if_true]
        have : lam p ^ 2 - 2 * (ε * lam p) ≤ 8 := by
          have := neg_abs_le (ε * lam p); nlinarith
        nlinarith
      · simp only [hps, if_false, add_zero]
        have hPp : P ≤ (p : ℕ) := by
          by_contra hc
          apply hps
          exact Finset.mem_subtype.mpr (Finset.mem_range.mpr (by omega))
        have h0 := h p hp hPp
        have hsqε : lam p ^ 2 = (ε * lam p) ^ 2 := by rw [mul_pow, hε2, one_mul]
        have : lam p ^ 2 ≤ 2 * (ε * lam p) := by
          rw [hsqε]
          have := (abs_le.mp hεl).2
          nlinarith
        nlinarith
    have hsum := (hsq.mul_left (Real.log 2)).tsum_le_tsum hpt
      ((hg.mul_left (2 * ε)).add hKs)
    rw [tsum_mul_left, (hg.mul_left (2 * ε)).tsum_add hKs, tsum_mul_left] at hsum
    have : 2 * ε * primeSum σ ≤ 2 * M := by
      have h1 : |2 * ε * primeSum σ| ≤ 2 * M := by
        rw [abs_mul, abs_mul, hεa]; simp; linarith
      exact (le_abs_self _).trans h1
    simp only [primeSum] at this
    linarith
  have hdiv := (tendsto_sum_lam_sq.const_mul_atTop hl2).eventually_gt_atTop (2 * M + KP)
  obtain ⟨σ, h1, h2⟩ := (hbound.and hdiv).exists
  linarith

/-- **Sign changes of `τ(p)` over primes** (conditional on `DeligneBound`): for every `N`
there are primes `p, q ≥ N` with `τ(p) > 0` and `τ(q) < 0`. -/
theorem tau_prime_sign_changes :
    (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ 0 < tau p) ∧ (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ tau p < 0) := by
  constructor
  · intro N
    by_contra hc
    push Not at hc
    refine not_eventually_signed (-1) (.inr rfl) N fun p hp hNp => ?_
    have := hc p hNp hp
    have : ¬ 0 < lam p := fun h => absurd ((lam_pos_iff hp).mp h) (not_lt.mpr this)
    linarith [not_lt.mp this]
  · intro N
    by_contra hc
    push Not at hc
    refine not_eventually_signed 1 (.inl rfl) N fun p hp hNp => ?_
    have := hc p hNp hp
    have : ¬ lam p < 0 := fun h => absurd ((lam_neg_iff hp).mp h) (not_lt.mpr this)
    linarith [not_lt.mp this]

end Deligne

end RamanujanTau.TauPNT
