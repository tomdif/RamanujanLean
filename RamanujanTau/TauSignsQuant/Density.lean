/-
# Quantitative sign changes of `τ(p)`, unconditionally: the signed primes are not sparse

`λ(p) = τ(p) p^{−11/2}`, `ε = ±1`.

* `not_summable_signed_part`: for every `σ < 29/40`,
  `∑_{p : ελ(p) < 0} |λ(p)| log p · p^{−σ} = ∞`.
  (Landau's theorem, as in `TauPNTUncond.not_eventually_signed_uncond`, but with the hypothesis
  "`ελ(p) ≥ 0` eventually" weakened to "the `ελ < 0` part converges absolutely at `σ`".)
* `not_summable_rpow_signed`: for every `β < 9/20`, `∑_{p : ελ(p) < 0} p^{−β} = ∞`.
* `not_summable_tau_pos`, `not_summable_tau_neg`: the same with `τ(p) > 0`, resp. `τ(p) < 0`.

Proof of the first.  Put `a(p) = ελ(p) log p` if `ελ(p) ≥ 0` (else `0`) and `b = εΛ_Δ − a`
(the `ελ < 0` primes plus the prime powers).  `b` converges absolutely at `σ₁ = max σ (5/8)`, by
hypothesis and `summable_vH_58`; `a ≥ 0`, `L(Δ, s + 11/2) > 0` on the real axis.  Landau gives
`∑ a(n) n^{−σ₂} < ∞` for `σ₂ ∈ (σ₁, 29/40)`, so `∑_p |λ(p)| log p · p^{−σ₂} < ∞`; with Weil,
`λ(p)²/p ≤ C|λ(p)| p^{−29/40}`, contradicting `∑_p λ(p)²/p = ∞`.
-/
import RamanujanTau.TauPNTUncond.Signs

set_option autoImplicit false

namespace RamanujanTau.TauSignsQuant

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT RamanujanTau.HeckeL
open RamanujanTau.TauPNTUncond

/-- The nonnegative part: `a(p) = ε Λ_Δ(p)` on primes with `ελ(p) ≥ 0`. -/
noncomputable def aP (ε : ℝ) (n : ℕ) : ℝ := if n.Prime ∧ 0 ≤ ε * lam n then ε * vM n else 0

/-- The rest. -/
noncomputable def bP (ε : ℝ) (n : ℕ) : ℝ :=
  ε * ((if n.Prime ∧ ε * lam n < 0 then vM n else 0) + vHi n)

lemma decompP (ε : ℝ) (n : ℕ) : ε * vM n = aP ε n + bP ε n := by
  unfold aP bP vHi
  by_cases hp : n.Prime
  · by_cases hs : 0 ≤ ε * lam n
    · rw [if_pos ⟨hp, hs⟩, if_neg (fun h => by linarith [h.2]), if_pos hp]; ring
    · rw [if_neg (fun h => hs h.2), if_pos ⟨hp, by linarith⟩, if_pos hp]; ring
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1), if_neg hp]; ring

/-- The `ελ < 0` part, weighted at `σ`. -/
noncomputable def negW (ε σ : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ ε * lam p < 0 then |lam p| * Real.log p * (p : ℝ) ^ (-σ) else 0

lemma negW_nonneg (ε σ : ℝ) (p : ℕ) : 0 ≤ negW ε σ p := by
  unfold negW
  split_ifs with h
  · have := Real.log_nonneg (by exact_mod_cast h.1.one_lt.le : (1 : ℝ) ≤ p)
    positivity
  · exact le_rfl

lemma negW_anti (ε : ℝ) {σ σ' : ℝ} (h : σ ≤ σ') (p : ℕ) : negW ε σ' p ≤ negW ε σ p := by
  unfold negW
  split_ifs with hp
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.one_lt.le
    have := Real.log_nonneg hp1
    have : (p : ℝ) ^ (-σ') ≤ (p : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    gcongr
  · exact le_rfl

set_option maxHeartbeats 1000000 in
/-- **Landau, quantitatively**: for `σ < 29/40`, the `ελ < 0` part of `∑_p |λ(p)| log p p^{−σ}`
diverges.  Equivalently `∑_{ελ(p) > 0} ... = ∞` with `−ε`. -/
theorem not_summable_signed_part (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {σ : ℝ} (hσ : σ < 29 / 40) :
    ¬ Summable (negW ε σ) := by
  intro hsum
  have hεε : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set σ1 : ℝ := max σ (5 / 8)
  have hσ1 : σ1 < 29 / 40 := max_lt hσ (by norm_num)
  have h58 : (5 / 8 : ℝ) ≤ σ1 := le_max_right _ _
  have hsum1 : Summable (negW ε σ1) :=
    Summable.of_nonneg_of_le (negW_nonneg ε σ1) (negW_anti ε (le_max_left _ _)) hsum
  set a := aP ε
  set b := bP ε
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    simp only [a, aP]
    split_ifs with hn
    · rw [vM_prime hn.1, ← mul_assoc]
      exact mul_nonneg hn.2 (Real.log_nonneg (by exact_mod_cast hn.1.one_lt.le))
    · exact le_rfl
  -- `b` converges absolutely at `σ1`
  have hneg : LSeriesSummable (fun n => ((if n.Prime ∧ ε * lam n < 0 then vM n else 0 : ℝ) : ℂ))
      (σ1 : ℂ) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum1)
    rcases eq_or_ne n 0 with rfl | h0
    · simp [negW_nonneg]
    rw [norm_term_eq, if_neg h0, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    simp only [negW]
    split_ifs with hn
    · have hp0 : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
      have hlog := Real.log_nonneg (by exact_mod_cast hn.1.one_lt.le : (1 : ℝ) ≤ n)
      rw [vM_prime hn.1, abs_mul, abs_of_nonneg hlog, Real.rpow_neg hp0.le, div_eq_mul_inv]
    · simp
  have hbsum : LSeriesSummable (fun n => (b n : ℂ)) (σ1 : ℂ) := by
    have hH : LSeriesSummable (fun n => (vHi n : ℂ)) (σ1 : ℂ) :=
      summable_vH_58.of_re_le_re (by simpa using h58)
    have h := (hneg.add hH).smul (ε : ℂ)
    refine h.congr fun n => ?_
    simp only [b, bP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LSeries.term_add, term_smul]
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · simp only [term_of_ne_zero h0]; push_cast; ring
  have hb : abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ (σ1 : EReal) := by
    simpa using hbsum.abscissaOfAbsConv_le
  have hsplit : ((ε : ℂ)) • (fun n => (vM n : ℂ)) = (fun n => (a n : ℂ)) + fun n => (b n : ℂ) := by
    funext n; simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, a, b]
    rw [← Complex.ofReal_mul, decompP ε n]; push_cast; ring
  have hbs : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (b n : ℂ)) s := fun s hs =>
    hbsum.of_re_le_re (by simp; linarith)
  have has : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (a n : ℂ)) s := by
    intro s hs
    have h1 := (LSeriesSummable_vM hs).smul (ε : ℂ)
    rw [hsplit] at h1
    have := h1.sub (hbs s hs)
    simpa using this
  have ha1 : abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ 1 :=
    abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => has _ (by simpa using hy)
  have hLσ : ∀ t : ℝ, σ1 < t → t ≤ 1 → Lnorm t ≠ 0 := by
    intro t ht _ h0
    have hpos := (HeckeL.tauL_pos (σ := t + 11 / 2) (by linarith)).2
    have e : ((t + 11 / 2 : ℝ) : ℂ) = (t : ℂ) + 11 / 2 := by push_cast; ring
    rw [e] at hpos
    unfold Lnorm at h0
    rw [h0] at hpos; simp at hpos
  have heq : ∀ s : ℂ, 1 < s.re → Lnorm s ≠ 0 ∧
      (ε : ℂ) * (-deriv Lnorm s / Lnorm s) =
        LSeries (fun n => (a n : ℂ)) s + LSeries (fun n => (b n : ℂ)) s := by
    intro s hs
    refine ⟨Lnorm_ne_zero hs.le, ?_⟩
    have h1 : -deriv Lnorm s / Lnorm s = negLogDeriv s := by rw [negLogDeriv, neg_div]
    rw [h1, negLogDeriv_eq_LSeries hs, ← LSeries_smul, hsplit,
      LSeries_add (has s hs) (hbs s hs)]
  have hab := landau_abscissa ha hb ha1 Lnorm_differentiable hLσ hεε heq
  set σ2 : ℝ := (σ1 + 29 / 40) / 2
  have h12 : σ1 < σ2 := by simp only [σ2]; linarith
  have h2 : σ2 < 29 / 40 := by simp only [σ2]; linarith
  have hconv : LSeriesSummable (fun n => (a n : ℂ)) (σ2 : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (hab.trans_lt (by simp only [Complex.ofReal_re]; exact_mod_cast h12))
  have hreal : Summable fun n : ℕ => a n / (n : ℝ) ^ σ2 := by
    refine hconv.norm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | h0
    · simp [a, aP, Nat.not_prime_zero]
    · rw [norm_term_eq, if_neg h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
        Complex.ofReal_re]
  -- `∑_p |λ(p)| log p p^{−σ2} < ∞`
  have habsP : Summable fun p : Nat.Primes =>
      a p / (p : ℝ) ^ σ2 + negW ε σ1 p :=
    (hreal.comp_injective Subtype.val_injective).add
      (hsum1.comp_injective Subtype.val_injective)
  obtain ⟨C, hC1, hC⟩ := weil_uu
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine not_summable_lam_sq (Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (habsP.mul_left (C / Real.log 2)))
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  -- key: |λ| log p p^{-σ2} ≤ a p / p^σ2 + negW
  have hkey : |lam p| * Real.log p * (p : ℝ) ^ (-σ2) ≤ a p / (p : ℝ) ^ σ2 + negW ε σ1 p := by
    have hA0 : 0 ≤ a p / (p : ℝ) ^ σ2 := div_nonneg (ha p) (by positivity)
    have hN0 := negW_nonneg ε σ1 p
    by_cases hs : 0 ≤ ε * lam p
    · have hap : a p = |lam p| * Real.log p := by
        simp only [a, aP, if_pos (⟨hp, hs⟩ : (p : ℕ).Prime ∧ 0 ≤ ε * lam p), vM_prime hp]
        rw [← mul_assoc, ← abs_of_nonneg hs, abs_mul, hεa, one_mul]
      rw [hap, Real.rpow_neg hp0.le, ← div_eq_mul_inv]; linarith
    · have hnw : negW ε σ1 p = |lam p| * Real.log p * (p : ℝ) ^ (-σ1) := by
        simp only [negW, if_pos (⟨hp, by linarith⟩ : (p : ℕ).Prime ∧ ε * lam p < 0)]
      have : (p : ℝ) ^ (-σ2) ≤ (p : ℝ) ^ (-σ1) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      have : |lam p| * Real.log p * (p : ℝ) ^ (-σ2) ≤ |lam p| * Real.log p * (p : ℝ) ^ (-σ1) := by
        gcongr
      linarith
  have hlam : |lam p| ≤ C * rho p := by
    have := hC hp 1; rwa [pow_one] at this
  have hlog2 : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hρp : rho p * (p : ℝ)⁻¹ = (p : ℝ) ^ (-(29 / 40 : ℝ)) := by
    rw [rho, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
  have h2940 : (p : ℝ) ^ (-(29 / 40 : ℝ)) ≤ (p : ℝ) ^ (-σ2) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  calc lam p ^ 2 * (p : ℝ)⁻¹ = |lam p| * (|lam p| * (p : ℝ)⁻¹) := by rw [← sq_abs]; ring
    _ ≤ |lam p| * (C * rho p * (p : ℝ)⁻¹) := by gcongr
    _ = C * (|lam p| * (p : ℝ) ^ (-(29 / 40 : ℝ))) := by rw [mul_assoc C, hρp]; ring
    _ ≤ C * (|lam p| * (p : ℝ) ^ (-σ2)) := by gcongr
    _ ≤ C * (|lam p| * (Real.log p / Real.log 2) * (p : ℝ) ^ (-σ2)) := by
        gcongr
        have h1 : 1 ≤ Real.log p / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
        nlinarith [abs_nonneg (lam p)]
    _ = C / Real.log 2 * (|lam p| * Real.log p * (p : ℝ) ^ (-σ2)) := by ring
    _ ≤ C / Real.log 2 * (a p / (p : ℝ) ^ σ2 + negW ε σ1 p) := by gcongr

/-- **The `ελ < 0` primes are not sparse**: `∑_{p : ελ(p) < 0} p^{−β} = ∞` for every `β < 9/20`. -/
theorem not_summable_rpow_signed (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {β : ℝ} (hβ : β < 9 / 20) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ ε * lam p < 0 then (p : ℝ) ^ (-β) else 0) := by
  intro hs
  set δ : ℝ := (9 / 20 - β) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  set σ : ℝ := β + 11 / 40 + δ
  have hσ : σ < 29 / 40 := by simp only [σ, δ]; linarith
  obtain ⟨C, hC1, hC⟩ := weil_uu
  refine not_summable_signed_part ε hε hσ
    (Summable.of_nonneg_of_le (negW_nonneg ε σ) (fun p => ?_) (hs.mul_left (C / δ)))
  simp only [negW]
  split_ifs with hp
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
    have hlog := Real.log_le_rpow_div hp0.le hδ
    have hlog0 := Real.log_nonneg (by exact_mod_cast hp.1.one_lt.le : (1 : ℝ) ≤ p)
    have hlam : |lam p| ≤ C * rho p := by
      have := hC hp.1 1; rwa [pow_one] at this
    have e : rho p * ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (-β) / δ := by
      rw [rho, mul_div_assoc', div_mul_eq_mul_div, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
      congr 2; simp only [σ]; ring
    calc |lam p| * Real.log p * (p : ℝ) ^ (-σ) ≤ (C * rho p) * ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-σ) := by
          have := rho_pos hp.1
          gcongr
      _ = C / δ * (p : ℝ) ^ (-β) := by rw [mul_assoc C, mul_assoc C, e]; ring
  · simp

/-- **Primes with `τ(p) > 0` are not sparse**: `∑_{τ(p) > 0} p^{−β} = ∞` for every `β < 9/20`. -/
theorem not_summable_tau_pos {β : ℝ} (hβ : β < 9 / 20) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ 0 < tau p then (p : ℝ) ^ (-β) else 0) := by
  have h := not_summable_rpow_signed (-1) (Or.inr rfl) hβ
  have e : (fun p : ℕ => if p.Prime ∧ 0 < tau p then (p : ℝ) ^ (-β) else 0) =
      (fun p : ℕ => if p.Prime ∧ -1 * lam p < 0 then (p : ℝ) ^ (-β) else 0) := by
    funext p
    by_cases hp : p.Prime
    · have : (-1 * lam p < 0) ↔ 0 < tau p := by
        rw [← lam_pos_iff hp]; constructor <;> intro h <;> linarith
      simp only [hp, true_and, this]
    · simp [hp]
  rwa [e]

/-- **Primes with `τ(p) < 0` are not sparse**: `∑_{τ(p) < 0} p^{−β} = ∞` for every `β < 9/20`. -/
theorem not_summable_tau_neg {β : ℝ} (hβ : β < 9 / 20) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ tau p < 0 then (p : ℝ) ^ (-β) else 0) := by
  have h := not_summable_rpow_signed 1 (Or.inl rfl) hβ
  have e : (fun p : ℕ => if p.Prime ∧ tau p < 0 then (p : ℝ) ^ (-β) else 0) =
      (fun p : ℕ => if p.Prime ∧ 1 * lam p < 0 then (p : ℝ) ^ (-β) else 0) := by
    funext p
    by_cases hp : p.Prime
    · have : (1 * lam p < 0) ↔ tau p < 0 := by rw [← lam_neg_iff hp, one_mul]
      simp only [hp, true_and, this]
    · simp [hp]
  rwa [e]

end RamanujanTau.TauSignsQuant
