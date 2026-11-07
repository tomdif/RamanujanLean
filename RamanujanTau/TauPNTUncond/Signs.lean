/-
# Unconditional sign changes of `τ(p)` over primes

**Theorem** (`tau_prime_sign_changes_uncond`): `τ(p) > 0` for infinitely many primes `p`, and
`τ(p) < 0` for infinitely many primes `p`.  No Deligne bound is assumed.

Proof.  Suppose `ε λ(p) ≥ 0` for all primes `p ≥ P` (`ε = ±1`).  Split the von Mangoldt function of
`Δ` as `ε Λ_Δ = a + b` with

* `a(p) = ε λ(p) log p ≥ 0` for primes `p ≥ P` (and `0` elsewhere),
* `b` = `ε ×` (the primes `p < P`, finitely many) `+ ε ×` (the prime powers `p^k`, `k ≥ 2`).

`b` converges absolutely at `s = 5/8` (`summable_vH_58`: `k = 2` by Rankin, `k ≥ 3` by Weil
`|A_k| ≪ p^{11k/40}`).  `L(s) = L(Δ, s + 11/2)` is entire and `L(σ) > 0` for real `σ`
(`HeckeL.tauL_pos`: the Mellin transform of `Δ(iy) > 0`), and `ε(−L'/L) = ∑ a n^{−s} + ∑ b n^{−s}`
on `Re s > 1`.  Landau's theorem (`Landau.landau_abscissa`) gives that `∑ a(n) n^{−s}` converges
for `Re s > 5/8`, so `∑_{p ≥ P} |λ(p)| log p · p^{−29/40} < ∞`.  With Weil, `λ(p)² /p ≤
C |λ(p)| p^{11/40 − 1}`, hence `∑_p λ(p)²/p < ∞`, contradicting `Weil.not_summable_lam_sq`.
-/
import RamanujanTau.TauPNTUncond.Weil
import RamanujanTau.TauPNTUncond.Landau
import RamanujanTau.TauPNT.Signs

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT RamanujanTau.HeckeL

/-- The higher prime-power part of `Λ_Δ`. -/
noncomputable def vHi (n : ℕ) : ℝ := if n.Prime then 0 else vM n

lemma vHi_zero_of_not {n : ℕ} (h : n ∉ Set.range ppow2) : vHi n = 0 := by
  unfold vHi
  split_ifs with hp
  · rfl
  by_cases hpp : IsPrimePow n
  · exfalso
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
    · exact hp (by simpa using hp')
    · exact h ⟨(⟨p, hp'⟩, k - 2), by simp only [ppow2]; congr 1; omega⟩
  · exact vM_of_not hpp

lemma vHi_ppow2 (q : Nat.Primes × ℕ) : vHi (ppow2 q) = AA q.1 (q.2 + 2) * Real.log q.1 := by
  obtain ⟨p, j⟩ := q
  have hp := p.2
  simp only [ppow2, vHi]
  rw [if_neg (Nat.Prime.not_prime_pow' (by omega)), show j + 2 = (j + 1) + 1 by ring, vM_pow hp]

set_option maxHeartbeats 800000 in
/-- **The prime powers `p^k`, `k ≥ 2`, of `Λ_Δ` converge absolutely at `s = 5/8`** (Rankin + Weil). -/
theorem summable_vH_58 : LSeriesSummable (fun n => (vHi n : ℂ)) ((5 / 8 : ℝ) : ℂ) := by
  obtain ⟨C, hC1, hC⟩ := weil_AA
  set u0 : ℝ := (2 : ℝ) ^ (-(7 / 20 : ℝ))
  have hu0 : 0 < u0 := Real.rpow_pos_of_pos (by norm_num) _
  have hu01 : u0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set Nb : Nat.Primes × ℕ → ℝ := fun q =>
    (if q.2 = 0 then 40 * (lam q.1 ^ 2 * (q.1 : ℝ) ^ (-(49 / 40 : ℝ))) +
      80 * (q.1 : ℝ) ^ (-(49 / 40 : ℝ)) else 0) +
    (80 * C / u0) * (q.1 : ℝ) ^ (-(41 / 40 : ℝ)) * u0 ^ q.2
  have hNb : Summable Nb := by
    refine Summable.add (summable_single_slot (fun p : Nat.Primes =>
      40 * (lam p ^ 2 * (p : ℝ) ^ (-(49 / 40 : ℝ))) + 80 * (p : ℝ) ^ (-(49 / 40 : ℝ)))
      (((summable_lam_sq (a := 49 / 40) (by norm_num)).mul_left _).add
        ((summable_primes_rpow (a := 49 / 40) (by norm_num)).mul_left _)) 0) ?_
    refine Summable.mul_of_nonneg
      (f := fun p : Nat.Primes => (80 * C / u0) * (p : ℝ) ^ (-(41 / 40 : ℝ)))
      (g := fun k : ℕ => u0 ^ k) ((summable_primes_rpow (a := 41 / 40) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one hu0.le hu01) ?_ ?_
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  have hbound : ∀ q : Nat.Primes × ℕ,
      ‖term (fun n => (vHi n : ℂ)) ((5 / 8 : ℝ) : ℂ) (ppow2 q)‖ ≤ Nb q := by
    rintro ⟨p, j⟩
    have hp := p.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlog : Real.log p ≤ 40 * (p : ℝ) ^ (1 / 40 : ℝ) := by
      have := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 40)
      linarith [show (p : ℝ) ^ (1 / 40 : ℝ) / (1 / 40) = 40 * (p : ℝ) ^ (1 / 40 : ℝ) by ring]
    set P58 : ℝ := (p : ℝ) ^ (5 / 8 : ℝ)
    have hP58 : 0 < P58 := Real.rpow_pos_of_pos hp0 _
    have hnorm : ‖term (fun n => (vHi n : ℂ)) ((5 / 8 : ℝ) : ℂ) (ppow2 (p, j))‖ =
        |AA p (j + 2)| * Real.log p / P58 ^ (j + 2) := by
      rw [norm_term_eq, if_neg (by simp only [ppow2]; exact pow_ne_zero _ hp.ne_zero),
        Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, vHi_ppow2, abs_mul,
        abs_of_nonneg hlog0]
      congr 1
      simp only [ppow2, P58]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        ← Real.rpow_mul hp0.le, mul_comm]
    rw [hnorm]
    have hNb0 : 0 ≤ (80 * C / u0) * (p : ℝ) ^ (-(41 / 40 : ℝ)) * u0 ^ j := by positivity
    simp only [Nb]
    rcases j with _ | j
    · rw [if_pos rfl]
      have hA : |AA p (0 + 2)| ≤ lam p ^ 2 + 2 := by
        rw [show 0 + 2 = 2 by rfl, AA_two, abs_le]; constructor <;> nlinarith [sq_nonneg (lam p)]
      have e : (p : ℝ) ^ (1 / 40 : ℝ) / P58 ^ (0 + 2) = (p : ℝ) ^ (-(49 / 40 : ℝ)) := by
        simp only [P58]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_sub hp0]; norm_num
      calc |AA p (0 + 2)| * Real.log p / P58 ^ (0 + 2)
          ≤ (lam p ^ 2 + 2) * (40 * (p : ℝ) ^ (1 / 40 : ℝ)) / P58 ^ (0 + 2) := by
            gcongr
        _ = 40 * (lam p ^ 2 + 2) * ((p : ℝ) ^ (1 / 40 : ℝ) / P58 ^ (0 + 2)) := by ring
        _ = 40 * (lam p ^ 2 * (p : ℝ) ^ (-(49 / 40 : ℝ))) + 80 * (p : ℝ) ^ (-(49 / 40 : ℝ)) := by
            rw [e]; ring
        _ ≤ _ := by linarith
    · rw [if_neg (by omega), zero_add]
      set u : ℝ := rho p / P58
      have hu : u = (p : ℝ) ^ (-(7 / 20 : ℝ)) := by
        simp only [u, rho, P58]; rw [← Real.rpow_sub hp0]; norm_num
      have hu0' : 0 ≤ u := by rw [hu]; positivity
      have huu0 : u ≤ u0 := by
        rw [hu]; exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      have hu3 : (p : ℝ) ^ (1 / 40 : ℝ) * u ^ 3 = (p : ℝ) ^ (-(41 / 40 : ℝ)) := by
        rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]; norm_num
      have hA := hC hp (j + 1 + 2)
      have hAu : |AA p (j + 1 + 2)| / P58 ^ (j + 1 + 2) ≤ 2 * C * u ^ (j + 1 + 2) := by
        rw [div_le_iff₀ (by positivity)]
        calc |AA p (j + 1 + 2)| ≤ 2 * C * rho p ^ (j + 1 + 2) := hA
          _ = 2 * C * u ^ (j + 1 + 2) * P58 ^ (j + 1 + 2) := by
            simp only [u]; rw [div_pow]; field_simp
      have huj : u ^ (j + 1 + 2) = u ^ 3 * u ^ j := by ring
      calc |AA p (j + 1 + 2)| * Real.log p / P58 ^ (j + 1 + 2)
          = (|AA p (j + 1 + 2)| / P58 ^ (j + 1 + 2)) * Real.log p := by ring
        _ ≤ (2 * C * u ^ (j + 1 + 2)) * (40 * (p : ℝ) ^ (1 / 40 : ℝ)) :=
            mul_le_mul hAu hlog hlog0 (by positivity)
        _ = 80 * C * ((p : ℝ) ^ (1 / 40 : ℝ) * u ^ 3) * u ^ j := by rw [huj]; ring
        _ ≤ 80 * C * ((p : ℝ) ^ (1 / 40 : ℝ) * u ^ 3) * u0 ^ j := by
            gcongr
        _ = (80 * C / u0) * (p : ℝ) ^ (-(41 / 40 : ℝ)) * u0 ^ (j + 1) := by
            rw [hu3, pow_succ]; field_simp
  have hs : Summable fun q : Nat.Primes × ℕ =>
      term (fun n => (vHi n : ℂ)) ((5 / 8 : ℝ) : ℂ) (ppow2 q) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hNb)
  refine (ppow2_injective.summable_iff (fun n hn => ?_)).mp hs
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · rw [term_of_ne_zero h0, vHi_zero_of_not hn]; simp

/-- Under `ε λ(p) ≥ 0` for `p ≥ P`: the nonnegative part `a`. -/
noncomputable def aPart (ε : ℝ) (P n : ℕ) : ℝ := if n.Prime ∧ P ≤ n then ε * vM n else 0

/-- The rest: `b = ε (Λ_Δ on primes `< P` + higher prime powers)`. -/
noncomputable def bPart (ε : ℝ) (P n : ℕ) : ℝ :=
  ε * ((if n.Prime ∧ n < P then vM n else 0) + vHi n)

lemma decomp (ε : ℝ) (P n : ℕ) : ε * vM n = aPart ε P n + bPart ε P n := by
  unfold aPart bPart vHi
  by_cases hp : n.Prime
  · by_cases hP : P ≤ n
    · rw [if_pos ⟨hp, hP⟩, if_neg (fun h => by omega), if_pos hp]; ring
    · rw [if_neg (fun h => hP h.2), if_pos ⟨hp, by omega⟩, if_pos hp]; ring
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1), if_neg hp]; ring

lemma summable_bPart (ε : ℝ) (P : ℕ) :
    LSeriesSummable (fun n => (bPart ε P n : ℂ)) ((5 / 8 : ℝ) : ℂ) := by
  have hfin : LSeriesSummable (fun n => ((if n.Prime ∧ n < P then vM n else 0 : ℝ) : ℂ))
      ((5 / 8 : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.range P) fun n hn => ?_
    have : ¬ (n.Prime ∧ n < P) := fun h => hn (Finset.mem_range.mpr h.2)
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · rw [term_of_ne_zero h0, if_neg this]; simp
  have h := (hfin.add summable_vH_58).smul (ε : ℂ)
  refine h.congr fun n => ?_
  simp only [bPart, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LSeries.term_add, term_smul]
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · simp only [term_of_ne_zero h0]; push_cast; ring

/-- **No eventual sign for `λ(p)`, unconditionally.** -/
theorem not_eventually_signed_uncond (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (P : ℕ)
    (h : ∀ p : ℕ, p.Prime → P ≤ p → 0 ≤ ε * lam p) : False := by
  have hεε : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set a := aPart ε P
  set b := bPart ε P
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    simp only [a, aPart]
    split_ifs with hn
    · rw [vM_prime hn.1, ← mul_assoc]
      exact mul_nonneg (h n hn.1 hn.2)
        (Real.log_nonneg (by exact_mod_cast hn.1.one_lt.le))
    · exact le_rfl
  have hb : abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ ((5 / 8 : ℝ) : EReal) := by
    have := (summable_bPart ε P).abscissaOfAbsConv_le
    simpa using this
  have hsplit : ((ε : ℂ)) • (fun n => (vM n : ℂ)) = (fun n => (a n : ℂ)) + fun n => (b n : ℂ) := by
    funext n; simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, a, b]
    rw [← Complex.ofReal_mul, decomp ε P n]; push_cast; ring
  have hbs : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (b n : ℂ)) s := fun s hs =>
    (summable_bPart ε P).of_re_le_re (by simp; linarith)
  have has : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (a n : ℂ)) s := by
    intro s hs
    have h1 := (LSeriesSummable_vM hs).smul (ε : ℂ)
    rw [hsplit] at h1
    have := h1.sub (hbs s hs)
    simpa using this
  have ha1 : abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ 1 :=
    abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => has _ (by simpa using hy)
  have hLσ : ∀ σ : ℝ, (5 / 8 : ℝ) < σ → σ ≤ 1 → Lnorm σ ≠ 0 := by
    intro σ hσ _ h0
    have hpos := (HeckeL.tauL_pos (σ := σ + 11 / 2) (by linarith)).2
    have e : ((σ + 11 / 2 : ℝ) : ℂ) = (σ : ℂ) + 11 / 2 := by push_cast; ring
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
  -- convergence at `29/40`
  have hconv : LSeriesSummable (fun n => (a n : ℂ)) ((29 / 40 : ℝ) : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (hab.trans_lt (by simp only [Complex.ofReal_re]; exact_mod_cast (by norm_num : (5 / 8 : ℝ) < 29 / 40)))
  have hreal : Summable fun n : ℕ => a n / (n : ℝ) ^ (29 / 40 : ℝ) := by
    refine hconv.norm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | h0
    · simp [a, aPart, Nat.not_prime_zero]
    · rw [norm_term_eq, if_neg h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
        Complex.ofReal_re]
  have hrealP : Summable fun p : Nat.Primes => a p / (p : ℝ) ^ (29 / 40 : ℝ) :=
    hreal.comp_injective Subtype.val_injective
  obtain ⟨C, hC1, hC⟩ := weil_uu
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set s : Finset Nat.Primes := (Finset.range P).subtype Nat.Prime
  set g : Nat.Primes → ℝ := fun p => C / Real.log 2 * (a p / (p : ℝ) ^ (29 / 40 : ℝ)) +
    (if p ∈ s then lam p ^ 2 * (p : ℝ)⁻¹ else 0)
  have hg : Summable g := (hrealP.mul_left _).add
    (summable_of_ne_finset_zero (s := s) fun p hp => by simp [hp])
  refine not_summable_lam_sq (Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hg)
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfirst : 0 ≤ C / Real.log 2 * (a p / (p : ℝ) ^ (29 / 40 : ℝ)) := by
    have := ha p; positivity
  by_cases hps : p ∈ s
  · simp only [g, if_pos hps]; linarith
  · simp only [g, if_neg hps, add_zero]
    have hPp : P ≤ (p : ℕ) := by
      by_contra hlt; push Not at hlt
      exact hps (Finset.mem_subtype.mpr (Finset.mem_range.mpr hlt))
    have hap : a p = |lam p| * Real.log p := by
      simp only [a, aPart, if_pos (⟨hp, hPp⟩ : (p : ℕ).Prime ∧ P ≤ p), vM_prime hp]
      have hε' := h p hp hPp
      rw [← mul_assoc, ← abs_of_nonneg hε', abs_mul, hεa, one_mul]
    have hlam : |lam p| ≤ C * rho p := by
      have := hC hp 1; rwa [pow_one] at this
    have hlog2 : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hρp : rho p * (p : ℝ)⁻¹ = (p : ℝ) ^ (-(29 / 40 : ℝ)) := by
      rw [rho, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
    rw [hap, div_eq_mul_inv (|lam p| * Real.log p), ← Real.rpow_neg hp0.le]
    calc lam p ^ 2 * (p : ℝ)⁻¹ = |lam p| * (|lam p| * (p : ℝ)⁻¹) := by rw [← sq_abs]; ring
      _ ≤ |lam p| * (C * rho p * (p : ℝ)⁻¹) := by gcongr
      _ = C * (|lam p| * (p : ℝ) ^ (-(29 / 40 : ℝ))) := by rw [mul_assoc C, hρp]; ring
      _ ≤ C * (|lam p| * (Real.log p / Real.log 2) * (p : ℝ) ^ (-(29 / 40 : ℝ))) := by
          gcongr
          have h1 : 1 ≤ Real.log p / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
          nlinarith [abs_nonneg (lam p)]
      _ = C / Real.log 2 * (|lam p| * Real.log p * (p : ℝ) ^ (-(29 / 40 : ℝ))) := by ring

/-- **`τ(p)` changes sign infinitely often over primes — unconditionally** (no Deligne). -/
theorem tau_prime_sign_changes_uncond :
    (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ 0 < tau p) ∧ (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ tau p < 0) := by
  constructor
  · intro N
    by_contra hcon
    push Not at hcon
    refine not_eventually_signed_uncond (-1) (Or.inr rfl) N fun p hp hNp => ?_
    have h1 : ¬ 0 < lam p := fun h => absurd ((lam_pos_iff hp).mp h) (not_lt.mpr (hcon p hNp hp))
    push Not at h1
    linarith
  · intro N
    by_contra hcon
    push Not at hcon
    refine not_eventually_signed_uncond 1 (Or.inl rfl) N fun p hp hNp => ?_
    have h1 : ¬ lam p < 0 := fun h => absurd ((lam_neg_iff hp).mp h) (not_lt.mpr (hcon p hNp hp))
    push Not at h1
    linarith

end RamanujanTau.TauPNTUncond
