/-
# Weil-type bounds at prime powers, and `∑_p λ(p)²/p = ∞` without Deligne

From the repository's unconditional Weil exponent `τ(n) = O(n^{23/4+ε})`
(`StepanovAS.tau_isBigO_23_4_unconditional`, `ε = 1/40`):

* `weil_uu`: `|λ(p^k)| = |τ(p^k)| p^{−11k/2} ≤ C ρ_p^k`, `ρ_p = p^{11/40}`, uniformly in `p, k`;
* `AA_add_two`: `A_{k+2}(p) = λ(p^{k+2}) − λ(p^k)` (Hecke), hence `weil_AA`: `|A_k(p)| ≤ 2C ρ_p^k`;
* `not_summable_lam_sq`: `∑_p λ(p)²/p = ∞`.  Proof: `‖ζ(2σ)R(σ)‖ = exp ∑ cR(n)n^{−σ}`, the
  prime powers `p^k`, `k ≥ 2`, contribute a bounded amount (`k = 2`: `A_2² ≤ 2λ⁴ + 8` and
  `λ² ≤ C²p^{11/20}` with Rankin's `∑ λ(p)²p^{−29/20} < ∞`; `k ≥ 3`: `A_k² ≤ 4C²p^{11k/20}`),
  while `ζ(2σ)R(σ) = KK(σ)/(σ−1)` blows up as `σ → 1⁺`.
-/
import RamanujanTau.TauPNTUncond.Edge
import RamanujanTau.StepanovAS.Main

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries Asymptotics
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT

/-- `ρ_p = p^{11/40}`. -/
noncomputable def rho (p : ℕ) : ℝ := (p : ℝ) ^ (11 / 40 : ℝ)

lemma rho_one_le {p : ℕ} (hp : p.Prime) : 1 ≤ rho p :=
  Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) (by norm_num)

lemma rho_pos {p : ℕ} (hp : p.Prime) : 0 < rho p := lt_of_lt_of_le one_pos (rho_one_le hp)

/-- A uniform bound `|τ(n)| ≤ C n^{231/40}` for all `n` (Weil, unconditional). -/
lemma tau_le_uniform : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    |(RamanujanTau.tau n : ℝ)| ≤ C * (n : ℝ) ^ (231 / 40 : ℝ) := by
  have h := StepanovAS.tau_isBigO_23_4_unconditional (1 / 40) (by norm_num)
  obtain ⟨C0, hC0⟩ := h.bound
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hC0
  set S : ℝ := ∑ n ∈ Finset.range N0, |(RamanujanTau.tau n : ℝ)|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|C0| + S + 1, by linarith [abs_nonneg C0], fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ (231 / 40 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  rcases lt_or_ge n N0 with hlt | hge
  · have : |(RamanujanTau.tau n : ℝ)| ≤ S :=
      Finset.single_le_sum (f := fun n => |(RamanujanTau.tau n : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hlt)
    nlinarith [abs_nonneg C0]
  · have h1 := hN0 n hge
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at h1
    have e : (23 / 4 : ℝ) + 1 / 40 = 231 / 40 := by norm_num
    rw [e] at h1
    have : C0 * (n : ℝ) ^ (231 / 40 : ℝ) ≤ |C0| * (n : ℝ) ^ (231 / 40 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith

/-- **`|λ(p^k)| ≤ C ρ_p^k`** uniformly (Weil, unconditional). -/
lemma weil_uu : ∃ C : ℝ, 1 ≤ C ∧ ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, |uu p k| ≤ C * rho p ^ k := by
  obtain ⟨C, hC1, hC⟩ := tau_le_uniform
  refine ⟨C, hC1, fun {p} hp k => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h := hC (p ^ k) (Nat.one_le_pow _ _ hp.pos)
  have hr : 0 < rr p := Real.rpow_pos_of_pos hp0 _
  have e1 : (((p ^ k : ℕ) : ℝ)) ^ (231 / 40 : ℝ) = ((p : ℝ) ^ (231 / 40 : ℝ)) ^ k := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      ← Real.rpow_mul hp0.le, mul_comm]
  have e2 : (p : ℝ) ^ (231 / 40 : ℝ) * rr p = rho p := by
    rw [rr, rho, ← Real.rpow_add hp0]; norm_num
  rw [uu, abs_mul, abs_of_pos (pow_pos hr k)]
  calc |(RamanujanTau.tau (p ^ k) : ℝ)| * rr p ^ k ≤ C * ((p : ℝ) ^ (231 / 40 : ℝ)) ^ k * rr p ^ k := by
        rw [← e1]; exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = C * rho p ^ k := by rw [mul_assoc, ← mul_pow, e2]

/-- Hecke: `A_{k+2}(p) = λ(p^{k+2}) − λ(p^k)`. -/
lemma AA_add_two {p : ℕ} (hp : p.Prime) (k : ℕ) : AA p (k + 2) = uu p (k + 2) - uu p k := by
  have key : ∀ k, AA p (k + 2) = uu p (k + 2) - uu p k ∧
      AA p (k + 3) = uu p (k + 3) - uu p (k + 1) := by
    intro k
    induction k with
    | zero =>
      have h2 := uu_rec hp 0
      have h3 := uu_rec hp 1
      simp only [uu_zero, zero_add] at h2 h3
      have h1 : uu p 1 = lam p := rfl
      refine ⟨?_, ?_⟩
      · rw [AA_two, h2, h1, uu_zero]; ring
      · have e : AA p 3 = lam p * AA p 2 - AA p 1 := rfl
        rw [e, AA_two, AA_one, h3, h2, h1]; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e : AA p (k + 1 + 3) = lam p * AA p (k + 3) - AA p (k + 2) := rfl
      rw [e, ih.1, ih.2, show k + 1 + 3 = k + 2 + 2 by ring, uu_rec hp (k + 2),
        show k + 1 + 1 = k + 2 by ring, uu_rec hp k]
      ring
  exact (key k).1

/-- **`|A_k(p)| ≤ 2C ρ_p^k`** for all `k` (Weil). -/
lemma weil_AA : ∃ C : ℝ, 1 ≤ C ∧ ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, |AA p k| ≤ 2 * C * rho p ^ k := by
  obtain ⟨C, hC1, hC⟩ := weil_uu
  refine ⟨C, hC1, fun {p} hp k => ?_⟩
  have hρ := rho_one_le hp
  have hρk : ∀ j, 1 ≤ rho p ^ j := fun j => one_le_pow₀ hρ
  rcases k with _ | _ | k
  · have : AA p 0 = 2 := rfl
    rw [this, abs_two]; nlinarith [hρk 0]
  · show |AA p 1| ≤ 2 * C * rho p ^ 1
    rw [AA_one]
    have := hC hp 1
    have h1 : uu p 1 = lam p := rfl
    rw [h1] at this
    nlinarith [hρk 1]
  · rw [AA_add_two hp]
    have h1 := hC hp (k + 2)
    have h2 := hC hp k
    have hm : rho p ^ k ≤ rho p ^ (k + 2) := pow_le_pow_right₀ hρ (by omega)
    calc |uu p (k + 2) - uu p k| ≤ |uu p (k + 2)| + |uu p k| := abs_sub _ _
      _ ≤ C * rho p ^ (k + 2) + C * rho p ^ k := add_le_add h1 h2
      _ ≤ 2 * C * rho p ^ (k + 2) := by nlinarith

/-- `ρ_p² / p = p^{−9/20}`. -/
lemma rho_sq_div {p : ℕ} (hp : p.Prime) : rho p ^ 2 * (p : ℝ)⁻¹ = (p : ℝ) ^ (-(9 / 20 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [rho, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_neg_one, ← Real.rpow_add hp0]
  norm_num

lemma summable_single_slot (f : Nat.Primes → ℝ) (hf : Summable f) (j : ℕ) :
    Summable fun q : Nat.Primes × ℕ => if q.2 = j then f q.1 else 0 := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p, j)) := fun a b h => by
    simpa using h
  refine (hinj.summable_iff (fun q hq => ?_)).mp ?_
  · split_ifs with h
    · exact absurd ⟨q.1, by ext <;> simp [h]⟩ hq
    · rfl
  · simpa [Function.comp_def] using hf

lemma term_cR_ppow_real (σ : ℝ) (q : Nat.Primes × ℕ) :
    term (fun n => (cR n : ℂ)) (σ : ℂ) (ppow q) =
      ((AA q.1 (q.2 + 1) ^ 2 / (q.2 + 1 : ℕ) * ((q.1 : ℝ) ^ (-σ)) ^ (q.2 + 1) : ℝ) : ℂ) := by
  rw [term_cR_ppow, show (((q.1 : ℕ) : ℂ)) ^ (-(σ : ℂ)) = ((((q.1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl]
  push_cast
  ring

/-- The majorant for the `log (ζ(2σ)R(σ))` coefficients on `σ ≥ 1`. -/
noncomputable def Mmaj (C r0 : ℝ) (q : Nat.Primes × ℕ) : ℝ :=
    (if q.2 = 0 then lam q.1 ^ 2 * (q.1 : ℝ)⁻¹ else 0) +
    (if q.2 = 1 then 32 * C ^ 2 * (lam q.1 ^ 2 * (q.1 : ℝ) ^ (-(29 / 20 : ℝ))) +
        8 * (q.1 : ℝ) ^ (-(2 : ℝ)) else 0) +
    (16 * C ^ 2 / r0 ^ 2) * (q.1 : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ q.2

lemma summable_Mmaj (hS : Summable fun p : Nat.Primes => lam p ^ 2 * (p : ℝ)⁻¹) (C : ℝ) {r0 : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 < 1) : Summable (Mmaj C r0) := by
  unfold Mmaj
  refine Summable.add (Summable.add
    (summable_single_slot (fun p : Nat.Primes => lam p ^ 2 * (p : ℝ)⁻¹) hS 0)
    (summable_single_slot (fun p : Nat.Primes => 32 * C ^ 2 * (lam p ^ 2 *
      (p : ℝ) ^ (-(29 / 20 : ℝ))) + 8 * (p : ℝ) ^ (-(2 : ℝ))) ?_ 1)) ?_
  · exact ((summable_lam_sq (a := 29 / 20) (by norm_num)).mul_left _).add
      ((summable_primes_rpow (a := 2) (by norm_num)).mul_left _)
  · refine Summable.mul_of_nonneg
      (f := fun p : Nat.Primes => (16 * C ^ 2 / r0 ^ 2) * (p : ℝ) ^ (-(27 / 20 : ℝ)))
      (g := fun k : ℕ => r0 ^ k) ((summable_primes_rpow (a := 27 / 20) (by norm_num)).mul_left _)
      (summable_geometric_of_lt_one hr0.le hr01) ?_ ?_
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity

set_option maxHeartbeats 800000 in
lemma Mmaj_bound {C : ℝ} (hC1 : 1 ≤ C)
    (hC : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, |AA p k| ≤ 2 * C * rho p ^ k) (σ : ℝ) (hσ : 1 ≤ σ)
    (q : Nat.Primes × ℕ) :
    AA q.1 (q.2 + 1) ^ 2 / (q.2 + 1 : ℕ) * ((q.1 : ℝ) ^ (-σ)) ^ (q.2 + 1) ≤
      Mmaj C ((2 : ℝ) ^ (-(9 / 20 : ℝ))) q := by
  set r0 : ℝ := (2 : ℝ) ^ (-(9 / 20 : ℝ))
  have hr0 : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨p, k⟩ := q
  have hp := p.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hip : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hy : (p : ℝ) ^ (-σ) ≤ (p : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hy0 : 0 ≤ (p : ℝ) ^ (-σ) := by positivity
  have hT : rho p ^ 2 * (p : ℝ)⁻¹ ≤ r0 := by
    rw [rho_sq_div hp]; exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
  have hT0 : 0 ≤ rho p ^ 2 * (p : ℝ)⁻¹ := by have := rho_pos hp; positivity
  have hM1 : 0 ≤ (if k = 0 then lam p ^ 2 * (p : ℝ)⁻¹ else 0) := by split_ifs <;> positivity
  have hM2 : 0 ≤ (if k = 1 then 32 * C ^ 2 * (lam p ^ 2 * (p : ℝ) ^ (-(29 / 20 : ℝ))) +
      8 * (p : ℝ) ^ (-(2 : ℝ)) else 0) := by split_ifs <;> positivity
  have hM3 : 0 ≤ (16 * C ^ 2 / r0 ^ 2) * (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ k := by positivity
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
  have hstep : AA p (k + 1) ^ 2 / (k + 1 : ℕ) * ((p : ℝ) ^ (-σ)) ^ (k + 1) ≤
      AA p (k + 1) ^ 2 * (p : ℝ)⁻¹ ^ (k + 1) :=
    mul_le_mul (div_le_self (sq_nonneg _) hk1) (pow_le_pow_left₀ hy0 hy _) (by positivity)
      (sq_nonneg _)
  refine hstep.trans ?_
  simp only [Mmaj]
  rcases k with _ | _ | k
  · rw [if_pos rfl, if_neg (by norm_num)]
    simp only [zero_add, pow_one, AA_one]
    linarith
  · simp only [one_ne_zero, if_false, if_true, zero_add]
    rw [show 1 + 1 = 2 by rfl, AA_two]
    have hl := (hC hp 1)
    rw [AA_one, pow_one] at hl
    have hl2 : lam p ^ 2 ≤ 4 * C ^ 2 * rho p ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hl 2
      rw [sq_abs] at this; nlinarith
    have e29 : rho p ^ 2 * (p : ℝ)⁻¹ ^ 2 = (p : ℝ) ^ (-(29 / 20 : ℝ)) := by
      rw [sq (p : ℝ)⁻¹, ← mul_assoc, rho_sq_div hp, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
    have e2 : (p : ℝ)⁻¹ ^ 2 = (p : ℝ) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    have h4 : (lam p ^ 2 - 2) ^ 2 ≤ 2 * lam p ^ 2 * lam p ^ 2 + 8 := by nlinarith [sq_nonneg (lam p)]
    calc (lam p ^ 2 - 2) ^ 2 * (p : ℝ)⁻¹ ^ 2 ≤ (2 * lam p ^ 2 * lam p ^ 2 + 8) * (p : ℝ)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ (2 * lam p ^ 2 * (4 * C ^ 2 * rho p ^ 2) + 8) * (p : ℝ)⁻¹ ^ 2 := by
          gcongr
      _ = 8 * C ^ 2 * (lam p ^ 2 * (rho p ^ 2 * (p : ℝ)⁻¹ ^ 2)) + 8 * (p : ℝ)⁻¹ ^ 2 := by ring
      _ ≤ 32 * C ^ 2 * (lam p ^ 2 * (p : ℝ) ^ (-(29 / 20 : ℝ))) + 8 * (p : ℝ) ^ (-(2 : ℝ)) +
          (16 * C ^ 2 / r0 ^ 2) * (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ (0 + 1) := by
          rw [e29, e2]
          have : 0 ≤ lam p ^ 2 * (p : ℝ) ^ (-(29 / 20 : ℝ)) := by positivity
          have : 0 ≤ (16 * C ^ 2 / r0 ^ 2) * (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ (0 + 1) := by
            positivity
          nlinarith
  · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, if_false, zero_add]
    have hA := hC hp (k + 1 + 1 + 1)
    have hA2 : AA p (k + 1 + 1 + 1) ^ 2 ≤ 4 * C ^ 2 * (rho p ^ 2) ^ (k + 3) := by
      have := pow_le_pow_left₀ (abs_nonneg _) hA 2
      rw [sq_abs] at this
      calc AA p (k + 1 + 1 + 1) ^ 2 ≤ (2 * C * rho p ^ (k + 1 + 1 + 1)) ^ 2 := this
        _ = 4 * C ^ 2 * (rho p ^ 2) ^ (k + 3) := by ring
    set T := rho p ^ 2 * (p : ℝ)⁻¹
    have hT3 : T ^ 3 = (p : ℝ) ^ (-(27 / 20 : ℝ)) := by
      simp only [T]; rw [rho_sq_div hp, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    have hTk : T ^ (k + 3) ≤ (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ k := by
      rw [pow_add, hT3, mul_comm (T ^ k)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hT k) (by positivity)
    calc AA p (k + 1 + 1 + 1) ^ 2 * (p : ℝ)⁻¹ ^ (k + 1 + 1 + 1) ≤ 4 * C ^ 2 * (rho p ^ 2) ^ (k + 3) *
          (p : ℝ)⁻¹ ^ (k + 3) := mul_le_mul_of_nonneg_right hA2 (by positivity)
      _ = 4 * C ^ 2 * T ^ (k + 3) := by simp only [T]; rw [mul_pow]; ring
      _ ≤ 4 * C ^ 2 * ((p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ k) := by gcongr
      _ ≤ (16 * C ^ 2 / r0 ^ 2) * (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ (k + 1 + 1) := by
          rw [show r0 ^ (k + 1 + 1) = r0 ^ k * r0 ^ 2 by ring]
          field_simp
          have : 0 ≤ C ^ 2 * (p : ℝ) ^ (-(27 / 20 : ℝ)) * r0 ^ k := by positivity
          nlinarith

/-- **`∑_p λ(p)²/p = ∞`** (unconditional; Rankin–Selberg pole plus Weil at prime powers). -/
theorem not_summable_lam_sq :
    ¬ Summable fun p : Nat.Primes => lam p ^ 2 * (p : ℝ)⁻¹ := by
  intro hS
  obtain ⟨C, hC1, hC⟩ := weil_AA
  set r0 : ℝ := (2 : ℝ) ^ (-(9 / 20 : ℝ))
  have hr0 : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  have hr01 : r0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hM : Summable (Mmaj C r0) := summable_Mmaj hS C hr0 hr01
  have hbound : ∀ σ : ℝ, 1 ≤ σ → ∀ q : Nat.Primes × ℕ,
      AA q.1 (q.2 + 1) ^ 2 / (q.2 + 1 : ℕ) * ((q.1 : ℝ) ^ (-σ)) ^ (q.2 + 1) ≤ Mmaj C r0 q :=
    fun σ hσ q => Mmaj_bound hC1 hC σ hσ q
  set M := Mmaj C r0
  -- `‖HH σ‖ ≤ exp B` for `σ > 1`
  set B : ℝ := ∑' q, M q
  have hHH : ∀ σ : ℝ, 1 < σ → ‖HH σ‖ ≤ Real.exp B := by
    intro σ hσ
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    have hsum := (LSeriesSummable_cR hs).LSeriesHasSum
    have hprod : HasSum (term (fun n => (cR n : ℂ)) σ ∘ ppow)
        (LSeries (fun n => (cR n : ℂ)) σ) :=
      (ppow_injective.hasSum_iff (fun _ hn => term_cR_zero_of_not hn)).mpr hsum
    have hre := Complex.hasSum_re hprod
    have hle : (LSeries (fun n => (cR n : ℂ)) σ).re ≤ B := by
      refine hasSum_le (fun q => ?_) hre hM.hasSum
      simp only [Function.comp_apply]
      rw [term_cR_ppow_real, Complex.ofReal_re]
      exact hbound σ hσ.le q
    rw [HH_exp hs, Complex.norm_exp]
    exact Real.exp_le_exp.mpr hle
  -- but `‖HH(1+h)‖ ≥ ‖KK 1‖/(2h)`
  have hK1 : 0 < ‖KK 1‖ := norm_pos_iff.mpr KK_one_ne
  have hcK : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ‖KK 1‖ / 2 < ‖KK (1 + 1 * (h : ℂ))‖ := by
    have := ((differentiableAt_KK one_ne_zero).continuousAt.tendsto.comp
      (tendsto_path 1 1)).norm
    exact this.eventually_const_lt (by linarith)
  have hsmallE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (‖KK 1‖ / (2 * Real.exp B)) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨h, hk, hh⟩ := (hcK.and hsmallE).exists
  have hpos : 0 < h := hh.1
  have hs0 : (1 : ℂ) + 1 * (h : ℂ) ≠ 0 := by
    intro hh0; have := congrArg Complex.re hh0; simp at this; linarith
  have hs1 : (1 : ℂ) + 1 * (h : ℂ) ≠ 1 := by
    intro hh0; have := congrArg Complex.re hh0; simp at this; linarith
  have hK := KK_eq hs0 hs1
  rw [show (1 : ℂ) + 1 * (h : ℂ) - 1 = (h : ℂ) by ring] at hK
  have hnorm : ‖KK (1 + 1 * (h : ℂ))‖ = h * ‖HH (1 + 1 * (h : ℂ))‖ := by
    rw [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hH := hHH (1 + h) (by linarith)
  rw [show (((1 + h : ℝ)) : ℂ) = 1 + 1 * (h : ℂ) by push_cast; ring] at hH
  have h2 : h * Real.exp B < ‖KK 1‖ / 2 := by
    have := hh.2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have : ‖KK 1‖ / 2 < h * Real.exp B := by
    calc ‖KK 1‖ / 2 < ‖KK (1 + 1 * (h : ℂ))‖ := hk
      _ = h * ‖HH (1 + 1 * (h : ℂ))‖ := hnorm
      _ ≤ h * Real.exp B := mul_le_mul_of_nonneg_left hH hpos.le
  linarith

end RamanujanTau.TauPNTUncond
