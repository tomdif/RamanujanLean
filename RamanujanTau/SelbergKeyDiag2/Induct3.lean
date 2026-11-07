/-
# M3 step 2e: the peeling step and the induction (`twisted_eval`)

For all coprime `h, k ≥ 1`, uniformly in `u`, `0 < |v| ≤ 1`, `α > 0`:

    |Σ_r λ(hr)λ(kr) r^{−1+iv} W̃(αr²) − Mn(h,k)(α)| ≤ Z₀ M^{ω(hk)} (hk)² · Er(α/T(u)T(u+v)).

Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Induct2

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset PowerSeries RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open RamanujanTau.SelbergKey (NpC DpC rhoC)
open scoped Real

theorem Inv_peel {Z : ℝ} (hZ : 0 ≤ Z) {p a h' k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hh' : 1 ≤ h')
    (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k)
    (hs : Summable fun j : ℕ => |gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j)
    (H : Inv Z h' k) : Inv (Z * Gp p a) (p ^ a * h') k := by
  intro u v α hα hv0 hv
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  set x : ℂ := (p : ℂ) ^ (-(1 - (v : ℂ) * I)) with hx
  have hs1 : (1 - (v : ℂ) * I).re = 1 := by simp
  have hxn : ‖x‖ = (p : ℝ)⁻¹ := norm_p_cpow hp hs1
  set r := α / TT u v with hr
  have hr0 : 0 ≤ r := (div_pos hα (TT_pos u v)).le
  set b : ℕ → ℂ := fun j => ((gseq p a j : ℝ) : ℂ) * x ^ j * Bs u v h' k (α * (p : ℝ) ^ (2 * j))
  set m : ℕ → ℂ := fun j => ((gseq p a j : ℝ) : ℂ) * x ^ j * Mn u v h' k (α * (p : ℝ) ^ (2 * j))
  have hm : HasSum m (Mn u v (p ^ a * h') k α) := hasSum_Mn_peel u v hp ha hh' hph hα
  have hbd : ∀ j, ‖b j - m j‖ ≤ (Z * Er r) * (|gseq p a j| * ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j) := by
    intro j
    have e : b j - m j = ((gseq p a j : ℝ) : ℂ) * x ^ j *
        (Bs u v h' k (α * (p : ℝ) ^ (2 * j)) - Mn u v h' k (α * (p : ℝ) ^ (2 * j))) := by
      simp only [b, m]; ring
    rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, hxn]
    have h1 := H u v (α * (p : ℝ) ^ (2 * j)) (by positivity) hv0 hv
    have hrj : α * (p : ℝ) ^ (2 * j) / TT u v = r * (p : ℝ) ^ (2 * j) := by rw [hr]; ring
    rw [hrj] at h1
    have h2 := Er_scale hr0 hp1 j
    have h3 : ((p : ℝ)⁻¹) ^ j * ((p : ℝ) ^ (1 / 3 : ℝ)) ^ j = ((p : ℝ) ^ (-(2 / 3 : ℝ))) ^ j := by
      rw [← mul_pow]; congr 1
      rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
    calc |gseq p a j| * ((p : ℝ)⁻¹) ^ j *
          ‖Bs u v h' k (α * (p : ℝ) ^ (2 * j)) - Mn u v h' k (α * (p : ℝ) ^ (2 * j))‖
        ≤ |gseq p a j| * ((p : ℝ)⁻¹) ^ j * (Z * ((((p : ℝ) ^ (1 / 3 : ℝ)) ^ j) * Er r)) := by
          gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hZ)
      _ = (Z * Er r) * (|gseq p a j| * (((p : ℝ)⁻¹) ^ j * ((p : ℝ) ^ (1 / 3 : ℝ)) ^ j)) := by ring
      _ = _ := by rw [h3]
  have hd : Summable fun j => b j - m j := Summable.of_norm_bounded (hs.mul_left (Z * Er r)) hbd
  have hb : Summable b := (hd.add hm.summable).congr fun j => by ring
  have hpeel : Bs u v (p ^ a * h') k α = ∑' j, b j := Bs_peel u v hp hph hpk hα
  rw [hpeel, ← hm.tsum_eq, ← hb.tsum_sub hm.summable]
  refine (tsum_of_norm_bounded ((hs.mul_left (Z * Er r)).hasSum) hbd).trans (le_of_eq ?_)
  rw [tsum_mul_left]; unfold Gp; ring

lemma card_pf_peel {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    (p ^ a * m).primeFactors.card = m.primeFactors.card + 1 := by
  rw [pf_peel hp ha hm, Finset.card_insert_of_notMem (p_notMem hpm)]

/-- **The twisted sum for all coprime `(h, k)`** (level 1). -/
theorem twisted_eval : ∃ Z₀ M : ℝ, 0 ≤ Z₀ ∧ 1 ≤ M ∧ ∀ h k : ℕ, 1 ≤ h → 1 ≤ k → h.Coprime k →
    Inv (Z₀ * M ^ (h * k).primeFactors.card * ((h * k : ℕ) : ℝ) ^ 2) h k := by
  obtain ⟨Z₀, hZ₀, hbase⟩ := Inv_base
  obtain ⟨M, hM1, hM⟩ := Gp_bound
  refine ⟨Z₀, M, hZ₀, hM1, ?_⟩
  set F : ℕ → ℕ → ℝ := fun h k => Z₀ * M ^ (h * k).primeFactors.card * ((h * k : ℕ) : ℝ) ^ 2 with hF
  have hF0 : ∀ h k, 0 ≤ F h k := fun h k => by simp only [hF]; positivity
  have hFc : ∀ h k, F h k = F k h := fun h k => by simp only [hF]; rw [mul_comm h k]
  suffices H : ∀ n : ℕ, ∀ h k : ℕ, h * k = n → 1 ≤ h → 1 ≤ k → h.Coprime k → Inv (F h k) h k from
    fun h k hh hk hc => H _ h k rfl hh hk hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  -- peeling a prime from the first argument
  have hcase : ∀ h k : ℕ, h * k = n → 1 < h → 1 ≤ k → h.Coprime k → Inv (F h k) h k := by
    intro h k hn hh hk hc
    have hh0 : h ≠ 0 := by omega
    set p := h.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    set a := h.factorization p with hadef
    set h' := h / p ^ a with hh'def
    have hpa : p ^ a * h' = h := Nat.ordProj_mul_ordCompl_eq_self h p
    have hpdvd : p ∣ h := Nat.minFac_dvd h
    have ha : 1 ≤ a := (hp.factorization_pos_of_dvd hh0 hpdvd)
    have hph : ¬ p ∣ h' := Nat.not_dvd_ordCompl hp hh0
    have hh' : 1 ≤ h' := by
      rcases Nat.eq_zero_or_pos h' with h0 | h0
      · rw [h0, mul_zero] at hpa; omega
      · exact h0
    have hpk : ¬ p ∣ k := (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpdvd hc)
    have hc' : h'.Coprime k := Nat.Coprime.coprime_dvd_left ⟨p ^ a, by rw [← hpa]; ring⟩ hc
    have hpa2 : 2 ≤ p ^ a := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hlt : h' * k < n := by
      rw [← hn, ← hpa]
      have h3 : 2 * (h' * k) ≤ p ^ a * (h' * k) := Nat.mul_le_mul_right _ hpa2
      have h4 : 1 ≤ h' * k := Nat.mul_pos hh' hk
      have e : p ^ a * h' * k = p ^ a * (h' * k) := by ring
      rw [e]; linarith
    have IH' := IH (h' * k) hlt h' k rfl hh' hk hc'
    obtain ⟨hs, hG⟩ := hM p a hp ha
    have hstep := Inv_peel (hF0 h' k) hp ha hh' hph hpk hs IH'
    rw [hpa] at hstep
    refine Inv_mono ?_ hstep
    have hpk' : ¬ p ∣ h' * k := fun hd => (Nat.Prime.dvd_mul hp).1 hd |>.elim hph hpk
    have hcard : (h * k).primeFactors.card = (h' * k).primeFactors.card + 1 := by
      rw [← hpa, mul_assoc, card_pf_peel hp ha (Nat.mul_pos hh' hk) hpk']
    have hcast : ((h * k : ℕ) : ℝ) = ((h' * k : ℕ) : ℝ) * (p : ℝ) ^ a := by
      rw [← hpa]; push_cast; ring
    simp only [hF]
    rw [hcard, hcast, pow_succ]
    calc Z₀ * M ^ (h' * k).primeFactors.card * ((h' * k : ℕ) : ℝ) ^ 2 * Gp p a
        ≤ Z₀ * M ^ (h' * k).primeFactors.card * ((h' * k : ℕ) : ℝ) ^ 2 * (M * ((p : ℝ) ^ a) ^ 2) := by
          gcongr
      _ = _ := by ring
  intro h k hn hh hk hc
  rcases lt_or_eq_of_le hh with hh1 | hh1
  · exact hcase h k hn hh1 hk hc
  · subst hh1
    rcases lt_or_eq_of_le hk with hk1 | hk1
    · have := hcase k 1 (by rw [← hn]; ring) hk1 le_rfl (Nat.coprime_one_right k)
      rw [hFc] at this
      exact Inv_swap this
    · subst hk1
      simp only [hF]
      simpa using hbase

end RamanujanTau.SelbergKeyDiag2
