/-
# Weil's bound for `S(h,h;c)` in gcd form, and `‖P‖² ≪ h^β ε³ Y^{−3/2−2δ}`

* `norm_kloosterman_hh_gcd_le`: `|S(h,h;c)| ≤ A (h,c)^{1/2} c^{1/2+δ}` (same proof as
  `SCSProof.norm_kloosterman_hh_le`, keeping `g c'^{1/2+δ} = g^{1/2−δ} c^{1/2+δ}`).
* `sum_gcd_le`: `Σ_{1≤m≤K+1} (h,m)^{1/2} m^{1/2+δ}/m ≤ τ(h) (K+2)^{1/2+δ} (1 + log(K+1))`
  (`(h,m)^{1/2} ≤ Σ_{d|h, d|m} d^{1/2}`, swap, `Σ_{d|m≤K+1} 1/m ≤ H_{K+1}/d`).
* `norm_tsum_Iγ_le_gcd`: `‖Σ_γ I(γ)‖ ≤ C h^β ε³ Y^{−3/2−2δ}` for every `β > 0`
  (was `C h ε³ Y^{−3/2−2δ}`, `SCSProof.norm_tsum_Iγ_le`).
-/
import RamanujanTau.SCSProof.Bruhat8
import RamanujanTau.SCSSharp2.Divisor

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open Complex Finset RamanujanTau.TauBound RamanujanTau.SCSProof

/-- **Weil for `S(h,h;c)`, gcd form**: `|S(h,h;c)| ≤ A (h,c)^{1/2} c^{1/2+δ}` for `h, c ≥ 1`. -/
theorem norm_kloosterman_hh_gcd_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h c : ℕ, 1 ≤ h → 1 ≤ c →
      ‖kloosterman h h c‖ ≤ A * Real.sqrt (Nat.gcd h c) * (c : ℝ) ^ (1 / 2 + δ) := by
  obtain ⟨A₀, hA₀⟩ := Discharge.Kloosterman.kloostermanBound_half_unconditional δ hδ
  refine ⟨max A₀ 1, by positivity, fun h c hh hc => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd h c := ⟨_, rfl⟩
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hh
  obtain ⟨c', hc'⟩ : g ∣ c := hg ▸ Nat.gcd_dvd_right h c
  obtain ⟨h', hh'⟩ : g ∣ h := hg ▸ Nat.gcd_dvd_left h c
  have hc'0 : 0 < c' := by
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · rw [h0, mul_zero] at hc'; omega
    · exact h0
  have hcop : Nat.Coprime h' c' := by
    have := Nat.coprime_div_gcd_div_gcd (m := h) (n := c) (hg ▸ hg0)
    rwa [← hg, hh', hc', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hgh : (g : ℝ) ≤ h := by
    have : g ≤ h := Nat.le_of_dvd (by omega) ⟨h', hh'⟩
    exact_mod_cast this
  have hc'c : (c' : ℝ) ≤ c := by
    have : c' ≤ c := Nat.le_of_dvd (by omega) ⟨g, by rw [hc']; ring⟩
    exact_mod_cast this
  subst hc' hh'
  haveI : NeZero c' := ⟨by omega⟩
  haveI : NeZero (g * c') := ⟨by positivity⟩
  -- step 1: scale reduction
  have hS : ‖kloosterman ((g * h' : ℕ) : ℤ) ((g * h' : ℕ) : ℤ) (g * c')‖ ≤
      g * ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ := by
    rw [kloosterman_eq_kl]
    simpa using norm_kl_scale_le g c' h'
  -- step 2: unit reduction and Weil
  have hW : ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ ≤ max A₀ 1 * (c' : ℝ) ^ (1 / 2 + δ) := by
    set t : (ZMod c')ˣ := ZMod.unitOfCoprime h' hcop
    have ht : ((h' : ℕ) : ZMod c') = (t : ZMod c') := by simp [t]
    rw [ht, kl_unit_eq]
    have e2 : ((t : ZMod c') * (t : ZMod c')) = (((h' * h' : ℕ) : ℤ) : ZMod c') := by
      rw [← ht]; push_cast; ring
    rw [e2]
    have := hA₀ ((h' * h' : ℕ) : ℤ) c' (by omega)
    rw [kloosterman_eq_kl] at this
    simp only [Int.cast_one] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  rw [← hg]
  push_cast at hS ⊢
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hgs : (g : ℝ) ≤ Real.sqrt g * (g : ℝ) ^ (1 / 2 + δ) := by
    have h1 : Real.sqrt g ≤ (g : ℝ) ^ (1 / 2 + δ) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
    have h2 : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt (by linarith)
    have h3 : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
    nlinarith
  have hc'0R : (0 : ℝ) ≤ c' := Nat.cast_nonneg _
  calc ‖kloosterman ((g : ℤ) * h') ((g : ℤ) * h') (g * c')‖
      ≤ g * ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ := hS
    _ ≤ (g : ℝ) * (max A₀ 1 * (c' : ℝ) ^ (1 / 2 + δ)) := by gcongr
    _ = max A₀ 1 * (c' : ℝ) ^ (1 / 2 + δ) * g := by ring
    _ ≤ max A₀ 1 * (c' : ℝ) ^ (1 / 2 + δ) * (Real.sqrt g * (g : ℝ) ^ (1 / 2 + δ)) := by
        gcongr
    _ = max A₀ 1 * Real.sqrt g * ((g : ℝ) * c') ^ (1 / 2 + δ) := by
        rw [Real.mul_rpow (by linarith) hc'0R]; ring


/-- `Σ_{1 ≤ m ≤ K+1, d | m} 1/m ≤ H_{K+1}/d`. -/
lemma sum_inv_dvd_le (d K : ℕ) (hd : 1 ≤ d) :
    ∑ m ∈ (range (K + 2)).filter (fun m => m ≠ 0 ∧ d ∣ m), (1 / (m : ℝ)) ≤
      1 / (d : ℝ) * (harmonic (K + 1) : ℝ) := by
  have hsub : (range (K + 2)).filter (fun m => m ≠ 0 ∧ d ∣ m) ⊆
      (range (K + 1)).image (fun j => d * (j + 1)) := by
    intro m hm
    obtain ⟨hm1, hm0, k, rfl⟩ := by simpa using hm
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hm0
      · exact h
    refine mem_image.2 ⟨k - 1, mem_range.2 ?_, by
      rw [Nat.sub_add_cancel hk]⟩
    have : k ≤ d * k := Nat.le_mul_of_pos_left k (by omega)
    omega
  have hinj : Set.InjOn (fun j => d * (j + 1)) (range (K + 1) : Set ℕ) := by
    intro a _ b _ hab
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) hab
    omega
  calc ∑ m ∈ (range (K + 2)).filter (fun m => m ≠ 0 ∧ d ∣ m), (1 / (m : ℝ))
      ≤ ∑ m ∈ (range (K + 1)).image (fun j => d * (j + 1)), (1 / (m : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ range (K + 1), (1 / ((d * (j + 1) : ℕ) : ℝ)) := sum_image hinj
    _ = 1 / (d : ℝ) * ∑ j ∈ range (K + 1), (1 / ((j + 1 : ℕ) : ℝ)) := by
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
        push_cast; field_simp
    _ = 1 / (d : ℝ) * (harmonic (K + 1) : ℝ) := by
        congr 1; simp [harmonic]

/-- `Σ_{m ≤ K+1} (h,m)^{1/2} m^{1/2+δ}/m ≤ τ(h) (K+2)^{1/2+δ} (1 + log (K+1))`. -/
lemma sum_gcd_le (δ : ℝ) (hδ : 0 < δ) (h : ℕ) (hh : 1 ≤ h) (K : ℕ) :
    ∑ m ∈ range (K + 2), Real.sqrt (Nat.gcd h m) *
        (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m) ≤
      (#h.divisors : ℝ) * (((K : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K + 1))) := by
  classical
  set Q : ℝ := ((K : ℝ) + 2) ^ (1 / 2 + δ)
  have hQ : 0 ≤ Q := by positivity
  -- pointwise domination by a divisor sum
  have hpt : ∀ m ∈ range (K + 2), Real.sqrt (Nat.gcd h m) *
      (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m) ≤
      Q * ∑ d ∈ h.divisors, (if m ≠ 0 ∧ d ∣ m then Real.sqrt d * (1 / (m : ℝ)) else 0) := by
    intro m hm
    split_ifs with hm0
    · simp only [mul_zero]
      refine mul_nonneg hQ (sum_nonneg fun d _ => ?_)
      split_ifs <;> positivity
    · have hmK : (m : ℝ) ≤ K + 1 := by
        have := mem_range.1 hm; have : m ≤ K + 1 := by omega
        exact_mod_cast this
      have hm1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
      have hmp : (m : ℝ) ^ (1 / 2 + δ) ≤ Q := Real.rpow_le_rpow hm1.le (by linarith) (by linarith)
      have hg : Nat.gcd h m ∈ h.divisors :=
        Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left h m, by omega⟩
      have hsingle : Real.sqrt (Nat.gcd h m) * (1 / (m : ℝ)) ≤
          ∑ d ∈ h.divisors, (if m ≠ 0 ∧ d ∣ m then Real.sqrt d * (1 / (m : ℝ)) else 0) := by
        have := Finset.single_le_sum (f := fun d => if m ≠ 0 ∧ d ∣ m then
          Real.sqrt d * (1 / (m : ℝ)) else 0) (fun d _ => by
            show (0 : ℝ) ≤ if m ≠ 0 ∧ d ∣ m then Real.sqrt d * (1 / (m : ℝ)) else 0
            split_ifs <;> positivity) hg
        simpa [hm0, Nat.gcd_dvd_right] using this
      calc Real.sqrt (Nat.gcd h m) * ((m : ℝ) ^ (1 / 2 + δ) / m)
          = (m : ℝ) ^ (1 / 2 + δ) * (Real.sqrt (Nat.gcd h m) * (1 / (m : ℝ))) := by ring
        _ ≤ Q * (Real.sqrt (Nat.gcd h m) * (1 / (m : ℝ))) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle hQ
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, sum_comm]
  have hH : (harmonic (K + 1) : ℝ) ≤ 1 + Real.log (K + 1) := by
    have := harmonic_le_one_add_log (K + 1); push_cast at this ⊢; linarith
  have hd : ∀ d ∈ h.divisors, ∑ m ∈ range (K + 2),
      (if m ≠ 0 ∧ d ∣ m then Real.sqrt d * (1 / (m : ℝ)) else 0) ≤ 1 + Real.log (K + 1) := by
    intro d hdm
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdm
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    rw [← sum_filter, ← mul_sum]
    have hs := sum_inv_dvd_le d K hd1
    have hsd : Real.sqrt d * (1 / (d : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      calc Real.sqrt d ≤ Real.sqrt d * Real.sqrt d := by
            have : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 hdR
            nlinarith
        _ = d := Real.mul_self_sqrt (by linarith)
    have hHn : (0 : ℝ) ≤ harmonic (K + 1) := by exact_mod_cast (harmonic_pos (by omega)).le
    calc Real.sqrt d * ∑ m ∈ (range (K + 2)).filter (fun m => m ≠ 0 ∧ d ∣ m), (1 / (m : ℝ))
        ≤ Real.sqrt d * (1 / (d : ℝ) * (harmonic (K + 1) : ℝ)) := by gcongr
      _ = (Real.sqrt d * (1 / (d : ℝ))) * (harmonic (K + 1) : ℝ) := by ring
      _ ≤ 1 * (harmonic (K + 1) : ℝ) := by gcongr
      _ ≤ 1 + Real.log (K + 1) := by linarith
  calc Q * ∑ d ∈ h.divisors, ∑ m ∈ range (K + 2),
        (if m ≠ 0 ∧ d ∣ m then Real.sqrt d * (1 / (m : ℝ)) else 0)
      ≤ Q * ∑ d ∈ h.divisors, (1 + Real.log (K + 1)) := by gcongr with d hdm; exact hd d hdm
    _ = (#h.divisors : ℝ) * (Q * (1 + Real.log (K + 1))) := by
        rw [sum_const, nsmul_eq_mul]; ring

set_option maxHeartbeats 1000000 in
/-- **`‖P‖²`-bound (Weil, gcd form)**: `‖Σ_γ I(γ)‖ ≤ C h^β ε³ Y^{−3/2−2δ}`. -/
theorem norm_tsum_Iγ_le_gcd (δ β : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Par, 1 ≤ P.h →
      ‖∑' γ, Iγ P γ‖ ≤ C * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
  obtain ⟨A, hA0, hA⟩ := norm_kloosterman_hh_gcd_le δ hδ
  obtain ⟨Cd, hCd1, hCd⟩ := card_divisors_le_rpow β hβ
  refine ⟨32 + 128 * A * Cd * 25 * (1 + 1 / δ), by positivity, fun P hh => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have h1 := norm_tsum_Iγ_le_gK P
  -- the `∫⁻ ‖ft‖` term
  have hX : (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 16 * P.ε ^ 3 / P.Y := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_ft_le P)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- `Y^{-1} ≤ Y^{-3/2-2δ}`
  have hYpow : P.Y ^ (-(1 : ℝ)) ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_ge hY hY1 (by linarith)
  have hYinv : 1 / P.Y = P.Y ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, one_div]
  have hhβ : (1 : ℝ) ≤ (P.h : ℝ) ^ β := Real.one_le_rpow hhR hβ.le
  -- the Kloosterman terms
  have hg : ∀ m ∈ Finset.range (K2 P + 2), gK P m ≤
      (A * (64 * P.ε ^ 3 / P.Y)) * (Real.sqrt (Nat.gcd P.h m) *
        (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m)) := by
    intro m _
    unfold gK
    split_ifs with hm0
    · subst hm0; simp [kloosterman_zero_mod]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      have hk := hA P.h m hh hm1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      calc ‖kloosterman P.h P.h m‖ * (64 * P.ε ^ 3 / (m * P.Y))
          ≤ (A * Real.sqrt (Nat.gcd P.h m) * (m : ℝ) ^ (1 / 2 + δ)) * (64 * P.ε ^ 3 / (m * P.Y)) := by
            gcongr
        _ = _ := by field_simp
  have hsum0 := Finset.sum_le_sum hg
  rw [← Finset.mul_sum] at hsum0
  have hG := sum_gcd_le δ hδ P.h hh (K2 P)
  have hcoef0 : 0 ≤ A * (64 * P.ε ^ 3 / P.Y) := by positivity
  have hsum : ∑ m ∈ Finset.range (K2 P + 2), gK P m ≤
      (A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y)) *
        (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1))) := by
    have hL0 : 0 ≤ ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ K2 P + 1 by
        have : (0 : ℝ) ≤ K2 P := Nat.cast_nonneg _
        linarith)
      positivity
    calc _ ≤ _ := hsum0
      _ ≤ (A * (64 * P.ε ^ 3 / P.Y)) * ((#P.h.divisors : ℝ) *
            (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)))) := by gcongr
      _ ≤ (A * (64 * P.ε ^ 3 / P.Y)) * ((Cd * (P.h : ℝ) ^ β) *
            (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)))) := by
          gcongr; exact hCd P.h hh
      _ = _ := by ring
  have hS := sum_rpow_div_le δ hδ (K2 P)
  -- `K₂ + 2 ≤ 5/Y`
  have hK : (K2 P : ℝ) + 2 ≤ 5 / P.Y := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / P.Y by positivity)
    have h3 : 3 ≤ 3 / P.Y := by rw [le_div_iff₀ hY]; linarith
    unfold K2
    have : (5 : ℝ) / P.Y = 2 / P.Y + 3 / P.Y := by ring
    linarith
  have hK1 : (1 : ℝ) ≤ 5 / P.Y := by rw [le_div_iff₀ hY]; linarith
  have hlog : Real.log ((K2 P : ℝ) + 1) ≤ (5 / P.Y) ^ δ / δ := by
    refine (Real.log_le_rpow_div (by positivity) hδ).trans ?_
    gcongr; linarith
  have hpow1 : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) ≤ (5 / P.Y) ^ (1 / 2 + δ) := by
    gcongr
  have hS' : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)) ≤
      25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
    have e1 : (5 / P.Y) ^ (1 / 2 + δ) * (5 / P.Y) ^ δ = (5 / P.Y) ^ (1 / 2 + 2 * δ) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have e2 : (5 / P.Y) ^ (1 / 2 + 2 * δ) = (5 : ℝ) ^ (1 / 2 + 2 * δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
      rw [Real.div_rpow (by norm_num) hY.le, div_eq_mul_inv, ← Real.rpow_neg hY.le]
      ring_nf
    have h5 : (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ 25 := by
      calc (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ (5 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 25 := by norm_num
    have hpowδ : 1 ≤ (5 / P.Y) ^ δ := Real.one_le_rpow hK1 hδ.le
    have hYp : 0 < P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := Real.rpow_pos_of_pos hY _
    calc ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1))
        ≤ (5 / P.Y) ^ (1 / 2 + δ) * ((5 / P.Y) ^ δ * (1 + 1 / δ)) := by
          gcongr
          · have := Real.log_nonneg (show (1 : ℝ) ≤ K2 P + 1 by
              have : (0 : ℝ) ≤ K2 P := Nat.cast_nonneg _
              linarith)
            linarith
          · calc 1 + Real.log ((K2 P : ℝ) + 1) ≤ 1 + (5 / P.Y) ^ δ / δ := by linarith
              _ ≤ (5 / P.Y) ^ δ + (5 / P.Y) ^ δ / δ := by linarith
              _ = (5 / P.Y) ^ δ * (1 + 1 / δ) := by ring
      _ = (5 / P.Y) ^ (1 / 2 + 2 * δ) * (1 + 1 / δ) := by rw [← e1]; ring
      _ ≤ 25 * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) * (1 + 1 / δ) := by
          rw [e2]; gcongr
      _ = 25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by ring
  have hYsplit : 1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) = P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    rw [hYinv, ← Real.rpow_add hY]; ring_nf
  have hYp3 : 0 ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := (Real.rpow_pos_of_pos hY _).le
  have hfin : 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m ≤
      128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
        P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have hcoef : 0 ≤ A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y) := by positivity
    calc 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m
        ≤ 2 * ((A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y)) * (25 * (1 + 1 / δ) *
            P.Y ^ (-(1 / 2 : ℝ) - 2 * δ))) := by
          gcongr; exact hsum.trans (mul_le_mul_of_nonneg_left hS' hcoef)
      _ = 128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
            (1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ)) := by ring
      _ = _ := by rw [hYsplit]
  have hfirst : 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤
      32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have : 2 * (16 * P.ε ^ 3 / P.Y) = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := by rw [← hYinv]; ring
    calc 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 2 * (16 * P.ε ^ 3 / P.Y) := by linarith
      _ = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := this
      _ ≤ 32 * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by gcongr
      _ ≤ 32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
          have : 0 ≤ P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by positivity
          nlinarith [hhβ]
  calc ‖∑' γ, Iγ P γ‖ ≤ _ := h1
    _ ≤ 32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) +
          128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
            P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
        add_le_add hfirst hfin
    _ = _ := by ring

end RamanujanTau.SCSSharp2
