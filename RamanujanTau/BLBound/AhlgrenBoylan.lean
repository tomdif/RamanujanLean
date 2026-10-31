import RamanujanTau.BLBound.WeightClass

/-!
# The theorem of Ahlgren–Boylan

For a prime `ℓ ≥ 13` there is no `β < ℓ` with `ℓ ∣ p(ℓn + β)` for all `n`.

The class `24β ≡ 1` is `no_ramanujan_congruence`. In any other class, `F = Δ^δ` has no coefficients at `n ≡ ρ ≠ 0`, which
says `∑_{1 ≤ j ≤ ℓ-1} ρ^{ℓ-1-j} θ^j F = 0`. Separating the classes modulo `ℓ - 1` gives
`θ^{(ℓ-1)/2}(θF) = c θF` with `c ≠ 0`, but the filtration rises at each of those `(ℓ-1)/2` steps.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open MvPolynomial ModP Igusa BoylanWebb
open RamanujanTau.TheoremA.HalfIntegral

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma FormBar.add' {k : ℕ} {f g : PowerSeries (ZMod ℓ)} (hf : FormBar ℓ k f) (hg : FormBar ℓ k g) :
    FormBar ℓ k (f + g) := by
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨Q, hQ, rfl⟩ := hg
  exact ⟨P + Q, hP.add hQ, map_add _ _ _⟩

lemma FormBar.smul' {k : ℕ} {f : PowerSeries (ZMod ℓ)} (c : ZMod ℓ) (hf : FormBar ℓ k f) : FormBar ℓ k (c • f) := by
  obtain ⟨P, hP, rfl⟩ := hf
  refine ⟨C c * P, hP.C_mul c, ?_⟩
  rw [map_mul, ev_C, PowerSeries.smul_eq_C_mul]

lemma filt_smul {r : ℕ} {c : ZMod ℓ} (hc : c ≠ 0) (f : PowerSeries (ZMod ℓ)) : filt ℓ r (c • f) = filt ℓ r f := by
  have hiff : ∀ k, FormBar ℓ k (c • f) ↔ FormBar ℓ k f := fun k =>
    ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul' c⁻¹, fun h => h.smul' c⟩
  simp only [filt, hiff]

/-- **No class `ρ ≠ 0` is empty for `Δ^δ`.** -/
theorem no_nonzero_class (h13 : 13 ≤ ℓ) {ρ : ZMod ℓ} (hρ : ρ ≠ 0)
    (hvan : ∀ n : ℕ, (n : ZMod ℓ) = ρ → PowerSeries.coeff n (Dl ℓ ^ δ ℓ) = 0) : False := by
  have hp := hℓ.out
  have h5 : 5 ≤ ℓ := by omega
  have h24' := h24 (ℓ := ℓ) h13
  obtain ⟨s, hs⟩ : ∃ s, ℓ = 2 * s + 1 := by
    obtain ⟨s, hs⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨s, hs⟩
  have hs6 : 6 ≤ s := by omega
  have hl1 : ℓ - 1 = 2 * s := by omega
  set dl := δ ℓ with hdl
  have hK : 12 * dl = 2 * s ^ 2 + 2 * s := by
    have : 24 * dl = 4 * s ^ 2 + 4 * s := by
      have e : ℓ ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by rw [hs]; ring
      omega
    omega
  set f := Dl ℓ ^ dl with hf
  have hx : 24 * (dl : ZMod ℓ) + 1 = 0 := by
    have := congrArg (Nat.cast : ℕ → ZMod ℓ) h24'
    push_cast at this
    rw [this, CharP.cast_eq_zero (ZMod ℓ) ℓ]
    simp
  have hx0 : (dl : ZMod ℓ) ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  obtain ⟨hc0, -⟩ := coeff_h (ℓ := ℓ) h24'
  have hfX : f = PowerSeries.X ^ dl * PowerSeries.map (Int.castRingHom (ZMod ℓ))
      (MockTheta5.JTP.qfacInf ^ (24 * dl)) := Dl_pow dl
  have hfd : PowerSeries.coeff dl f = 1 := by
    rw [hfX, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    exact hc0
  have hflow : ∀ n < dl, PowerSeries.coeff n f = 0 := by
    intro n hn
    rw [hfX, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hf12 := formBar_Dl_pow (ℓ := ℓ) h5 dl
  have hFg : ∀ i, FormBar ℓ (12 * dl + i * (ℓ + 1)) (Igusa.theta^[i] f) := fun i => hf12.theta_iter h5 i
  have hg0 : ∀ i, Igusa.theta^[i] f ≠ 0 := by
    intro i hi
    have := congrArg (PowerSeries.coeff dl) hi
    rw [coeff_theta_iter, hfd, mul_one, map_zero] at this
    exact pow_ne_zero _ hx0 this
  -- the relation
  let G : ℕ → PowerSeries (ZMod ℓ) := fun j => (ρ ^ (2 * s - (j + 1))) • Igusa.theta^[j + 1] f
  have hfermat : ∀ x : ZMod ℓ, x ^ (2 * s + 1) = x := by
    intro x
    rw [← hs]
    exact ZMod.pow_card x
  have hT : ∑ j ∈ Finset.range (2 * s), G j = 0 := by
    ext n
    rw [map_sum, map_zero]
    simp only [G, PowerSeries.coeff_smul, coeff_theta_iter, smul_eq_mul]
    by_cases hn : (n : ZMod ℓ) = ρ
    · rw [hvan n hn]
      simp
    · set a := PowerSeries.coeff n f
      have hgeo := geom_sum₂_mul (n : ZMod ℓ) ρ (2 * s + 1)
      rw [hfermat, hfermat] at hgeo
      have hsum : ∑ i ∈ Finset.range (2 * s + 1), (n : ZMod ℓ) ^ i * ρ ^ (2 * s + 1 - 1 - i) = 1 :=
        mul_right_cancel₀ (sub_ne_zero.mpr hn) (by rw [hgeo, one_mul])
      rw [Finset.sum_range_succ'] at hsum
      have hone : ρ ^ (2 * s) = 1 := by
        have := ZMod.pow_card_sub_one_eq_one hρ
        rwa [hl1] at this
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel, hone] at hsum
      have hsum0 : ∑ i ∈ Finset.range (2 * s), (n : ZMod ℓ) ^ (i + 1) * ρ ^ (2 * s - (i + 1)) = 0 := by
        linear_combination hsum
      calc ∑ j ∈ Finset.range (2 * s), ρ ^ (2 * s - (j + 1)) * ((n : ZMod ℓ) ^ (j + 1) * a)
          = (∑ i ∈ Finset.range (2 * s), (n : ZMod ℓ) ^ (i + 1) * ρ ^ (2 * s - (i + 1))) * a := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hsum0, zero_mul]
  -- the classes
  let H : ℕ → PowerSeries (ZMod ℓ) := fun i => G i + G (s + i)
  have hHsum : ∑ i ∈ Finset.range s, H i = 0 := by
    rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib] at hT
    exact hT
  have hHform : ∀ i < s, FormBar ℓ (12 * dl + (s + i + 1) * (ℓ + 1)) (H i) := by
    intro i _
    refine FormBar.add' ?_ ?_
    · have h1 := (hFg (i + 1)).up h5 (s + 1)
      have e : 12 * dl + (i + 1) * (ℓ + 1) + (s + 1) * (ℓ - 1) = 12 * dl + (s + i + 1) * (ℓ + 1) := by
        rw [hl1, hs]
        ring
      rw [e] at h1
      exact h1.smul' _
    · exact (by simpa [add_assoc] using hFg (s + i + 1) : FormBar ℓ _ _).smul' _
  have hHclass : ∀ i < s, (12 * dl + (s + i + 1) * (ℓ + 1)) % (ℓ - 1) = (12 * dl + 2 + 2 * i) % (ℓ - 1) := by
    intro i _
    rw [hl1, show 12 * dl + (s + i + 1) * (ℓ + 1) = 12 * dl + 2 + 2 * i + 2 * s * (s + i + 2) by rw [hs]; ring,
      Nat.add_mul_mod_self_left]
  have hsep := class_sep h5 s hs (12 * dl + 2) (by omega) H _ hHform hHclass hHsum 0 (by omega)
  have hrel : Igusa.theta^[s + 1] f = (-ρ ^ s) • Igusa.theta^[1] f := by
    have h1 : ρ ^ (s - 1) • (ρ ^ s • Igusa.theta^[1] f + Igusa.theta^[s + 1] f) = 0 := by
      have e1 : 2 * s - (0 + 1) = s - 1 + s := by omega
      have e2 : 2 * s - (s + 0 + 1) = s - 1 := by omega
      simp only [H, G, e1, e2, add_zero, pow_add, mul_smul] at hsep
      rw [smul_add]
      exact hsep
    have h2 := (smul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hρ)
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right h2
  -- the filtration
  have hclass : ∀ i, (12 * dl + i * (ℓ + 1)) % (ℓ - 1) = (12 * dl + 2 * i) % (ℓ - 1) := by
    intro i
    rw [hl1, show 12 * dl + i * (ℓ + 1) = 12 * dl + 2 * i + 2 * s * i by rw [hs]; ring, Nat.add_mul_mod_self_left]
  have hW : ∀ i, i ≤ s + 1 → filt ℓ (12 * dl + 2 * i) (Igusa.theta^[i] f) = 12 * dl + i * (ℓ + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine le_antisymm (filt_le (by simp) (by simpa using hf12)) ?_
      obtain ⟨P, hP, he⟩ := (filt_spec (hclass 0) (hFg 0)).2
      have := (div_Delta_pow h5 dl hP (by rw [he]; exact hflow) (by rw [he]; exact hg0 0)).1
      simpa using this
    | succ i ih =>
      intro hi
      have hwi := ih (by omega)
      have hnd : ((filt ℓ (12 * dl + 2 * i) (Igusa.theta^[i] f) : ℕ) : ZMod ℓ) ≠ 0 := by
        rw [hwi]
        intro h0
        have hd := (ZMod.natCast_eq_zero_iff _ _).mp h0
        have e : 12 * dl + i * (ℓ + 1) = ℓ * (s + i) + (s + i) := by
          rw [hK, hs]
          ring
        rw [e] at hd
        have hd2 := (Nat.dvd_add_right (dvd_mul_right ℓ _)).mp hd
        have := Nat.le_of_dvd (by omega) hd2
        omega
      have heq := filt_theta_eq h5 (hclass i) (hFg i) (hg0 i) hnd
      rw [hwi, ← Function.iterate_succ_apply' Igusa.theta] at heq
      rw [show 12 * dl + 2 * (i + 1) = 12 * dl + 2 * i + 2 by ring, heq]
      ring
  have h1 := hW 1 (by omega)
  have h2 := hW (s + 1) le_rfl
  have hc' : (-ρ ^ s) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hρ)
  rw [hrel, filt_smul hc'] at h2
  rw [filt_congr (s := 12 * dl + 2 * 1) _ (by
    rw [hl1, show 12 * dl + 2 * (s + 1) = 12 * dl + 2 * 1 + 2 * s * 1 by ring, Nat.add_mul_mod_self_left]), h1] at h2
  have hpos : 0 < s * (ℓ + 1) := by positivity
  nlinarith

/-- `Δ^δ` has no coefficient in a class where the partition numbers vanish. -/
lemma coeff_Dl_of_congr (h13 : 13 ≤ ℓ) {β : ℕ} (hβ : β < ℓ) (hall : ∀ n : ℕ, ℓ ∣ Fintype.card (Nat.Partition (ℓ * n + β)))
    (n : ℕ) (hn : (n : ZMod ℓ) = ((β + δ ℓ : ℕ) : ZMod ℓ)) : PowerSeries.coeff n (Dl ℓ ^ δ ℓ) = 0 := by
  have h24' := h24 (ℓ := ℓ) h13
  have hF : Dl ℓ ^ δ ℓ = Ψ ℓ (Φ ℓ) := by rw [Ψ_Φ ℓ h24', Psi_Dz_pow]
  rw [hF, PowerSeries.coeff_map]
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
  rw [Φ, mul_assoc, PowerSeries.coeff_X_pow_mul']
  split_ifs with hle
  swap
  · exact dvd_zero _
  rw [PowerSeries.coeff_mul]
  refine Finset.dvd_sum ?_
  rintro ⟨a, b⟩ hab
  have hsum : a + b = n - δ ℓ := Finset.mem_antidiagonal.mp hab
  simp only
  rw [RankProof.coeff_Ea]
  split_ifs with hd
  swap
  · simp
  have hdl : ℓ ∣ a := (dvd_pow_self ℓ (by norm_num)).trans hd
  have hb : (b : ZMod ℓ) = (β : ZMod ℓ) := by
    have hna : n = δ ℓ + (a + b) := by omega
    have ha0 : (a : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdl
    rw [hna] at hn
    push_cast at hn
    rw [ha0] at hn
    linear_combination hn
  have hmod : b % ℓ = β := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hb
    rwa [Nat.mod_eq_of_lt hβ] at this
  have hc := hall (b / ℓ)
  rw [← hmod, Nat.div_add_mod] at hc
  rw [MockTheta5.JTP.coeff_partitionGF_eq_card]
  exact dvd_mul_of_dvd_right (by exact_mod_cast hc) _

/-- **The theorem of Ahlgren–Boylan.** For a prime `ℓ ≥ 13` there is no `β < ℓ` such that `ℓ ∣ p(ℓn + β)` for
all `n`. So Ramanujan's congruences modulo `5`, `7`, `11` have no analogue at larger primes. -/
theorem ahlgren_boylan (h13 : 13 ≤ ℓ) {β : ℕ} (hβ : β < ℓ) :
    ¬ ∀ n : ℕ, ℓ ∣ Fintype.card (Nat.Partition (ℓ * n + β)) := by
  intro hall
  have hvan := coeff_Dl_of_congr h13 hβ hall
  by_cases hρ : ((β + δ ℓ : ℕ) : ZMod ℓ) = 0
  · apply U_Dl_ne_zero (ℓ := ℓ) h13
    ext N
    rw [coeff_U, map_zero]
    refine hvan _ ?_
    rw [hρ]
    push_cast
    simp
  · exact no_nonzero_class h13 hρ hvan

end

end RamanujanTau.BLBound
