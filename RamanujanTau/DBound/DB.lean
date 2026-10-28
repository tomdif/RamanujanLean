import RamanujanTau.DBound.Limit

/-!
# (DB) from (UB) and `E^s W ∈ B_E(r)` (Step 1 of `docs/ATKIN_OBRIEN_PROOF.md`)

Notation (`p = ℓ`): `s = (ℓ+1)/2`, `δ = (ℓ²−1)/24`, `W = η(ℓ²z)/η(z)^{ℓ²} = (q^{ℓ²};q^{ℓ²})_∞/(q;q)_∞^{ℓ²}`,
`Φ = η(ℓ²z)/η(z) = Δ^δ W`.

* **`HW`**: `E^s W` has a Katz expansion with `v_i ≥ ⌈i/(ℓ+1)⌉`, i.e. `E^sW ∈ B_E(r)` for every
  `v(r) < 1/(ℓ+1)` (sharp form).
* **`DB_of_UB`**: `UB → HW → DB`.

Proof. `Φ·b/E^j = (Δ^δ/E^s)·(E^sW)·(b/E^j)`. Here `Δ^δ` has weight `12δ = s(ℓ−1)`, so
`Δ^δ/E^s = Σ_{m≤s} c_m/E^m` is a finite *integral* Katz series (`decompN`), i.e. lies in
`r^{-s}B_E(r)` with the bound `⌈(m−s)/(ℓ+1)⌉ ≤ 0`. Multiplying (`Ap_mul`, the ring structure of
`B_E(r)` in coordinates) gives `Φ·b/E^j` with `v_k ≥ ⌈(k−j−s)/(ℓ+1)⌉`. The column bounds (UB) and
`transfer` then give `v_i(D(b/E^j)) ≥ ⌈(ℓi−j−s)/(ℓ+1)⌉ − 1` (using `⌈x⌉ + ⌈y⌉ ≥ ⌈x+y⌉`), and
`isKatz_of_Ap` turns the approximations into a genuine Katz expansion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien PowerSeries MockTheta5.JTP

variable (ℓ : ℕ) [hℓp : Fact ℓ.Prime]

/-- `s = (ℓ+1)/2`. -/
def sN : ℕ := (ℓ + 1) / 2

/-- `W = (q^{ℓ²};q^{ℓ²})_∞ / (q;q)_∞^{ℓ²} ∈ ℤ⟦q⟧` (`η(ℓ²z)/η(z)^{ℓ²}`; the `q`-powers cancel). -/
noncomputable def Wz : PowerSeries ℤ :=
  RankProof.Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2) qfacInf * partitionGF ^ (ℓ ^ 2)

/-- `W ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Wl : PS ℓ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (Wz ℓ)

/-- `Δ ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable abbrev Dl : PS ℓ := ModP.Dq ℤ_[ℓ]

variable {ℓ}

lemma odd_ell (hℓ : 5 ≤ ℓ) : ℓ % 2 = 1 := by
  rcases Nat.even_or_odd ℓ with h | h
  · exfalso
    have := (hℓp.out.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp h))
    omega
  · exact Nat.odd_iff.mp h

lemma two_sN (hℓ : 5 ≤ ℓ) : 2 * sN ℓ = ℓ + 1 := by
  have := odd_ell hℓ; unfold sN; omega

/-- `24 δ + 1 = ℓ²` for primes `ℓ ≥ 5`. -/
lemma h24 (hℓ : 5 ≤ ℓ) : 24 * BoylanWebb.δ ℓ + 1 = ℓ ^ 2 := by
  have h2 : ℓ % 2 = 1 := odd_ell hℓ
  have h3 : ℓ % 3 ≠ 0 := by
    intro h
    have := hℓp.out.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have hsq : ℓ ^ 2 % 24 = 1 := by
    rw [Nat.pow_mod]
    have hr : ℓ % 24 < 24 := Nat.mod_lt _ (by norm_num)
    have e2 : ℓ % 24 % 2 = 1 := by omega
    have e3 : ℓ % 24 % 3 ≠ 0 := by omega
    interval_cases h : ℓ % 24 <;> simp_all
  have hpos : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold BoylanWebb.δ
  omega

/-- `12 δ = s(ℓ−1)`: `Δ^δ` and `E^s` have the same weight. -/
lemma twelve_delta (hℓ : 5 ≤ ℓ) : 12 * BoylanWebb.δ ℓ = sN ℓ * (ℓ - 1) := by
  have h := h24 hℓ
  have hs := two_sN hℓ
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h' : (2 * sN (m + 1)) * m = (m + 2) * m := by rw [hs]
  have e : 2 * (12 * BoylanWebb.δ (m + 1)) = 2 * (sN (m + 1) * m) := by nlinarith [h, h']
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) e

/-- **`Φ = Δ^δ · W`** in `ℤ⟦q⟧`. -/
lemma Phi_eq (hℓ : 5 ≤ ℓ) : BoylanWebb.Φ ℓ = BoylanWebb.Dz ^ BoylanWebb.δ ℓ * Wz ℓ := by
  have h := h24 hℓ
  rw [BoylanWebb.Φ, Wz, show partitionGF ^ (ℓ ^ 2) = partitionGF ^ (24 * BoylanWebb.δ ℓ) * partitionGF
    by rw [← pow_succ, h], BoylanWebb.Dz, mul_pow, ← pow_mul]
  have h1 := BoylanWebb.qfac_mul_pgf
  have : qfacInf ^ (24 * BoylanWebb.δ ℓ) * partitionGF ^ (24 * BoylanWebb.δ ℓ) = 1 := by
    rw [← mul_pow, h1, one_pow]
  rw [mul_comm 24 (BoylanWebb.δ ℓ)] at this ⊢
  linear_combination (-(PowerSeries.X ^ BoylanWebb.δ ℓ * RankProof.Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2)
    qfacInf * partitionGF)) * this

lemma Phil_eq (hℓ : 5 ≤ ℓ) : Φl ℓ = Dl ℓ ^ BoylanWebb.δ ℓ * Wl ℓ := by
  rw [Φl, Phi_eq hℓ, map_mul, map_pow, Wl]; rfl

variable (hℓ : 5 ≤ ℓ)

/-- `Δ = (X₀³ − X₁²)/1728`. -/
noncomputable def Pdisc : Poly ℓ :=
  MvPolynomial.C (↑(isUnit_1728_Zp (p := ℓ) hℓ).unit⁻¹ : ℤ_[ℓ]) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

lemma ev_Pdisc : ModP.ev ℤ_[ℓ] (Pdisc hℓ) = Dl ℓ := by
  rw [Pdisc, map_mul, ev_disc, MvPolynomial.algHom_C, ← mul_assoc]
  have : (algebraMap ℤ_[ℓ] (PS ℓ)) (↑(isUnit_1728_Zp (p := ℓ) hℓ).unit⁻¹ : ℤ_[ℓ]) * 1728 = 1 := by
    rw [show (1728 : PS ℓ) = algebraMap ℤ_[ℓ] (PS ℓ) 1728 from (map_ofNat _ _).symm, ← map_mul]
    rw [show (↑(isUnit_1728_Zp (p := ℓ) hℓ).unit⁻¹ : ℤ_[ℓ]) * 1728 = 1 from
      (isUnit_1728_Zp (p := ℓ) hℓ).val_inv_mul, map_one]
  rw [this, one_mul]

lemma iso_Pdisc : Iso (Pdisc hℓ) 12 := by
  have h1 : Iso (MvPolynomial.X 0 ^ 3 : Poly ℓ) 12 :=
    iso_of_eq ((isWeightedHomogeneous_X (R := ℤ_[ℓ]) ModP.wt 0).pow 3) (by simp [ModP.wt])
  have h2 : Iso (MvPolynomial.X 1 ^ 2 : Poly ℓ) 12 :=
    iso_of_eq ((isWeightedHomogeneous_X (R := ℤ_[ℓ]) ModP.wt 1).pow 2) (by simp [ModP.wt])
  exact iso_of_eq ((isWeightedHomogeneous_C ModP.wt _).mul (iso_sub h1 h2)) (by simp)

/-! ### the bounds `⌈(m − t)/(ℓ+1)⌉₊` -/

lemma toNat_max (x : ℤ) : (max 0 x).toNat = x.toNat := by omega

variable (ℓ) in
/-- `B_t(m) = max(0, ⌈(m − t)/(ℓ+1)⌉)`: the coordinates of `r^{-t}B_E(r)` (all `v(r) < 1/(ℓ+1)`). -/
noncomputable def Bq (t : ℚ) (m : ℕ) : ℕ := (⌈((m : ℚ) - t) / ((ℓ : ℚ) + 1)⌉).toNat

lemma Bq_mul (t t' : ℚ) (k l m : ℕ) (h : m ≤ k + l) : Bq ℓ (t + t') m ≤ Bq ℓ t k + Bq ℓ t' l := by
  unfold Bq
  have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  have h1 : ⌈((m : ℚ) - (t + t')) / ((ℓ : ℚ) + 1)⌉ ≤
      ⌈((k : ℚ) - t) / ((ℓ : ℚ) + 1)⌉ + ⌈((l : ℚ) - t') / ((ℓ : ℚ) + 1)⌉ := by
    refine le_trans (Int.ceil_mono ?_) (Int.ceil_add_le _ _)
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have : (m : ℚ) ≤ k + l := by exact_mod_cast h
    linarith
  have := Int.self_le_toNat ⌈((k : ℚ) - t) / ((ℓ : ℚ) + 1)⌉
  have := Int.self_le_toNat ⌈((l : ℚ) - t') / ((ℓ : ℚ) + 1)⌉
  omega

lemma Bq_le_zero {t : ℚ} {m : ℕ} (h : (m : ℚ) ≤ t) : Bq ℓ t m = 0 := by
  unfold Bq
  have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  have : ⌈((m : ℚ) - t) / ((ℓ : ℚ) + 1)⌉ ≤ 0 := by
    rw [Int.ceil_le, Int.cast_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  omega

/-! ### the three factors -/

/-- `Δ^δ/E^s` is a finite integral Katz series (indices `≤ s`). -/
lemma Ap_Delta : Ap hℓ (Bq ℓ (sN ℓ)) (Dl ℓ ^ BoylanWebb.δ ℓ * Einv ℓ hℓ ^ sN ℓ) := by
  intro N
  have hiso : Iso (Pdisc hℓ ^ BoylanWebb.δ ℓ) (sN ℓ * (ℓ - 1)) :=
    iso_of_eq ((iso_Pdisc hℓ).pow _) (by rw [smul_eq_mul, mul_comm, twelve_delta hℓ])
  obtain ⟨c, hcK, hc0, hcD⟩ := decompN hℓ N (sN ℓ) _ hiso
  refine ⟨sN ℓ + 1, c, hcK, ?_, fun m => ?_⟩
  · unfold Approx; rwa [map_pow, ev_Pdisc] at hcD
  · by_cases hm : m ≤ sN ℓ
    · rw [Bq_le_zero (by exact_mod_cast hm)]; exact ⟨c m, by rw [pow_zero, one_smul]⟩
    · rw [hc0 m (by omega)]; exact Dvd_zero _

variable (ℓ) in
/-- **(HW)** `E^s W ∈ B_E(r)` for all `v(r) < 1/(ℓ+1)`: a Katz expansion with `v_i ≥ ⌈i/(ℓ+1)⌉`. -/
def HW : Prop :=
  ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c (E ℓ hℓ ^ sN ℓ * Wl ℓ) ∧
    ∀ i : ℕ, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (⌈(i : ℚ) / ((ℓ : ℚ) + 1)⌉).toNat (c i)

lemma Ap_W (hW : HW ℓ hℓ) : Ap hℓ (Bq ℓ 0) (E ℓ hℓ ^ sN ℓ * Wl ℓ) := by
  obtain ⟨c, hc, hcb⟩ := hW
  exact Ap_of_isKatz hc fun i => by simpa [Bq] using hcb i

lemma Ap_x (j : ℕ) {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j) :
    Ap hℓ (Bq ℓ j) (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) :=
  Ap_single j hx (by rw [Bq_le_zero le_rfl]; exact ⟨x, by rw [pow_zero, one_smul]⟩)

/-- **`Φ·b/E^j ∈ r^{-(j+s)}B_E(r)`**, in coordinates. -/
theorem Ap_Phi (hW : HW ℓ hℓ) (j : ℕ) {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j) :
    Ap hℓ (Bq ℓ (sN ℓ + 0 + j)) (Φl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) := by
  have e : Φl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) =
      Dl ℓ ^ BoylanWebb.δ ℓ * Einv ℓ hℓ ^ sN ℓ * (E ℓ hℓ ^ sN ℓ * Wl ℓ) *
        (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) := by
    rw [Phil_eq hℓ]
    have : Einv ℓ hℓ ^ sN ℓ * E ℓ hℓ ^ sN ℓ = 1 := by
      rw [← mul_pow, mul_comm, E_mul_Einv, one_pow]
    linear_combination (Dl ℓ ^ BoylanWebb.δ ℓ * Wl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) * this.symm
  rw [e]
  exact Ap_mul (Bq_mul _ _) (Ap_mul (Bq_mul _ _) (Ap_Delta hℓ) (Ap_W hℓ hW)) (Ap_x hℓ j hx)

/-- **(DB) from (UB) and (HW).** -/
theorem DB_of_UB (hUB : UB ℓ hℓ) (hW : HW ℓ hℓ) : DB ℓ hℓ := by
  intro j x hx
  have hs : ((sN ℓ : ℕ) : ℚ) = AtkinOBrien.s ℓ := by
    have := two_sN hℓ
    rw [AtkinOBrien.s]
    have h' : (2 : ℚ) * (sN ℓ : ℚ) = (ℓ : ℚ) + 1 := by exact_mod_cast this
    linarith
  set γ : ℕ → ℤ := fun k => ⌈((k : ℚ) - j - AtkinOBrien.s ℓ) / ((ℓ : ℚ) + 1)⌉ with hγ
  have hEnv : Env ℓ hℓ 0 γ (Φl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) := by
    rw [env_iff_Ap]
    refine Ap_mono (fun k => le_of_eq ?_) (Ap_Phi hℓ hW j hx)
    rw [toNat_max, sub_zero, hγ, Bq, hs]
    congr 3
    ring_nf
  have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  have henv : ∀ i k, (d ℓ i j + 1) - 1 ≤ max 0 (γ k - 0) + u ℓ i k := by
    intro i k
    have h1 : ⌈((ℓ : ℚ) * i - j - AtkinOBrien.s ℓ) / ((ℓ : ℚ) + 1)⌉ ≤
        γ k + ⌈((ℓ : ℚ) * i - k) / ((ℓ : ℚ) + 1)⌉ := by
      refine le_trans (le_of_eq (congrArg _ ?_)) (Int.ceil_add_le _ _)
      field_simp
      ring
    have h2 : γ k ≤ max 0 (γ k - 0) := by rw [sub_zero]; exact le_max_right _ _
    simp only [d, u] at h1 ⊢
    omega
  have hT := transfer hℓ (Ulin ℓ) (u ℓ) (cols_U ℓ hℓ hUB) 0 γ (fun i => d ℓ i j + 1) henv _ hEnv
  rw [env_iff_Ap] at hT
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap hT
  refine ⟨c, hc, fun i => ?_⟩
  have := hcb i
  rwa [add_sub_cancel_right, toNat_max] at this

end DBound
