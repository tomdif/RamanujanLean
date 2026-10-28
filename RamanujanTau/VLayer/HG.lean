import RamanujanTau.VLayer.ModEq
import RamanujanTau.DBound.HW

/-!
# (HG) `G = E/V(E) ∈ B_E(r)`, unconditionally

From the modular equation of `E` (`VLayer.modular_equation_E`):

  `Σ_{k ≤ ℓ+1} (−1)^k f_k · (ℓ^{ℓ−1} V E)^{ℓ+1−k} = 0`,   `f_k` classical of weight `k(ℓ−1)`,

dividing by `ℓ^{ℓ−1} E^{ℓ+1}` gives, for `y = V(E)/E`,

  `Σ_{k ≤ ℓ} (−1)^k ℓ^{(ℓ−1)(ℓ−k)} (f_k/E^k) y^{ℓ+1−k} + M/E^{ℓ+1} = 0`,  `f_{ℓ+1} = ℓ^{ℓ−1} M`.

Every coefficient is a Katz series of index `≤ ℓ + 1`, and on indices `i ≤ ℓ + 1` the target bound
`v_i ≥ ⌈i/(ℓ+1)⌉` asks only for divisibility by `ℓ` in positive index. The coefficients of `y^d`,
`d ≥ 2`, carry `ℓ^{≥ℓ−1}`; those of `y` and `1` are `−f_ℓ/E^ℓ ≡ −1` and `M/E^{ℓ+1} ≡ 1` (mod `ℓ`), so
they are `±1` plus `ℓ·(integral Katz series)`. Hence `y` is the fixed point of an `ℓ`-adic
contraction preserving the class `{v_i ≥ ⌈i/(ℓ+1)⌉}` (`hensel_fix`), so `y` lies in it; so does
`G = 1/y`.

* **`HG_holds : DBound.HG ℓ hℓ`** for every prime `ℓ ≥ 5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### helpers -/

lemma Dvd_mul_mul {a b : ℕ} {x z : PS ℓ} (hx : Dvd (ℓ : ℤ_[ℓ]) a x) (hz : Dvd (ℓ : ℤ_[ℓ]) b z) :
    Dvd (ℓ : ℤ_[ℓ]) (a + b) (x * z) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hz
  exact ⟨u * w, by simp only [Algebra.smul_def, map_pow, map_mul, pow_add]; ring⟩

lemma Dvd_of_eq {n : ℕ} {x : PS ℓ} (y : PS ℓ) (h : x = C ((ℓ : ℤ_[ℓ]) ^ n) * y) :
    Dvd (ℓ : ℤ_[ℓ]) n x := ⟨y, by rw [h, smul_eq_C_mul]⟩

lemma map_zero_of_Dvd {x : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) 1 x) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) x = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [pow_one, smul_eq_C_mul, map_mul, map_C, map_natCast, ZMod.natCast_self, map_zero, zero_mul]

lemma Dvd_of_map {x : PS ℓ} (h : PowerSeries.map (PadicInt.toZMod (p := ℓ)) x = 0) :
    Dvd (ℓ : ℤ_[ℓ]) 1 x := by
  obtain ⟨y, hy⟩ := PS_dvd_of_map x h
  exact ⟨y, by rw [pow_one, hy]⟩

lemma map_one_of_Dvd {x : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) 1 (x - 1)) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) x = 1 := by
  have := map_zero_of_Dvd h
  rwa [map_sub, map_one, sub_eq_zero] at this

lemma Bq0_le_one {m : ℕ} (hm : m ≤ ℓ + 1) : Bq ℓ 0 m ≤ 1 := by
  rw [Bq, Int.toNat_le]
  have h : ((m : ℚ) - 0) / ((ℓ : ℚ) + 1) ≤ ((1 : ℤ) : ℚ) := by
    rw [sub_zero, div_le_iff₀ (by positivity)]
    push_cast; exact_mod_cast (by omega : m ≤ 1 * (ℓ + 1))
  exact_mod_cast Int.ceil_le.mpr h

include hℓ in
/-- an isobaric polynomial whose q-expansion is `≡ 0 (mod ℓ)` is divisible by `ℓ`. -/
lemma poly_dvd1 {Q : Poly ℓ} {w : ℕ} (hQ : Iso Q w) (h : Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] Q)) :
    ∃ Q' : Poly ℓ, Iso Q' w ∧ Q = (ℓ : ℤ_[ℓ]) • Q' := by
  have h0 : ev (ZMod ℓ) (MvPolynomial.map (PadicInt.toZMod (p := ℓ)) Q) = 0 := by
    rw [← map_ev]; exact map_zero_of_Dvd h
  obtain ⟨Q', hQ'⟩ := Poly_dvd_of_map Q (eq_zero_of_ev_eq_zero_modP hℓ (iso_map _ hQ) h0)
  exact ⟨Q', iso_smul_cancel (by rw [← hQ']; exact hQ), hQ'⟩

include hℓ in
lemma poly_dvd_pow (n : ℕ) : ∀ {Q : Poly ℓ} {w : ℕ}, Iso Q w → Dvd (ℓ : ℤ_[ℓ]) n (ev ℤ_[ℓ] Q) →
    ∃ Q' : Poly ℓ, Iso Q' w ∧ Q = (ℓ : ℤ_[ℓ]) ^ n • Q' := by
  induction n with
  | zero => intro Q w hQ _; exact ⟨Q, hQ, by rw [pow_zero, one_smul]⟩
  | succ n ih =>
    intro Q w hQ h
    obtain ⟨Q1, hQ1, rfl⟩ := poly_dvd1 hℓ hQ (Dvd_mono (by omega) h)
    obtain ⟨y, hy⟩ := h
    have h1 : Dvd (ℓ : ℤ_[ℓ]) n (ev ℤ_[ℓ] Q1) := ⟨y, smul_cancel PS_reg (by
      rw [← map_smul, hy, smul_smul, ← pow_succ'])⟩
    obtain ⟨Q2, hQ2, rfl⟩ := ih hQ1 h1
    exact ⟨Q2, hQ2, by rw [smul_smul, ← pow_succ']⟩

/-- `ℓ·f/E^k ∈ B_E(r)` for any classical `f` of weight `k(ℓ−1)`, `k ≤ ℓ+1`. -/
lemma Ap_low {k : ℕ} (hk : k ≤ ℓ + 1) {P : Poly ℓ} (hP : Iso P (k * (ℓ - 1))) :
    Ap hℓ (Bq ℓ 0) ((ℓ : ℤ_[ℓ]) • (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ k)) := by
  intro N
  obtain ⟨c, hcK, hc0, hcD⟩ := decompN hℓ N k P hP
  refine ⟨k + 1, fun m => (ℓ : ℤ_[ℓ]) • c m, fun m => Submodule.smul_mem _ _ (hcK m), ?_, fun m => ?_⟩
  · have := Dvd_smul (ℓ : ℤ_[ℓ]) hcD
    unfold Approx
    convert this using 1
    rw [smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_mul_assoc]
  · dsimp only
    by_cases hm : m ≤ k
    · exact Dvd_mono (Bq0_le_one (by omega)) ⟨c m, by rw [pow_one]⟩
    · rw [hc0 m (by omega), smul_zero]; exact Dvd_zero _

/-- `f/E^k ∈ B_E(r)` for classical `f` of weight `k(ℓ−1)`, `k ≤ ℓ+1`, with `f ≡ 1 (mod ℓ)`. -/
lemma Ap_const {k : ℕ} (hk : k ≤ ℓ + 1) {P : Poly ℓ} (hP : Iso P (k * (ℓ - 1)))
    (h : Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] P - 1)) : Ap hℓ (Bq ℓ 0) (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ k) := by
  have hA : Iso (hasseA ℓ hℓ ^ k) (k * (ℓ - 1)) :=
    iso_of_eq ((iso_hasseA hℓ).pow k) (by rw [smul_eq_mul])
  have hd : Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] (P - hasseA ℓ hℓ ^ k)) := by
    refine Dvd_of_map ?_
    rw [map_sub, map_pow, ev_hasseA_E, map_sub, map_one_of_Dvd h, map_pow, map_E, one_pow, sub_self]
  obtain ⟨Q', hQ', hQ'e⟩ := poly_dvd1 hℓ (iso_sub hP hA) hd
  have he : ev ℤ_[ℓ] P * Einv ℓ hℓ ^ k =
      1 + (ℓ : ℤ_[ℓ]) • (ev ℤ_[ℓ] Q' * Einv ℓ hℓ ^ k) := by
    have : P = hasseA ℓ hℓ ^ k + (ℓ : ℤ_[ℓ]) • Q' := by rw [← hQ'e]; ring
    rw [this, map_add, map_pow, ev_hasseA_E, map_smul, add_mul, ← mul_pow, E_mul_Einv, one_pow,
      smul_mul_assoc]
  rw [he]
  exact Ap_add (Ap_one (by simp [Bq])) (Ap_low hℓ hk hQ')

/-- **Fixed points of `ℓ`-adic contractions stay in an `Ap` class.** -/
theorem hensel_fix {B : ℕ → ℕ} (hB0 : B 0 = 0) {T : PS ℓ → PS ℓ}
    (hT1 : ∀ Y Y' n, Dvd (ℓ : ℤ_[ℓ]) n (Y - Y') → Dvd (ℓ : ℤ_[ℓ]) (n + 1) (T Y - T Y'))
    (hT2 : ∀ Y, Ap hℓ B Y → Ap hℓ B (T Y)) {y : PS ℓ} (hy : T y = y)
    (hy1 : Dvd (ℓ : ℤ_[ℓ]) 1 (y - 1)) : Ap hℓ B y := by
  have hap : ∀ n, Ap hℓ B (T^[n] 1) := by
    intro n
    induction n with
    | zero => exact Ap_one hB0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hT2 _ ih
  have hd : ∀ n, Dvd (ℓ : ℤ_[ℓ]) (n + 1) (y - T^[n] 1) := by
    intro n
    induction n with
    | zero => simpa using hy1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have e : y - T (T^[n] 1) = T y - T (T^[n] 1) := by rw [hy]
      rw [e]
      exact hT1 _ _ _ ih
  intro N
  obtain ⟨I, a, haK, haA, haB⟩ := hap N N
  exact ⟨I, a, haK, Dvd_sub_trans (Dvd_mono (Nat.le_succ N) (hd N)) haA, haB⟩

/-! ### `V(E)/E` -/

/-- the term identity behind "divide the modular equation by `ℓ^{ℓ−1}E^{ℓ+1}`". -/
lemma term_id {k : ℕ} (hk : k ≤ ℓ) (F V D : PS ℓ) :
    C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * (C ((-1) ^ k * (ℓ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ - k))) * (F * D ^ k) *
      (V * D) ^ (ℓ + 1 - k)) =
    D ^ (ℓ + 1) * ((-1) ^ k * F * (C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * V) ^ (ℓ + 1 - k)) := by
  obtain ⟨j, hj⟩ : ∃ j, ℓ = k + j := ⟨ℓ - k, by omega⟩
  rw [show ℓ + 1 - k = j + 1 by omega, show ℓ - k = j by omega,
    show ℓ + 1 = k + (j + 1) by omega]
  generalize ℓ - 1 = d
  generalize (ℓ : ℤ_[ℓ]) = L
  simp only [map_mul, map_pow, map_neg, map_one, mul_pow, pow_add, pow_mul]
  ring

/-- the coefficient of `y^{ℓ+1−k}`. -/
noncomputable def acoef (f : ℕ → Poly ℓ) (k : ℕ) : PS ℓ :=
  C ((-1) ^ k * (ℓ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ - k))) * (ev ℤ_[ℓ] (f k) * Einv ℓ hℓ ^ k)

lemma acoef_ell (f : ℕ → Poly ℓ) : acoef hℓ f ℓ = -(ev ℤ_[ℓ] (f ℓ) * Einv ℓ hℓ ^ ℓ) := by
  have hodd : Odd ℓ := Nat.odd_iff.mpr (odd_ell hℓ)
  rw [acoef]
  simp only [Nat.sub_self, mul_zero, pow_zero, mul_one, hodd.neg_one_pow, map_neg, map_one,
    neg_one_mul]

lemma acoef_eq_smul (f : ℕ → Poly ℓ) {k : ℕ} (hk : k < ℓ) :
    acoef hℓ f k = ((-1) ^ k * (ℓ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ - k) - 1)) •
      ((ℓ : ℤ_[ℓ]) • (ev ℤ_[ℓ] (f k) * Einv ℓ hℓ ^ k)) := by
  obtain ⟨e, he⟩ : ∃ e, (ℓ - 1) * (ℓ - k) = e + 1 := ⟨(ℓ - 1) * (ℓ - k) - 1, by
    have : 1 ≤ (ℓ - 1) * (ℓ - k) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  rw [acoef, he, Nat.add_sub_cancel, smul_smul, smul_eq_C_mul, pow_succ]
  ring_nf

lemma acoef_dvd (f : ℕ → Poly ℓ) {k : ℕ} (hk : k < ℓ) : Dvd (ℓ : ℤ_[ℓ]) 1 (acoef hℓ f k) := by
  rw [acoef_eq_smul hℓ f hk, smul_comm]
  exact ⟨_, by rw [pow_one]⟩

/-- **`V(E)/E ∈ B_E(r)`** (coordinates `v_i ≥ ⌈i/(ℓ+1)⌉`). -/
theorem Ap_VE_div_E : Ap hℓ (Bq ℓ 0) (Vl ℓ (E ℓ hℓ) * Einv ℓ hℓ) := by
  obtain ⟨f, hf, hsum, hdvd⟩ := modular_equation_E hℓ
  have hodd : Odd ℓ := Nat.odd_iff.mpr (odd_ell hℓ)
  have hZ : C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * expand ℓ (ell_ne_zero' ℓ) (E ℓ hℓ) =
      C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * Vl ℓ (E ℓ hℓ) := rfl
  rw [hZ, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, (hodd.add_one).neg_one_pow,
    one_mul] at hsum
  -- step A: `f_{ℓ+1} = ℓ^{ℓ−1} M`
  have hA : Dvd (ℓ : ℤ_[ℓ]) (ℓ - 1) (ev ℤ_[ℓ] (f (ℓ + 1))) := by
    have he : ev ℤ_[ℓ] (f (ℓ + 1)) = (-1 : ℤ_[ℓ]) • ∑ k ∈ Finset.range (ℓ + 1),
        (-1) ^ k * ev ℤ_[ℓ] (f k) * (C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * Vl ℓ (E ℓ hℓ)) ^ (ℓ + 1 - k) := by
      rw [neg_one_smul]; linear_combination hsum
    rw [he]
    refine Dvd_smul _ (Dvd.sum _ _ fun k hk => Dvd_of_eq ((-1) ^ k * ev ℤ_[ℓ] (f k) *
      (C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * Vl ℓ (E ℓ hℓ)) ^ (ℓ - k) * Vl ℓ (E ℓ hℓ)) ?_)
    have hk' := Finset.mem_range.mp hk
    rw [show ℓ + 1 - k = (ℓ - k) + 1 by omega, pow_succ]; ring
  obtain ⟨M, hM, hMe⟩ := poly_dvd_pow hℓ (ℓ - 1) (hf (ℓ + 1)) hA
  -- the divided equation
  have hid : ∑ k ∈ Finset.range (ℓ + 1), acoef hℓ f k * (Vl ℓ (E ℓ hℓ) * Einv ℓ hℓ) ^ (ℓ + 1 - k) +
      ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1) = 0 := by
    have hcz : C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) ≠ 0 := by
      intro h
      have := congrArg (constantCoeff) h
      rw [constantCoeff_C, map_zero] at this
      exact pow_ne_zero _ ell_ne_zero this
    refine (mul_eq_zero.mp ?_).resolve_left hcz
    simp only [acoef]
    rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k hk => term_id (k := k)
      (by have := Finset.mem_range.mp hk; omega) (ev ℤ_[ℓ] (f k)) (Vl ℓ (E ℓ hℓ)) (Einv ℓ hℓ)]
    rw [← Finset.mul_sum, show C ((ℓ : ℤ_[ℓ]) ^ (ℓ - 1)) * (ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1)) =
      Einv ℓ hℓ ^ (ℓ + 1) * ev ℤ_[ℓ] (f (ℓ + 1)) by rw [hMe, map_smul, smul_eq_C_mul]; ring,
      ← mul_add, hsum, mul_zero]
  -- split off `k = ℓ`
  rw [Finset.sum_range_succ, show ℓ + 1 - ℓ = 1 by omega, pow_one] at hid
  set y := Vl ℓ (E ℓ hℓ) * Einv ℓ hℓ with hy
  have hmapf : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ev ℤ_[ℓ] (f ℓ)) = 1 :=
    map_one_of_Dvd hdvd
  have hmapD : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Einv ℓ hℓ) = 1 := map_Einv ℓ hℓ
  have hmapy : PowerSeries.map (PadicInt.toZMod (p := ℓ)) y = 1 := by
    rw [hy, map_mul, hmapD, mul_one, Vl]
    change PowerSeries.map _ (PowerSeries.expand ℓ _ (E ℓ hℓ)) = 1
    rw [PowerSeries.map_expand, map_E, map_one]
  have hmapa : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (acoef hℓ f ℓ) = -1 := by
    rw [acoef_ell, map_neg, map_mul, map_pow, hmapf, hmapD, one_pow, mul_one]
  -- `M ≡ 1`
  have hMd : Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] M - 1) := by
    refine Dvd_of_map ?_
    have h0 := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) hid
    rw [map_add, map_add, map_sum, map_mul, hmapa, hmapy, mul_one,
      Finset.sum_eq_zero (fun k hk => by
        rw [map_mul, map_zero_of_Dvd (acoef_dvd hℓ f (Finset.mem_range.mp hk)), zero_mul]),
      zero_add, map_mul, map_pow, hmapD, one_pow, mul_one, map_zero] at h0
    rw [map_sub, map_one]; linear_combination h0
  -- the contraction
  have hT1 : ∀ Y Y' n, Dvd (ℓ : ℤ_[ℓ]) n (Y - Y') → Dvd (ℓ : ℤ_[ℓ]) (n + 1)
      (((1 + acoef hℓ f ℓ) * Y + ∑ k ∈ Finset.range ℓ, acoef hℓ f k * Y ^ (ℓ + 1 - k) +
          ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1)) -
        ((1 + acoef hℓ f ℓ) * Y' + ∑ k ∈ Finset.range ℓ, acoef hℓ f k * Y' ^ (ℓ + 1 - k) +
          ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1))) := by
    intro Y Y' n h
    have h1a : Dvd (ℓ : ℤ_[ℓ]) 1 (1 + acoef hℓ f ℓ) := by
      refine Dvd_of_map ?_
      rw [map_add, map_one, hmapa, add_neg_cancel]
    have e : ((1 + acoef hℓ f ℓ) * Y + ∑ k ∈ Finset.range ℓ, acoef hℓ f k * Y ^ (ℓ + 1 - k) +
          ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1)) -
        ((1 + acoef hℓ f ℓ) * Y' + ∑ k ∈ Finset.range ℓ, acoef hℓ f k * Y' ^ (ℓ + 1 - k) +
          ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1)) = (1 + acoef hℓ f ℓ) * (Y - Y') +
        ∑ k ∈ Finset.range ℓ, acoef hℓ f k * (Y ^ (ℓ + 1 - k) - Y' ^ (ℓ + 1 - k)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e, add_comm n 1]
    refine Dvd_add (Dvd_mul_mul h1a h) (Dvd.sum _ _ fun k hk =>
      Dvd_mul_mul (acoef_dvd hℓ f (Finset.mem_range.mp hk)) ?_)
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow Y Y' (ℓ + 1 - k)
    rw [hq, ← add_zero n]
    exact Dvd_mul_mul h ⟨q, by rw [pow_zero, one_smul]⟩
  have hB0 : Bq ℓ 0 0 = 0 := by simp [Bq]
  have hAa : ∀ k ∈ Finset.range ℓ, Ap hℓ (Bq ℓ 0) (acoef hℓ f k) := fun k hk => by
    have hk' := Finset.mem_range.mp hk
    rw [acoef_eq_smul hℓ f hk']
    exact Ap_smul _ (Ap_low hℓ (k := k) (by omega) (hf k))
  have hAℓ : Ap hℓ (Bq ℓ 0) (acoef hℓ f ℓ) := by
    rw [acoef_ell, ← neg_one_smul ℤ_[ℓ]]
    exact Ap_smul _ (Ap_const hℓ (Nat.le_succ ℓ) (hf ℓ) hdvd)
  have hAM : Ap hℓ (Bq ℓ 0) (ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1)) := Ap_const hℓ le_rfl hM hMd
  refine hensel_fix hℓ hB0 (T := fun Y => (1 + acoef hℓ f ℓ) * Y +
      ∑ k ∈ Finset.range ℓ, acoef hℓ f k * Y ^ (ℓ + 1 - k) + ev ℤ_[ℓ] M * Einv ℓ hℓ ^ (ℓ + 1))
    hT1 ?_ ?_ (Dvd_of_map (by rw [map_sub, hmapy, map_one, sub_self]))
  · intro Y hY
    refine Ap_add (Ap_add (Ap_mul B1_mul (Ap_add (Ap_one hB0) hAℓ) hY) ?_) hAM
    refine Finset.sum_induction _ (Ap hℓ (Bq ℓ 0)) (fun _ _ => Ap_add) ?_ fun k hk =>
      Ap_mul B1_mul (hAa k hk) (Ap_pow hℓ B1_mul B1_zero hY _)
    simpa using Ap_smul (0 : ℤ_[ℓ]) (Ap_one (hℓ := hℓ) (B := Bq ℓ 0) hB0)
  · dsimp only
    linear_combination hid

/-- **(HG) holds**: `G = E/V(E)` has Katz coordinates `v_i ≥ ⌈i/(ℓ+1)⌉`. -/
theorem HG_holds : HG ℓ hℓ := by
  have hy := Ap_VE_div_E hℓ
  set y := Vl ℓ (E ℓ hℓ) * Einv ℓ hℓ with hy'
  have hyG : y * Gl ℓ hℓ = 1 := by
    rw [hy', Gl]
    calc Vl ℓ (E ℓ hℓ) * Einv ℓ hℓ * (E ℓ hℓ * Vl ℓ (Einv ℓ hℓ))
        = Vl ℓ (E ℓ hℓ * Einv ℓ hℓ) * (E ℓ hℓ * Einv ℓ hℓ) := by rw [map_mul]; ring
      _ = 1 := by rw [E_mul_Einv, map_one, one_mul]
  have hmapy : PowerSeries.map (PadicInt.toZMod (p := ℓ)) y = 1 := by
    rw [hy', map_mul, map_Einv, mul_one, Vl]
    change PowerSeries.map _ (PowerSeries.expand ℓ _ (E ℓ hℓ)) = 1
    rw [PowerSeries.map_expand, map_E, map_one]
  have h1y : Dvd (ℓ : ℤ_[ℓ]) 1 (1 - y) :=
    Dvd_of_map (by rw [map_sub, map_one, hmapy, sub_self])
  have hB0 : Bq ℓ 0 0 = 0 := by simp [Bq]
  have hAp1y : Ap hℓ (Bq ℓ 0) (1 - y) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ] y]
    exact Ap_add (Ap_one hB0) (Ap_smul _ hy)
  have hG : Ap hℓ (Bq ℓ 0) (Gl ℓ hℓ) := by
    refine hensel_fix hℓ hB0 (T := fun Y => (1 - y) * Y + 1) ?_ ?_ ?_ ?_
    · intro Y Y' n h
      have e : (1 - y) * Y + 1 - ((1 - y) * Y' + 1) = (1 - y) * (Y - Y') := by ring
      dsimp only
      rw [e, add_comm]
      exact Dvd_mul_mul h1y h
    · intro Y hY
      exact Ap_add (Ap_mul B1_mul hAp1y hY) (Ap_one hB0)
    · dsimp only; linear_combination (-1 : PS ℓ) * hyG
    · refine Dvd_of_map ?_
      rw [map_sub, map_one, Gl, map_mul, map_E, one_mul, Vl]
      change PowerSeries.map _ (PowerSeries.expand ℓ _ (Einv ℓ hℓ)) - 1 = 0
      rw [PowerSeries.map_expand, map_Einv, map_one, sub_self]
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap hG
  exact ⟨c, hc, fun i => by simpa [Bq] using hcb i⟩

end VLayer
