import RamanujanTau.VLayer.ModEq
import RamanujanTau.UpContraction.TateU
import RamanujanTau.DBound.Limit

/-!
# `U(b/E^j)` has an integral Katz expansion, unconditionally

For an isobaric `P ∈ ℤ_ℓ[E₄,E₆]` of weight `j(ℓ−1)`, the q-series `U_ℓ(P/E^j)` has an *integral* Katz
expansion `Σ c_i/E^i`, `c_i ∈ B_i` (`U_katz_int`, `U_isKatz`). No geometry enters:

* `E^{ℓ^n} ≡ 1 (mod ℓ^{n+1})`, so `P/E^j ≡ P·E^{j(ℓ^n−1)} =: F` (mod `ℓ^{n+1}`), a classical form of
  weight `k = jℓ^n(ℓ−1)`;
* `U F = T_ℓ F − ℓ^{k−1} V F` and `T_ℓ F` is classical over `ℤ_ℓ` (`exists_hecke_Zp`: `heckePoly` over
  `ℚ_ℓ` + `ModP.descend`);
* `T_ℓ F / E^{jℓ^n}` is a finite Katz series (`DBound.decompN`), and `E^{jℓ^n} ≡ 1 (mod ℓ^{n+1})`.

This removes the "existence/rationality of the Katz expansion of `U f`" part of the hypotheses of
`UpContraction.UB`; what remains is the *decay* (overconvergence) and the geometric description.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBound
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound HeckeQExp

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

lemma U_eq_Up (F : PS ℓ) : BoylanWebb.U ℓ F = UpContraction.Up ℓ F := rfl

include hℓ in
/-- **`T_ℓ` on classical forms over `ℤ_ℓ`.** -/
theorem exists_hecke_Zp {k : ℕ} (hk : 1 ≤ k) {P : Poly ℓ} (hP : Iso P k) :
    ∃ P' : Poly ℓ, Iso P' k ∧
      ev ℤ_[ℓ] P' = Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P) := by
  set Pq := MvPolynomial.map (VLayer.ιz ℓ) P
  have hPq : Iso Pq k := iso_map _ hP
  have hev := ev_heckePoly ℓ hPq
  have hc : algebraMap ℚ ℚ_[ℓ] (mulQ ℓ k) = VLayer.ιz ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) := by
    rw [mulQ_of_pos ℓ hk]; simp
  obtain ⟨P', hP', hP'e⟩ := descend (VLayer.ιz ℓ) Subtype.val_injective (isUnit_1728_Zp hℓ) k
    (heckePoly ℓ Pq) (iso_heckePoly ℓ hPq)
    ⟨Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P), by rw [map_Tq, hev, hc, map_ev]⟩
  refine ⟨P', hP', PowerSeries.map_injective (VLayer.ιz ℓ) Subtype.val_injective ?_⟩
  rw [map_ev, hP'e, hev, hc, map_Tq, map_ev]

/-! ### divisibility helpers -/

lemma Dvd_mul_left' {N : ℕ} (y : PS ℓ) {x : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) N x) :
    Dvd (ℓ : ℤ_[ℓ]) N (y * x) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨y * z, by rw [mul_smul_comm]⟩

lemma Dvd_neg' {N : ℕ} {x : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) N x) : Dvd (ℓ : ℤ_[ℓ]) N (-x) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨-z, by rw [smul_neg]⟩

lemma Dvd_U {N : ℕ} {x : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) N x) : Dvd (ℓ : ℤ_[ℓ]) N (BoylanWebb.U ℓ x) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨BoylanWebb.U ℓ z, by rw [← Ulin_apply, map_smul, Ulin_apply]⟩

lemma Dvd_of_dvd {N : ℕ} {x : PS ℓ} (h : (ℓ : PS ℓ) ^ N ∣ x) : Dvd (ℓ : ℤ_[ℓ]) N x := by
  obtain ⟨z, rfl⟩ := h
  refine ⟨z, ?_⟩
  rw [smul_eq_C_mul, map_pow, map_natCast]

lemma dvd_E_sub_one : (ℓ : PS ℓ) ∣ E ℓ hℓ - 1 := by
  obtain ⟨y, hy⟩ := PS_dvd_of_map (E ℓ hℓ - 1) (by rw [map_sub, map_E, map_one, sub_self])
  exact ⟨y, by rw [hy, smul_eq_C_mul, map_natCast]⟩

/-- **`E^{jℓ^n} ≡ 1 (mod ℓ^{n+1})`.** -/
lemma Dvd_E_pow_sub_one (n j : ℕ) : Dvd (ℓ : ℤ_[ℓ]) (n + 1) (E ℓ hℓ ^ (j * ℓ ^ n) - 1) := by
  apply Dvd_of_dvd
  have h1 := dvd_sub_pow_of_dvd_sub (dvd_E_sub_one hℓ) n
  rw [one_pow] at h1
  refine h1.trans ?_
  rw [mul_comm, pow_mul]
  simpa using sub_dvd_pow_sub_pow (E ℓ hℓ ^ ℓ ^ n) 1 j

/-! ### the main lemma -/

lemma U_katz_int_pos {j : ℕ} (hj : 1 ≤ j) {P : Poly ℓ} (hP : Iso P (j * (ℓ - 1))) :
    Ap hℓ (fun _ => 0) (BoylanWebb.U ℓ (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j)) := by
  intro N
  set K := j * ℓ ^ N with hK
  have hl1 : 1 ≤ ℓ - 1 := by omega
  have hNK : N < ℓ ^ N := Nat.lt_pow_self (by omega)
  have hjK : j ≤ K := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  set m := K - j with hm
  set k := K * (ℓ - 1) with hk
  have hk1 : N + 1 ≤ k - 1 := by
    have : ℓ ^ N ≤ K := Nat.le_mul_of_pos_left _ (by omega)
    have : 4 * K ≤ k := by rw [hk, mul_comm 4 K]; exact Nat.mul_le_mul_left K (by omega)
    omega
  have hF : Iso (P * hasseA ℓ hℓ ^ m) k := by
    refine iso_of_eq (hP.mul ((iso_hasseA hℓ).pow m)) ?_
    rw [smul_eq_mul, hk, ← add_mul]; congr 1; omega
  obtain ⟨PT, hPT, hPTe⟩ := exists_hecke_Zp hℓ (by omega) hF
  obtain ⟨c, hcK, -, hcD⟩ := decompN hℓ N K PT (by rw [← hk]; exact hPT)
  refine ⟨K + 1, c, hcK, ?_, fun i => ⟨c i, by rw [pow_zero, one_smul]⟩⟩
  unfold Approx
  set S := ∑ i ∈ Finset.range (K + 1), ev ℤ_[ℓ] (c i) * Einv ℓ hℓ ^ i
  set F := ev ℤ_[ℓ] (P * hasseA ℓ hℓ ^ m)
  have hEK : Dvd (ℓ : ℤ_[ℓ]) N (E ℓ hℓ ^ K - 1) := Dvd_mono (Nat.le_succ N) (Dvd_E_pow_sub_one hℓ N j)
  have hEE : ∀ n, E ℓ hℓ ^ n * Einv ℓ hℓ ^ n = 1 := fun n => by rw [← mul_pow, E_mul_Einv, one_pow]
  -- the four pieces
  have h1 : Dvd (ℓ : ℤ_[ℓ]) N (BoylanWebb.U ℓ (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j) - BoylanWebb.U ℓ F) := by
    rw [← BoylanWebb.U_sub]
    apply Dvd_U
    have e : ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j - F =
        -(ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j * (E ℓ hℓ ^ K - 1)) := by
      have hKe : K = j + m := by omega
      simp only [F, map_mul, map_pow, ev_hasseA_E hℓ]
      rw [hKe, pow_add]
      linear_combination (ev ℤ_[ℓ] P * E ℓ hℓ ^ m) * hEE j
    rw [e]; exact Dvd_neg' (Dvd_mul_left' _ hEK)
  have h2 : Dvd (ℓ : ℤ_[ℓ]) N (BoylanWebb.U ℓ F - ev ℤ_[ℓ] PT) := by
    rw [hPTe, Tq_eq ℓ (VLayer.ell_ne_zero' ℓ), ← U_eq_Up, sub_add_cancel_left]
    apply Dvd_neg'
    rw [mul_comm]
    refine Dvd_mul_left' _ ⟨(ℓ : ℤ_[ℓ]) ^ (k - 1 - N) • 1, ?_⟩
    rw [smul_smul, ← pow_add, show N + (k - 1 - N) = k - 1 by omega, smul_eq_C_mul, mul_one]
  have h3 : Dvd (ℓ : ℤ_[ℓ]) N (ev ℤ_[ℓ] PT - ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ K) := by
    have e : ev ℤ_[ℓ] PT - ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ K =
        ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ K * (E ℓ hℓ ^ K - 1) := by
      linear_combination (-ev ℤ_[ℓ] PT) * hEE K
    rw [e]; exact Dvd_mul_left' _ hEK
  have h4 : Dvd (ℓ : ℤ_[ℓ]) N (ev ℤ_[ℓ] PT * Einv ℓ hℓ ^ K - S) := hcD
  have := Dvd_add (Dvd_add (Dvd_add h1 h2) h3) h4
  convert this using 1
  ring

/-- **`U(P/E^j)` has integral approximate Katz expansions** (all `j`, all isobaric `P` of weight
`j(ℓ−1)`). -/
theorem U_katz_int (j : ℕ) {P : Poly ℓ} (hP : Iso P (j * (ℓ - 1))) :
    Ap hℓ (fun _ => 0) (BoylanWebb.U ℓ (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j)) := by
  have hP' : Iso (P * hasseA ℓ hℓ) ((j + 1) * (ℓ - 1)) :=
    iso_of_eq (hP.mul (iso_hasseA hℓ)) (by ring)
  have h := U_katz_int_pos hℓ (Nat.le_add_left 1 j) hP'
  have e : ev ℤ_[ℓ] (P * hasseA ℓ hℓ) * Einv ℓ hℓ ^ (j + 1) = ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j := by
    rw [map_mul, ev_hasseA_E hℓ, pow_succ]
    linear_combination (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ j) * E_mul_Einv ℓ hℓ
  rwa [e] at h

/-- Elements of `Kpiece j` are isobaric of weight `j(ℓ−1)`. -/
lemma iso_of_Kpiece {j : ℕ} {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j) : Iso x (j * (ℓ - 1)) := by
  intro d hd
  have := (mem_Kpiece hℓ).mp hx (MvPolynomial.mem_support_iff.mpr hd)
  rw [weight_wt]; exact this.1

/-- **The integral Katz expansion of `U(b/E^j)`**, `b ∈ B_j`. -/
theorem U_isKatz (j : ℕ) {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j) :
    ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c (BoylanWebb.U ℓ (ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) := by
  obtain ⟨c, hc, -⟩ := isKatz_of_Ap (U_katz_int hℓ j (iso_of_Kpiece hℓ hx))
  exact ⟨c, hc⟩

end UBound
