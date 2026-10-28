import RamanujanTau.VLayer.HG
import RamanujanTau.VLayer.ModEqGen

/-!
# `Q = E/A_ℓ ∈ B_E(r)` from the modular equation of `Δ`

`Q^{12} Δ^ℓ = E^{12} V(Δ)`, and `ℓ^{12} V(Δ)` is a root of the level-`ℓ` modular equation of `Δ`
(`VLayer.modular_equation`, `P = Δ`, `w = 12`):

  `Σ_{k ≤ ℓ+1} (−1)^k g_k (ℓ^{12} VΔ)^{ℓ+1−k} = 0`,   `g_k` classical of weight `12k`.

From the conjugates `Δ(ζ^j t)`: `g_ℓ(0) = 0` and `[q¹] g_ℓ = 1`, so `g_ℓ = Δ·h` with `h(0) = 1`;
the equation forces `g_{ℓ+1} = ℓ^{12} c Δ^{ℓ+1}`. Dividing by `ℓ^{12}Δ^{ℓ+1}` and putting
`VΔ = Q^{12}Δ^ℓ/E^{12}`:

  `c − (h/E^{12}) Q^{12} + Σ_{k<ℓ} (−1)^k ℓ^{12(ℓ−k)} (g_k Δ^{ℓ(ℓ−k)−1}/E^{12(ℓ+1−k)}) Q^{12(ℓ+1−k)} = 0.`

All Katz indices are `≤ 12(ℓ+1)`, the coefficients of `Q^{12d}`, `d ≥ 2`, carry `ℓ^{12}`, and the
index-12 coefficient `h/E^{12}` is `≡ 1` (for `ℓ ≥ 11`, `12 ≤ ℓ + 1`). So, as for `HG`, `Q^{12}` is the
fixed point of a contraction preserving `{v_i ≥ ⌈i/(ℓ+1)⌉}`; a Hensel 12th root gives `Q`.

* **`Q_InB1`**: `Q` has Katz coordinates `v_i ≥ ⌈i/(ℓ+1)⌉` (for `ℓ ≥ 11`).

This is the `B_E(r)` (not the sharp `B_E(r^ℓ)`) form of (I2); it is what `HW` needs for the factor
`Q^ℓ` of `(E^sW)² = Q^ℓ V(Q) G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### `Δ`-divisibility of isobaric polynomials -/

include hℓ in
lemma disc_dvd {Q : Poly ℓ} {k : ℕ} (hQ : Iso Q k) (h0 : constantCoeff (ev ℤ_[ℓ] Q) = 0) :
    ∃ Q' : Poly ℓ, Iso Q' (k - 12) ∧ Q = Pdisc hℓ * Q' := by
  obtain ⟨Q1, hQ1, -, hQe⟩ := exists_div hQ
  rw [← constantCoeff_ev, h0, map_zero, zero_mul, zero_add] at hQe
  refine ⟨MvPolynomial.C 1728 * Q1, hQ1.C_mul _, ?_⟩
  rw [hQe, Pdisc, mul_assoc, ← mul_assoc (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2),
    mul_comm (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) (MvPolynomial.C 1728), ← mul_assoc,
    ← mul_assoc, ← map_mul, (isUnit_1728_Zp (p := ℓ) hℓ).val_inv_mul, map_one, one_mul]

lemma Dl_eq : Dl ℓ = X * Pl ℓ ^ 24 := by
  rw [Dl, Dq, map_mul, map_pow, map_X]; rfl

lemma isUnit_Pl : IsUnit (Pl ℓ) := IsUnit.of_mul_eq_one _ Pl_mul_Pinv

include hℓ in
lemma disc_pow_dvd (n : ℕ) : ∀ (m : ℕ) (Q : Poly ℓ), Iso Q (12 * n + m) →
    (X : PS ℓ) ^ n ∣ ev ℤ_[ℓ] Q → ∃ Q' : Poly ℓ, Iso Q' m ∧ Q = Pdisc hℓ ^ n * Q' := by
  induction n with
  | zero => intro m Q hQ _; exact ⟨Q, by simpa using hQ, by rw [pow_zero, one_mul]⟩
  | succ n ih =>
    intro m Q hQ hd
    have h0 : constantCoeff (ev ℤ_[ℓ] Q) = 0 := by
      obtain ⟨z, hz⟩ := hd
      rw [hz, map_mul, map_pow, constantCoeff_X, zero_pow (Nat.succ_ne_zero n), zero_mul]
    obtain ⟨Q1, hQ1, rfl⟩ := disc_dvd hℓ hQ h0
    have hQ1' : Iso Q1 (12 * n + m) := iso_of_eq hQ1 (by omega)
    have hd1 : (X : PS ℓ) ^ n ∣ ev ℤ_[ℓ] Q1 := by
      rw [map_mul, ev_Pdisc, Dl_eq, pow_succ, mul_comm ((X : PS ℓ) ^ n) X, mul_assoc] at hd
      have h2 := (mul_dvd_mul_iff_left (X_ne_zero (R := ℤ_[ℓ]))).mp hd
      exact ((isUnit_Pl.pow 24).dvd_mul_left).mp h2
    obtain ⟨Q', hQ', rfl⟩ := ih m Q1 hQ1' hd1
    exact ⟨Q', hQ', by rw [pow_succ', mul_assoc]⟩

lemma iso_zero_eq_C {Q : Poly ℓ} (hQ : Iso Q 0) : Q = MvPolynomial.C (MvPolynomial.eval one2 Q) := by
  obtain ⟨Q1, -, hQ0, hQe⟩ := exists_div hQ
  rw [hQ0 (by norm_num), mul_zero, add_zero] at hQe
  rw [hQe]
  conv_rhs => rw [hQe]
  simp [base, bexp0, bexp1]

/-! ### the conjugates of `Δ` -/

lemma FK_disc : FK (Pdisc hℓ) = X * map (Int.castRingHom (PadicAlgCl ℓ))
    (MockTheta5.JTP.qfacInf ^ 24) := by
  rw [FK, Fq, ev_Pdisc, Dl, Dq, psmap_map, psmap_map,
    show ((ιq ℓ).comp (ιz ℓ)).comp (Int.castRingHom ℤ_[ℓ]) = Int.castRingHom (PadicAlgCl ℓ) from
      RingHom.ext_int _ _, map_mul, map_X]

lemma constantCoeff_qfacInf : constantCoeff MockTheta5.JTP.qfacInf = 1 := by
  simp [MockTheta5.JTP.qfacInf, MockTheta5.Bailey.qfac]

lemma prod_zeta {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (hodd : Odd ℓ) :
    ∏ j : Fin ℓ, ζ ^ (j : ℕ) = 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun j => ζ ^ j), Finset.prod_pow_eq_pow_sum,
    hζ.pow_eq_one_iff_dvd]
  have h2 := Finset.sum_range_id_mul_two ℓ
  obtain ⟨k, hk⟩ := hodd
  have : ∑ i ∈ Finset.range ℓ, i = ℓ * k := by
    have : (∑ i ∈ Finset.range ℓ, i) * 2 = ℓ * k * 2 := by rw [h2, hk]; simp; ring
    omega
  rw [this]; exact dvd_mul_right _ _

/-- **`e_ℓ` of the conjugates of `Δ`**: zero constant term, and `t^ℓ`-coefficient `1`. -/
theorem esymm_ell_disc {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) :
    constantCoeff (MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ)
        (MvPolynomial.esymm (Option (Fin ℓ)) ℤ ℓ)) = 0 ∧
      coeff ℓ (MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ)
        (MvPolynomial.esymm (Option (Fin ℓ)) ℤ ℓ)) = 1 := by
  classical
  set G := map (Int.castRingHom (PadicAlgCl ℓ)) (MockTheta5.JTP.qfacInf ^ 24) with hG
  have hG0 : constantCoeff G = 1 := by
    rw [hG, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      map_pow, constantCoeff_qfacInf, one_pow, map_one]
  set v : Option (Fin ℓ) → PowerSeries (PadicAlgCl ℓ) := fun i =>
    Option.elim i 1 (fun j => C (ζ ^ (j : ℕ)) * rescale (ζ ^ (j : ℕ)) G) with hv
  have hys : ∀ j : Fin ℓ, ys (Pdisc hℓ) 12 ζ (some j) = X * v (some j) := by
    intro j
    simp only [ys, FK_disc, hv, Option.elim, map_mul, rescale_X, ← hG]
    ring
  have hnone : (X : PowerSeries (PadicAlgCl ℓ)) ^ (ℓ * ℓ) ∣ ys (Pdisc hℓ) 12 ζ none := by
    simp only [ys, FK_disc, map_mul, expand_X, ← hG]
    refine ⟨expand ℓ (ell_ne_zero' ℓ) (C ((ℓ : PadicAlgCl ℓ) ^ 12) *
      expand ℓ (ell_ne_zero' ℓ) G), ?_⟩
    rw [show expand ℓ (ell_ne_zero' ℓ) (X ^ ℓ : PowerSeries (PadicAlgCl ℓ)) = X ^ (ℓ * ℓ) by
      rw [map_pow, expand_X, ← pow_mul], map_mul]; ring
  have hodd : Odd ℓ := Nat.odd_iff.mpr (odd_ell hℓ)
  have hcard : (Finset.univ.erase (none : Option (Fin ℓ))).card = ℓ := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
      Fintype.card_fin, Nat.add_sub_cancel]
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
  constructor
  · refine Finset.sum_eq_zero fun t ht => ?_
    have htc := (Finset.mem_powersetCard.mp ht).2
    obtain ⟨i, hi⟩ : t.Nonempty := Finset.card_pos.mp (by rw [htc]; exact hℓp.out.pos)
    refine Finset.prod_eq_zero hi ?_
    cases i with
    | none =>
      obtain ⟨z, hz⟩ := hnone
      rw [hz, map_mul, map_pow, constantCoeff_X, zero_pow (by positivity), zero_mul]
    | some j => rw [hys, map_mul, constantCoeff_X, zero_mul]
  · rw [← Finset.sum_filter_add_sum_filter_not _ (fun t => none ∈ t)]
    have hsing : (Finset.powersetCard ℓ (Finset.univ : Finset (Option (Fin ℓ)))).filter
        (fun t => ¬ none ∈ t) = {Finset.univ.erase none} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, hc⟩, hn⟩
        exact Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_erase.mpr
          ⟨fun h => hn (h ▸ hi), Finset.mem_univ _⟩) (by rw [hc, hcard])
      · rintro rfl
        exact ⟨⟨Finset.subset_univ _, hcard⟩, Finset.notMem_erase _ _⟩
    rw [hsing, Finset.sum_singleton]
    rw [Finset.sum_eq_zero (fun t ht => ?_), zero_add]
    · -- the product over `univ.erase none`
      have hprod : ∏ i ∈ Finset.univ.erase none, ys (Pdisc hℓ) 12 ζ i =
          X ^ ℓ * ∏ j : Fin ℓ, v (some j) := by
        rw [Finset.prod_congr rfl (g := fun i => X * v i) fun i hi => by
          cases i with
          | none => exact absurd rfl (Finset.mem_erase.mp hi).1
          | some j => exact hys j]
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
          Finset.prod_erase _ (by simp [hv] : v none = 1), Fintype.prod_option]
        simp [hv]
      rw [hprod, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
        map_prod]
      simp only [hv, Option.elim, map_mul, ← coeff_zero_eq_constantCoeff_apply,
        coeff_rescale, pow_zero, one_mul]
      rw [coeff_zero_eq_constantCoeff_apply, hG0]
      simp only [mul_one, coeff_zero_C]
      exact prod_zeta hζ hodd
    · have hn := (Finset.mem_filter.mp ht).2
      rw [← Finset.mul_prod_erase t _ hn]
      obtain ⟨z, hz⟩ := hnone
      rw [hz, mul_assoc, coeff_X_pow_mul', if_neg]
      have := hℓp.out.two_le
      nlinarith


/-! ### the `Q`-identities -/

lemma Vl_Dl : Vl ℓ (Dl ℓ) = X ^ ℓ * Vl ℓ (Pl ℓ) ^ 24 := by
  rw [Dl_eq, map_mul, map_pow]
  congr 1
  change PowerSeries.expand ℓ _ X = X ^ ℓ
  rw [PowerSeries.expand_X]

/-- `Q^{12} Δ^ℓ = E^{12} V(Δ)`. -/
lemma Q12_id : Ql ℓ hℓ ^ 12 * Dl ℓ ^ ℓ = E ℓ hℓ ^ 12 * Vl ℓ (Dl ℓ) := by
  calc Ql ℓ hℓ ^ 12 * Dl ℓ ^ ℓ
      = E ℓ hℓ ^ 12 * (X ^ ℓ * Vl ℓ (Pl ℓ) ^ 24) * (Pl ℓ * Pinv ℓ) ^ (24 * ℓ) := by
        rw [Ql, Dl_eq]; ring
    _ = _ := by rw [Pl_mul_Pinv, one_pow, mul_one, Vl_Dl]

/-- `Q ≡ 1 (mod ℓ)`. -/
lemma map_Ql : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Ql ℓ hℓ) = 1 := by
  have hc : (PadicInt.toZMod (p := ℓ)).comp (Int.castRingHom ℤ_[ℓ]) = Int.castRingHom (ZMod ℓ) :=
    RingHom.ext_int _ _
  have hP : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Pl ℓ) = TauCong.Ψ ℓ MockTheta5.JTP.qfacInf := by
    rw [Pl, psmap_map, hc]; rfl
  have hPi : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Pinv ℓ) =
      TauCong.Ψ ℓ MockTheta5.JTP.partitionGF := by
    rw [Pinv, psmap_map, hc]; rfl
  have hV : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Vl ℓ (Pl ℓ)) =
      (TauCong.Ψ ℓ MockTheta5.JTP.qfacInf) ^ ℓ := by
    rw [Vl]
    change PowerSeries.map _ (PowerSeries.expand ℓ _ (Pl ℓ)) = _
    rw [PowerSeries.map_expand, hP]
    have hfr : (TauCong.Ψ ℓ MockTheta5.JTP.qfacInf) ^ ℓ =
        PowerSeries.map (Int.castRingHom (ZMod ℓ))
          (PowerSeries.expand ℓ (ell_ne_zero' ℓ) MockTheta5.JTP.qfacInf) := by
      rw [show (TauCong.Ψ ℓ MockTheta5.JTP.qfacInf) ^ ℓ =
        (TauCong.Ψ ℓ MockTheta5.JTP.qfacInf) ^ (ℓ ^ 1) by rw [pow_one], TauCong.frob_qfacInf ℓ 1]
      change PowerSeries.map _ (PowerSeries.expand (ℓ ^ 1) _ _) = _
      rw [DBound.expand_congr (pow_one ℓ)]
    rw [hfr]
    change PowerSeries.expand ℓ _ (PowerSeries.map _ _) = _
    rw [PowerSeries.map_expand]
  rw [Ql, map_mul, map_mul, map_pow, map_pow, map_E, hV, hPi, one_mul, ← pow_mul, mul_comm ℓ 2,
    ← mul_pow, ← map_mul, BoylanWebb.qfac_mul_pgf, map_one, one_pow]

/-! ### generalized helpers -/

lemma Bq0_le_of {n c : ℕ} (h : n ≤ c * (ℓ + 1)) : Bq ℓ 0 n ≤ c := by
  rw [Bq, Int.toNat_le]
  have h' : ((n : ℚ) - 0) / ((ℓ : ℚ) + 1) ≤ ((c : ℤ) : ℚ) := by
    rw [sub_zero, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  exact_mod_cast Int.ceil_le.mpr h'

/-- `ℓ^e·f/E^n ∈ B_E(r)` when `e ≥ ⌈n/(ℓ+1)⌉`. -/
lemma Ap_lowe {n e : ℕ} (he : Bq ℓ 0 n ≤ e) {P : Poly ℓ} (hP : Iso P (n * (ℓ - 1))) :
    Ap hℓ (Bq ℓ 0) ((ℓ : ℤ_[ℓ]) ^ e • (ev ℤ_[ℓ] P * Einv ℓ hℓ ^ n)) := by
  intro N
  obtain ⟨c, hcK, hc0, hcD⟩ := decompN hℓ N n P hP
  refine ⟨n + 1, fun m => (ℓ : ℤ_[ℓ]) ^ e • c m, fun m => Submodule.smul_mem _ _ (hcK m), ?_,
    fun m => ?_⟩
  · have := Dvd_smul ((ℓ : ℤ_[ℓ]) ^ e) hcD
    unfold Approx
    convert this using 1
    rw [smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_mul_assoc]
  · dsimp only
    by_cases hm : m ≤ n
    · have : Bq ℓ 0 m ≤ Bq ℓ 0 n := by
        unfold Bq
        refine Int.toNat_le_toNat (Int.ceil_mono (div_le_div_of_nonneg_right ?_ (by positivity)))
        linarith [(Nat.cast_le (α := ℚ)).mpr hm]
      exact Dvd_mono (this.trans he) ⟨c m, rfl⟩
    · rw [hc0 m (by omega), smul_zero]; exact Dvd_zero _

/-- **`hensel_fix` with an invariant set.** -/
theorem hensel_fixS {B : ℕ → ℕ} (hB0 : B 0 = 0) {T : PS ℓ → PS ℓ} (S : PS ℓ → Prop) (hS1 : S 1)
    (hST : ∀ Y, S Y → S (T Y))
    (hT1 : ∀ Y Y' n, S Y → S Y' → Dvd (ℓ : ℤ_[ℓ]) n (Y - Y') → Dvd (ℓ : ℤ_[ℓ]) (n + 1) (T Y - T Y'))
    (hT2 : ∀ Y, Ap hℓ B Y → Ap hℓ B (T Y)) {y : PS ℓ} (hyS : S y) (hy : T y = y)
    (hy1 : Dvd (ℓ : ℤ_[ℓ]) 1 (y - 1)) : Ap hℓ B y := by
  have hS : ∀ n, S (T^[n] 1) := by
    intro n
    induction n with
    | zero => exact hS1
    | succ n ih => rw [Function.iterate_succ_apply']; exact hST _ ih
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
      exact hT1 _ _ _ hyS (hS n) ih
  intro N
  obtain ⟨I, a, haK, haA, haB⟩ := hap N N
  exact ⟨I, a, haK, Dvd_sub_trans (Dvd_mono (Nat.le_succ N) (hd N)) haA, haB⟩

/-- the term identity for dividing the `Δ`-modular equation by `ℓ^{12}Δ^{ℓ+1}`. -/
lemma term12 (e a b : ℕ) (hab : (ℓ + 1) + a = ℓ * e) (hb : 12 + b = 12 * e) (s : ℤ_[ℓ])
    (G F W D : PS ℓ) :
    C ((ℓ : ℤ_[ℓ]) ^ 12) * F ^ (ℓ + 1) * (C (s * (ℓ : ℤ_[ℓ]) ^ b) * (G * F ^ a * D ^ (12 * e)) *
      W ^ e) = C s * G * (C ((ℓ : ℤ_[ℓ]) ^ 12) * (W * F ^ ℓ * D ^ 12)) ^ e := by
  have h1 : (C ((ℓ : ℤ_[ℓ]) ^ 12) : PS ℓ) ^ e = C ((ℓ : ℤ_[ℓ]) ^ 12) * C ((ℓ : ℤ_[ℓ]) ^ b) := by
    rw [← map_pow, ← pow_mul, ← map_mul, ← pow_add, hb]
  have h2 : (F ^ ℓ) ^ e = F ^ (ℓ + 1) * F ^ a := by rw [← pow_mul, ← hab, pow_add]
  have h3 : (D ^ 12) ^ e = D ^ (12 * e) := by rw [← pow_mul]
  rw [mul_pow, mul_pow, mul_pow, h1, h2, h3, map_mul]
  ring

lemma arith12 {k : ℕ} (hk : k < ℓ) :
    (ℓ + 1) + (ℓ * (ℓ - k) - 1) = ℓ * (ℓ + 1 - k) ∧ 12 + 12 * (ℓ - k) = 12 * (ℓ + 1 - k) ∧
      12 * (k + (ℓ * (ℓ - k) - 1)) = 12 * (ℓ + 1 - k) * (ℓ - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = k + j + 1 := ⟨ℓ - k - 1, by omega⟩
  have e1 : k + j + 1 - k = j + 1 := by omega
  have e2 : k + j + 1 + 1 - k = j + 2 := by omega
  have e3 : k + j + 1 - 1 = k + j := by omega
  rw [e1, e2, e3]
  have e4 : (k + j + 1) * (j + 1) = (k * j + k + j * j + 2 * j) + 1 := by ring
  rw [e4]
  refine ⟨?_, by ring, ?_⟩
  · rw [Nat.add_sub_cancel]; ring
  · rw [Nat.add_sub_cancel]; ring

/-! ### `Q^{12} ∈ B_E(r)` -/

/-- **`Q^{12}` has Katz coordinates `v_i ≥ ⌈i/(ℓ+1)⌉`** (`ℓ ≥ 11`). -/
theorem Ap_Q12 (h11 : 11 ≤ ℓ) : Ap hℓ (Bq ℓ 0) (Ql ℓ hℓ ^ 12) := by
  obtain ⟨ζ, hζ⟩ := exists_zeta ℓ
  obtain ⟨f, hf, hJ, hsum⟩ := modular_equation hℓ (iso_Pdisc hℓ) (by norm_num : 1 ≤ 12) hζ
  have hodd : Odd ℓ := Nat.odd_iff.mpr (odd_ell hℓ)
  have hinj : Function.Injective ((ιq ℓ).comp (ιz ℓ)) :=
    (ιq ℓ).injective.comp Subtype.val_injective
  -- the two coefficients of `g_ℓ`
  obtain ⟨hc0, hc1⟩ := esymm_ell_disc hℓ hζ
  rw [← hJ ℓ] at hc0 hc1
  have h0 : constantCoeff (ev ℤ_[ℓ] (f ℓ)) = 0 := by
    have := coeff_J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f ℓ))) 0
    rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hc0, coeff_map] at this
    apply hinj
    rw [map_zero, RingHom.comp_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact this.symm
  have h1 : coeff 1 (ev ℤ_[ℓ] (f ℓ)) = 1 := by
    have := coeff_J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f ℓ))) 1
    rw [mul_one, hc1, coeff_map] at this
    apply hinj
    rw [map_one, RingHom.comp_apply, ← this]
  obtain ⟨h, hh, hfh⟩ := disc_dvd hℓ (hf ℓ) h0
  have hh' : Iso h (12 * (ℓ - 1)) := iso_of_eq hh (by omega)
  have hevf : ev ℤ_[ℓ] (f ℓ) = Dl ℓ * ev ℤ_[ℓ] h := by rw [hfh, map_mul, ev_Pdisc]
  have hh0 : constantCoeff (ev ℤ_[ℓ] h) = 1 := by
    rw [hevf, Dl_eq, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow] at h1
    rw [← h1]
    have : constantCoeff (Pl ℓ) = 1 := by
      rw [Pl, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_qfacInf, map_one]
    rw [this, one_pow, one_mul]
  -- notation
  set F := Dl ℓ with hF
  set D := Einv ℓ hℓ with hD
  set W := Ql ℓ hℓ ^ 12 with hW
  set L : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) with hL
  have hVF : Vl ℓ F = W * F ^ ℓ * D ^ 12 := by
    have := congrArg (· * D ^ 12) (Q12_id hℓ)
    simp only at this
    rw [← hW, ← hF, mul_assoc (E ℓ hℓ ^ 12), mul_comm (Vl ℓ F), ← mul_assoc, ← mul_pow,
      E_mul_Einv, one_pow, one_mul] at this
    rw [← this]
  have hexp : expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] (Pdisc hℓ)) = Vl ℓ F := by rw [ev_Pdisc]; rfl
  rw [hexp, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, (hodd.add_one).neg_one_pow,
    one_mul] at hsum
  -- `g_{ℓ+1} = ℓ^{12} c' Δ^{ℓ+1}`
  have hVF' : Vl ℓ F = X ^ ℓ * Vl ℓ (Pl ℓ) ^ 24 := Vl_Dl
  have hterm : ∀ k ∈ Finset.range (ℓ + 1), ∃ R : PS ℓ,
      (-1) ^ k * ev ℤ_[ℓ] (f k) * (C (L ^ 12) * Vl ℓ F) ^ (ℓ + 1 - k) =
        C (L ^ 12) * X ^ (ℓ + 1) * R := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases Nat.lt_or_ge k ℓ with hkl | hkl
    · obtain ⟨j, hj⟩ : ∃ j, ℓ + 1 - k = j + 2 := ⟨ℓ - 1 - k, by omega⟩
      refine ⟨(-1) ^ k * ev ℤ_[ℓ] (f k) * C (L ^ 12) ^ (j + 1) * X ^ (ℓ * (j + 2) - (ℓ + 1)) *
        Vl ℓ (Pl ℓ) ^ (24 * (j + 2)), ?_⟩
      rw [hj, hVF', mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      have hx : (X : PS ℓ) ^ (ℓ * (j + 2)) = X ^ (ℓ + 1) * X ^ (ℓ * (j + 2) - (ℓ + 1)) := by
        rw [← pow_add]; congr 1
        have : ℓ + 1 ≤ ℓ * (j + 2) := by nlinarith
        omega
      rw [hx, pow_succ (C (L ^ 12) : PS ℓ) (j + 1)]
      ring
    · have hkℓ : k = ℓ := by omega
      rw [hkℓ]
      refine ⟨-(ev ℤ_[ℓ] h * Pl ℓ ^ 24 * Vl ℓ (Pl ℓ) ^ 24), ?_⟩
      rw [show ℓ + 1 - ℓ = 1 by omega, pow_one, hodd.neg_one_pow, hevf, hVF', hF, Dl_eq]
      ring
  choose! R hR using hterm
  have hfl : ev ℤ_[ℓ] (f (ℓ + 1)) =
      C (L ^ 12) * X ^ (ℓ + 1) * -(∑ k ∈ Finset.range (ℓ + 1), R k) := by
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_congr rfl hR]
    linear_combination hsum
  obtain ⟨Q', hQ', hQ'e⟩ := disc_pow_dvd hℓ (ℓ + 1) 0 (f (ℓ + 1))
    (iso_of_eq (hf (ℓ + 1)) (by ring))
    ⟨C (L ^ 12) * -(∑ k ∈ Finset.range (ℓ + 1), R k), by rw [hfl]; ring⟩
  rw [iso_zero_eq_C hQ'] at hQ'e
  set c := MvPolynomial.eval one2 Q' with hc
  have hevl : ev ℤ_[ℓ] (f (ℓ + 1)) = C c * F ^ (ℓ + 1) := by
    rw [hQ'e, map_mul, map_pow, ev_Pdisc, ev_C, mul_comm]
  -- `c = ℓ^{12} c'`
  have hFc : coeff (ℓ + 1) (F ^ (ℓ + 1)) = 1 := by
    rw [hF, Dl_eq, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_pow, map_pow]
    rw [Pl, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_qfacInf, map_one, one_pow, one_pow]
  set c' := constantCoeff (-(∑ k ∈ Finset.range (ℓ + 1), R k)) with hc'
  have hcc : c = L ^ 12 * c' := by
    have := congrArg (coeff (ℓ + 1)) (hevl.symm.trans hfl)
    rw [coeff_C_mul, hFc, mul_one, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at this
    rw [this]
  -- the divided equation
  set b : ℕ → PS ℓ := fun k => C ((-1) ^ k * L ^ (12 * (ℓ - k))) *
    (ev ℤ_[ℓ] (f k * Pdisc hℓ ^ (ℓ * (ℓ - k) - 1)) * D ^ (12 * (ℓ + 1 - k))) with hb
  have hid : ∑ k ∈ Finset.range ℓ, b k * W ^ (ℓ + 1 - k) - ev ℤ_[ℓ] h * D ^ 12 * W + C c' = 0 := by
    have hcz : C (L ^ 12) * F ^ (ℓ + 1) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
      · rw [Ne, ← map_zero C, (C_injective).eq_iff]; exact pow_ne_zero _ ell_ne_zero
      · intro h0'
        have := congrArg (coeff 1) h0'
        rw [hF, Dl_eq, coeff_succ_X_mul, map_zero, coeff_zero_eq_constantCoeff_apply, map_pow] at this
        rw [Pl, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
          constantCoeff_qfacInf, map_one, one_pow] at this
        exact one_ne_zero this
    refine (mul_eq_zero.mp ?_).resolve_left hcz
    rw [← hsum, Finset.sum_range_succ, hVF, hevl, hcc]
    rw [mul_add, mul_sub, Finset.mul_sum]
    have e3 : C (L ^ 12) * F ^ (ℓ + 1) * C c' = C (L ^ 12 * c') * F ^ (ℓ + 1) := by
      rw [map_mul]; ring
    have e2 : C (L ^ 12) * F ^ (ℓ + 1) * (ev ℤ_[ℓ] h * D ^ 12 * W) =
        -((-1) ^ ℓ * ev ℤ_[ℓ] (f ℓ) * (C (L ^ 12) * (W * F ^ ℓ * D ^ 12)) ^ (ℓ + 1 - ℓ)) := by
      rw [show ℓ + 1 - ℓ = 1 by omega, pow_one, hodd.neg_one_pow, hevf]; ring
    have hsumeq : ∑ k ∈ Finset.range ℓ, C (L ^ 12) * F ^ (ℓ + 1) * (b k * W ^ (ℓ + 1 - k)) =
        ∑ k ∈ Finset.range ℓ,
          (-1) ^ k * ev ℤ_[ℓ] (f k) * (C (L ^ 12) * (W * F ^ ℓ * D ^ 12)) ^ (ℓ + 1 - k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      obtain ⟨a1, a2, -⟩ := arith12 hk'
      have hbk : b k = C ((-1) ^ k * L ^ (12 * (ℓ - k))) *
          (ev ℤ_[ℓ] (f k) * F ^ (ℓ * (ℓ - k) - 1) * D ^ (12 * (ℓ + 1 - k))) := by
        rw [hb]; dsimp only
        rw [map_mul (ev ℤ_[ℓ]), map_pow, ev_Pdisc]
      rw [hbk, hL, term12 (ℓ + 1 - k) (ℓ * (ℓ - k) - 1) (12 * (ℓ - k)) a1 a2]
      simp
    rw [e3, e2, sub_neg_eq_add, hsumeq]
  -- reductions mod `ℓ`
  have hmapD : PowerSeries.map (PadicInt.toZMod (p := ℓ)) D = 1 := map_Einv ℓ hℓ
  have hmapW : PowerSeries.map (PadicInt.toZMod (p := ℓ)) W = 1 := by
    rw [hW, map_pow, map_Ql, one_pow]
  have hbd : ∀ k ∈ Finset.range ℓ, Dvd (ℓ : ℤ_[ℓ]) 1 (b k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨e, he⟩ : ∃ e, 12 * (ℓ - k) = e + 1 := ⟨12 * (ℓ - k) - 1, by omega⟩
    refine Dvd_of_eq (C ((-1) ^ k * L ^ e) *
      (ev ℤ_[ℓ] (f k * Pdisc hℓ ^ (ℓ * (ℓ - k) - 1)) * D ^ (12 * (ℓ + 1 - k)))) ?_
    rw [hb]; dsimp only
    rw [he, pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, map_mul, hL]; ring_nf
  have hmaph : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ev ℤ_[ℓ] h) = 1 := by
    have h0' := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) hid
    rw [map_add, map_sub, map_sum, Finset.sum_eq_zero (fun k hk => by
        rw [map_mul, map_zero_of_Dvd (hbd k hk), zero_mul]), map_mul, map_mul, map_pow,
      hmapD, hmapW, map_C, map_zero] at h0'
    have hmh : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ev ℤ_[ℓ] h) =
        C (PadicInt.toZMod c') := by
      linear_combination (-1 : PowerSeries (ZMod ℓ)) * h0'
    have := congrArg constantCoeff hmh
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hh0,
      map_one, constantCoeff_C] at this
    rw [hmh, ← this, map_one]
  have hhd : Dvd (ℓ : ℤ_[ℓ]) 1 (ev ℤ_[ℓ] h - 1) :=
    Dvd_of_map (by rw [map_sub, hmaph, map_one, sub_self])
  -- the contraction
  have hB0 : Bq ℓ 0 0 = 0 := by simp [Bq]
  have hAb : ∀ k ∈ Finset.range ℓ, Ap hℓ (Bq ℓ 0) (b k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨-, -, a3⟩ := arith12 hk'
    have hiso : Iso (f k * Pdisc hℓ ^ (ℓ * (ℓ - k) - 1)) (12 * (ℓ + 1 - k) * (ℓ - 1)) :=
      iso_of_eq ((hf k).mul ((iso_Pdisc hℓ).pow _)) (by rw [← a3, smul_eq_mul]; ring)
    have hbe : b k = ((-1) ^ k : ℤ_[ℓ]) • ((ℓ : ℤ_[ℓ]) ^ (12 * (ℓ - k)) •
        (ev ℤ_[ℓ] (f k * Pdisc hℓ ^ (ℓ * (ℓ - k) - 1)) * D ^ (12 * (ℓ + 1 - k)))) := by
      rw [hb]; dsimp only
      rw [smul_smul, smul_eq_C_mul]
    rw [hbe]
    refine Ap_smul _ (Ap_lowe hℓ ?_ hiso)
    exact (Bq0_le_of (c := 12) (by omega)).trans (by omega)
  have hAh : Ap hℓ (Bq ℓ 0) (1 - ev ℤ_[ℓ] h * D ^ 12) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ]]
    exact Ap_add (Ap_one hB0) (Ap_smul _ (Ap_const hℓ (by omega) hh' hhd))
  have h1d : Dvd (ℓ : ℤ_[ℓ]) 1 (1 - ev ℤ_[ℓ] h * D ^ 12) :=
    Dvd_of_map (by rw [map_sub, map_one, map_mul, map_pow, hmaph, hmapD, one_pow, mul_one,
      sub_self])
  refine hensel_fix hℓ hB0 (T := fun Y => (1 - ev ℤ_[ℓ] h * D ^ 12) * Y +
      ∑ k ∈ Finset.range ℓ, b k * Y ^ (ℓ + 1 - k) + C c') ?_ ?_ ?_
    (Dvd_of_map (by rw [map_sub, hmapW, map_one, sub_self]))
  · intro Y Y' n hY
    have e : (1 - ev ℤ_[ℓ] h * D ^ 12) * Y + ∑ k ∈ Finset.range ℓ, b k * Y ^ (ℓ + 1 - k) + C c' -
        ((1 - ev ℤ_[ℓ] h * D ^ 12) * Y' + ∑ k ∈ Finset.range ℓ, b k * Y' ^ (ℓ + 1 - k) + C c') =
        (1 - ev ℤ_[ℓ] h * D ^ 12) * (Y - Y') +
          ∑ k ∈ Finset.range ℓ, b k * (Y ^ (ℓ + 1 - k) - Y' ^ (ℓ + 1 - k)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    dsimp only
    rw [e, add_comm n 1]
    refine Dvd_add (Dvd_mul_mul h1d hY) (Dvd.sum _ _ fun k hk => Dvd_mul_mul (hbd k hk) ?_)
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow Y Y' (ℓ + 1 - k)
    rw [hq, ← add_zero n]
    exact Dvd_mul_mul hY ⟨q, by rw [pow_zero, one_smul]⟩
  · intro Y hY
    dsimp only
    refine Ap_add (Ap_add (Ap_mul B1_mul hAh hY) ?_) ?_
    · refine Finset.sum_induction _ (Ap hℓ (Bq ℓ 0)) (fun _ _ => Ap_add) ?_ fun k hk =>
        Ap_mul B1_mul (hAb k hk) (Ap_pow hℓ B1_mul B1_zero hY _)
      simpa using Ap_smul (0 : ℤ_[ℓ]) (Ap_one (hℓ := hℓ) (B := Bq ℓ 0) hB0)
    · rw [show (C c' : PS ℓ) = c' • (1 : PS ℓ) by rw [smul_eq_C_mul, mul_one]]
      exact Ap_smul _ (Ap_one hB0)
  · dsimp only
    linear_combination hid


/-! ### the 12th root -/

include hℓ in
lemma isUnit_twelve : IsUnit (12 : ℤ_[ℓ]) := by
  have h3 : IsUnit (3 : ℤ_[ℓ]) := by
    have h3' : ℓ ≠ 3 := by omega
    rw [PadicInt.isUnit_iff, show (3 : ℤ_[ℓ]) = ((3 : ℕ) : ℤ_[ℓ]) by norm_num,
      PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hℓp.out Nat.prime_three).mpr h3'
  have : (12 : ℤ_[ℓ]) = 2 * 2 * 3 := by norm_num
  rw [this]
  exact ((isUnit_two hℓ).mul (isUnit_two hℓ)).mul h3

/-- **`Q ∈ B_E(r)`** in approximation form (`ℓ ≥ 11`). -/
theorem Ap_Q (h11 : 11 ≤ ℓ) : Ap hℓ (Bq ℓ 0) (Ql ℓ hℓ) := by
  have hW := Ap_Q12 hℓ h11
  obtain ⟨u, hu⟩ := isUnit_twelve hℓ
  set i : ℤ_[ℓ] := ↑u⁻¹ with hi
  have hi12 : i * 12 = 1 := by rw [hi, ← hu, Units.inv_mul]
  have hB0 : Bq ℓ 0 0 = 0 := by simp [Bq]
  have hmapi : PadicInt.toZMod (p := ℓ) i * 12 = 1 := by
    have := congrArg (PadicInt.toZMod (p := ℓ)) hi12
    rwa [map_mul, map_ofNat, map_one] at this
  have hmapQ := map_Ql hℓ
  refine hensel_fixS hℓ hB0 (T := fun Y => Y - i • (Y ^ 12 - Ql ℓ hℓ ^ 12))
    (fun Y => Dvd (ℓ : ℤ_[ℓ]) 1 (Y - 1)) (by simpa using Dvd_zero (ℓ := ℓ) 1) ?_ ?_ ?_
    (Dvd_of_map (by rw [map_sub, hmapQ, map_one, sub_self])) ?_
    (Dvd_of_map (by rw [map_sub, hmapQ, map_one, sub_self]))
  · intro Y hY
    have hmY := map_one_of_Dvd hY
    refine Dvd_of_map ?_
    dsimp only
    rw [map_sub, map_sub, smul_eq_C_mul, map_mul, map_sub, map_pow, map_pow, hmY, hmapQ, map_C]
    simp
  · intro Y Y' n hY hY' h
    have hmY := map_one_of_Dvd hY
    have hmY' := map_one_of_Dvd hY'
    have e : Y - i • (Y ^ 12 - Ql ℓ hℓ ^ 12) - (Y' - i • (Y' ^ 12 - Ql ℓ hℓ ^ 12)) =
        (Y - Y') * (1 - C i * ∑ j ∈ Finset.range 12, Y ^ j * Y' ^ (12 - 1 - j)) := by
      have hg := Commute.geom_sum₂_mul (Commute.all Y Y') 12
      rw [smul_eq_C_mul, smul_eq_C_mul]
      linear_combination (C i : PS ℓ) * hg
    dsimp only
    rw [e, add_comm n 1, mul_comm]
    refine Dvd_mul_mul (Dvd_of_map ?_) h
    rw [map_sub, map_one, map_mul, map_sum, map_C]
    simp only [map_mul, map_pow, hmY, hmY', one_pow, mul_one, Finset.sum_const, Finset.card_range]
    rw [nsmul_eq_mul, show ((12 : ℕ) : PowerSeries (ZMod ℓ)) = C 12 from (map_natCast C 12).symm,
      mul_one, ← map_mul, hmapi, map_one, sub_self]
  · intro Y hY
    dsimp only
    rw [sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ] (i • _), smul_smul, sub_eq_add_neg,
      ← neg_one_smul ℤ_[ℓ] (Ql ℓ hℓ ^ 12)]
    exact Ap_add hY (Ap_smul _ (Ap_add (Ap_pow hℓ B1_mul B1_zero hY 12) (Ap_smul _ hW)))
  · dsimp only; rw [sub_self, smul_zero, sub_zero]

/-- **`Q ∈ B_E(r)`** (`ℓ ≥ 11`): Katz coordinates `v_i(Q) ≥ ⌈i/(ℓ+1)⌉`. -/
theorem Q_InB1 (h11 : 11 ≤ ℓ) : InB1 ℓ hℓ (Ql ℓ hℓ) := by
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap (Ap_Q hℓ h11)
  exact ⟨c, hc, fun i => by simpa [Bq] using hcb i⟩

end VLayer
