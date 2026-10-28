import RamanujanTau.VLayer.Final

/-!
# (DB) from (UB) and the sharp (I2) `HQ`, without `V(Q)`

With `h = V(P)/P^ℓ = η(ℓz)/η(z)^ℓ` (`h² = Q/E`) one has `W = V(h)·h^ℓ`, hence
`Φ = Δ^δ W = V(h)·(h^ℓΔ^δ)` and, by `U(V(a)·b) = a·U(b)`,

  `D f = U(Φ f) = h · U(h^ℓ Δ^δ f)`.

Write `h = Q^{1/2}·E^{-1/2}` and move `E^{-1/2} = U(V(E^{-1/2})·)` inside:

  `D f = Q^{1/2} · U( Q^{ℓ/2} · G^{1/2} · (Δ^δ/E^s) · f )`,   `G = E/V(E)`   (**`D_eq`**).

Only `Q`, `G`, `E`, `Δ` occur. Inside, `Q^{ℓ/2}G^{1/2} ∈ B_E(r)` (`Q_InB1`, `HG_holds`, square roots),
so (UB) bounds the `U`-image exactly as in `DB_of_UB`; the outer factor `Q^{1/2}` must lie in
`B_E(r^ℓ)` (sharp class `⌈ℓm/(ℓ+1)⌉`) not to spoil `d(i,j)`, which is what `HQ` provides.

* **`DB_of_UB_HQ : UB → HQ → DB`** (every prime `ℓ ≥ 5`).
* **`atkin_obrien_ℓ'''`**: the final theorems from `UB` and `HQ` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries AtkinOBrienFinal AtkinOBrien DBound

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### `U(V(a)·b) = a·U(b)` over any ring -/

lemma U_expand_mul {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0) (g f : PowerSeries R) :
    BoylanWebb.U p (expand p hp g * f) = g * BoylanWebb.U p f := by
  have hpos : 0 < p := Nat.pos_of_ne_zero hp
  ext n
  rw [BoylanWebb.coeff_U, coeff_mul, coeff_mul]
  rw [← Finset.sum_subset (s₁ := (Finset.antidiagonal n).map ⟨fun q => (p * q.1, p * q.2),
      fun q r h => by
        simp only [Prod.mk.injEq] at h
        ext
        · exact Nat.eq_of_mul_eq_mul_left hpos h.1
        · exact Nat.eq_of_mul_eq_mul_left hpos h.2⟩) ?_ ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_expand, BoylanWebb.coeff_U]
    rw [if_pos (dvd_mul_right p _), Nat.mul_div_cancel_left _ hpos]
  · intro q hq
    simp only [Finset.mem_map, Finset.mem_antidiagonal, Function.Embedding.coeFn_mk] at hq ⊢
    obtain ⟨r, hr, rfl⟩ := hq
    rw [← mul_add, hr]
  · intro q hq hq'
    simp only [Finset.mem_antidiagonal] at hq
    rw [coeff_expand]
    split_ifs with h
    · exfalso; apply hq'
      obtain ⟨c, hc⟩ := h
      have h2 : p ∣ q.2 := by
        have : q.2 = p * n - q.1 := by omega
        rw [this, hc, ← Nat.mul_sub]; exact dvd_mul_right _ _
      obtain ⟨d, hd⟩ := h2
      simp only [Finset.mem_map, Finset.mem_antidiagonal, Function.Embedding.coeFn_mk]
      refine ⟨(c, d), ?_, ?_⟩
      · apply Nat.eq_of_mul_eq_mul_left hpos
        rw [mul_add, ← hc, ← hd, hq]
      · ext <;> simp [hc, hd]
    · rw [zero_mul]

/-! ### square roots of power series -/

/-- coefficients of `√F` (`F(0) = 1`, `2` invertible with inverse `i2`). -/
noncomputable def sqc {R : Type*} [CommRing R] (F : PowerSeries R) (i2 : R) : ℕ → R
  | 0 => 1
  | n + 1 => i2 * (coeff (n + 1) F -
      ∑ q ∈ (Finset.antidiagonal (n + 1)).attach,
        if h : q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 then sqc F i2 q.1.1 * sqc F i2 q.1.2 else 0)
decreasing_by
  all_goals
    have hq := Finset.mem_antidiagonal.mp q.2
    omega

lemma exists_sqrt {R : Type*} [CommRing R] (F : PowerSeries R) (hF : constantCoeff F = 1)
    (i2 : R) (hi2 : i2 * 2 = 1) : ∃ y : PowerSeries R, y * y = F ∧ constantCoeff y = 1 := by
  classical
  refine ⟨mk (sqc F i2), ?_, by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, sqc]⟩
  ext n
  rw [coeff_mul]
  rcases n with _ | n
  · simp [sqc, hF]
  · rw [← Finset.sum_filter_add_sum_filter_not _ (fun q : ℕ × ℕ => q.1 ≠ 0 ∧ q.2 ≠ 0)]
    have hb : (Finset.antidiagonal (n + 1)).filter (fun q : ℕ × ℕ => ¬ (q.1 ≠ 0 ∧ q.2 ≠ 0)) =
        {(0, n + 1), (n + 1, 0)} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
        Finset.mem_singleton, not_and_or, not_not]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · left; ext <;> simp <;> omega
        · right; ext <;> simp <;> omega
      · rintro (rfl | rfl) <;> simp
    rw [hb, Finset.sum_pair (by simp)]
    simp only [coeff_mk]
    have hint : ∑ q ∈ (Finset.antidiagonal (n + 1)).filter
        (fun q : ℕ × ℕ => q.1 ≠ 0 ∧ q.2 ≠ 0), sqc F i2 q.1 * sqc F i2 q.2 =
        ∑ q ∈ (Finset.antidiagonal (n + 1)).attach,
          if h : q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 then sqc F i2 q.1.1 * sqc F i2 q.1.2 else 0 := by
      rw [Finset.sum_filter, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> rfl
    rw [hint]
    have h0 : sqc F i2 0 = 1 := by rw [sqc]
    rw [h0, sqc]
    linear_combination (coeff (n + 1) F -
      ∑ q ∈ (Finset.antidiagonal (n + 1)).attach,
        if h : q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 then sqc F i2 q.1.1 * sqc F i2 q.1.2 else 0) * hi2

/-! ### the factorization of `D` -/

lemma constantCoeff_E : constantCoeff (E ℓ hℓ) = 1 := by
  apply Subtype.ext
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [E, TateCurve.EhasseZp, TateCurve.coeff_Eis]

/-- `h = V(P)/P^ℓ`. -/
noncomputable def hh : PS ℓ := Vl ℓ (Pl ℓ) * Pinv ℓ ^ ℓ

lemma Wl_eq_hh : Wl ℓ = Vl ℓ (hh (ℓ := ℓ)) * hh ^ ℓ := by
  rw [Wl_eq, hh, map_mul, map_pow]
  have h1 : Vl ℓ (Pinv ℓ) * Vl ℓ (Pl ℓ) = 1 := by rw [← map_mul, mul_comm, Pl_mul_Pinv, map_one]
  calc Vl ℓ (Vl ℓ (Pl ℓ)) * Pinv ℓ ^ ℓ ^ 2
      = Vl ℓ (Vl ℓ (Pl ℓ)) * Pinv ℓ ^ ℓ ^ 2 * (Vl ℓ (Pinv ℓ) * Vl ℓ (Pl ℓ)) ^ ℓ := by
        rw [h1, one_pow, mul_one]
    _ = _ := by ring

lemma hh_sq : hh (ℓ := ℓ) * hh = Ql ℓ hℓ * Einv ℓ hℓ := by
  rw [hh, Ql]
  have := E_mul_Einv ℓ hℓ
  linear_combination (Vl ℓ (Pl ℓ) ^ 2 * Pinv ℓ ^ (2 * ℓ)) * this.symm +
    (0 : PS ℓ) * this

include hℓ in
lemma D_eq_hh (f : PS ℓ) :
    BoylanWebb.U ℓ (Φl ℓ * f) = hh * BoylanWebb.U ℓ (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f) := by
  rw [Phil_eq hℓ, Wl_eq_hh]
  rw [← U_expand_mul ℓ hℓp.out.ne_zero]
  congr 1
  change _ = Vl ℓ hh * _
  ring

include hℓ in
lemma map_eq_one_of_sq {x : PS ℓ} (h : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (x * x) = 1)
    (h0 : constantCoeff x = 1) : PowerSeries.map (PadicInt.toZMod (p := ℓ)) x = 1 := by
  have h2 : (PowerSeries.map (PadicInt.toZMod (p := ℓ)) x - 1) *
      (PowerSeries.map (PadicInt.toZMod (p := ℓ)) x + 1) = 0 := by
    rw [map_mul] at h; linear_combination h
  rcases mul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, map_one, map_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, h0, map_one] at this
    have h2' : (2 : ZMod ℓ) ≠ 0 := by
      intro h0'
      have h3 : ℓ ∣ 2 := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 2).mp (by exact_mod_cast h0')
      have := Nat.le_of_dvd two_pos h3
      omega
    exact h2' (by rw [← this]; norm_num)

lemma constantCoeff_hh : constantCoeff (hh (ℓ := ℓ)) = 1 := by
  have hP : constantCoeff (Pl ℓ) = 1 := by
    rw [Pl, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_qfacInf, map_one]
  have hPi : constantCoeff (Pinv ℓ) = 1 := by
    have := congrArg constantCoeff (Pl_mul_Pinv (ℓ := ℓ))
    rwa [map_mul, hP, one_mul, map_one] at this
  have hV : constantCoeff (Vl ℓ (Pl ℓ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Vl]
    change coeff 0 (PowerSeries.expand ℓ _ (Pl ℓ)) = 1
    rw [coeff_expand, if_pos (dvd_zero _), Nat.zero_div, coeff_zero_eq_constantCoeff_apply, hP]
  rw [hh, map_mul, map_pow, hV, hPi, one_pow, one_mul]

include hℓ in
lemma map_hh : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (hh (ℓ := ℓ)) = 1 :=
  map_eq_one_of_sq hℓ (by rw [hh_sq hℓ, map_mul, map_Ql, map_Einv, one_mul]) constantCoeff_hh

/-- **The factorization**: `D f = Q^{1/2} · U(Q^{ℓ/2} G^{1/2} (Δ^δ/E^s) f)`. -/
theorem D_eq : ∃ qh gh : PS ℓ, qh * qh = Ql ℓ hℓ ∧ gh * gh = Gl ℓ hℓ ∧
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) qh = 1 ∧
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) gh = 1 ∧
    ∀ f, BoylanWebb.U ℓ (Φl ℓ * f) =
      qh * BoylanWebb.U ℓ (qh ^ ℓ * gh * (Dl ℓ ^ BoylanWebb.δ ℓ * Einv ℓ hℓ ^ sN ℓ) * f) := by
  obtain ⟨u2, hu2⟩ := isUnit_two hℓ
  have hi2 : (↑u2⁻¹ : ℤ_[ℓ]) * 2 = 1 := by rw [← hu2, Units.inv_mul]
  obtain ⟨e, he, he0⟩ := exists_sqrt (E ℓ hℓ) (constantCoeff_E hℓ) _ hi2
  have heu : IsUnit (constantCoeff e) := by rw [he0]; exact isUnit_one
  set ei := e.invOfUnit heu.unit with hei
  have hee : e * ei = 1 := PowerSeries.mul_invOfUnit _ _ (by simp)
  have hEi : ei * ei = Einv ℓ hℓ := by
    have h1 : E ℓ hℓ * (ei * ei) = 1 := by rw [← he]; linear_combination (e * ei + 1) * hee
    calc ei * ei = Einv ℓ hℓ * (E ℓ hℓ * (ei * ei)) := by
          rw [← mul_assoc, mul_comm (Einv ℓ hℓ), E_mul_Einv, one_mul]
      _ = Einv ℓ hℓ := by rw [h1, mul_one]
  -- mod `ℓ`
  have hmE := map_E ℓ hℓ
  have hme : PowerSeries.map (PadicInt.toZMod (p := ℓ)) e = 1 :=
    map_eq_one_of_sq hℓ (by rw [he, hmE]) he0
  have hmei : PowerSeries.map (PadicInt.toZMod (p := ℓ)) ei = 1 := by
    have := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) hee
    rwa [map_mul, hme, one_mul, map_one] at this
  refine ⟨hh * e, e * Vl ℓ ei, ?_, ?_, ?_, ?_, fun f => ?_⟩
  · calc hh * e * (hh * e) = (hh * hh) * (e * e) := by ring
      _ = Ql ℓ hℓ := by rw [hh_sq hℓ, he, mul_assoc, mul_comm (Einv ℓ hℓ), E_mul_Einv, mul_one]
  · calc e * Vl ℓ ei * (e * Vl ℓ ei) = (e * e) * Vl ℓ (ei * ei) := by rw [map_mul]; ring
      _ = Gl ℓ hℓ := by rw [he, hEi, Gl]
  · rw [map_mul, hme, mul_one]; exact map_hh hℓ
  · rw [map_mul, hme, one_mul, Vl]
    change PowerSeries.map _ (PowerSeries.expand ℓ _ ei) = 1
    rw [PowerSeries.map_expand, hmei, map_one]
  · rw [D_eq_hh hℓ f]
    have hU : ∀ y, ei * BoylanWebb.U ℓ y = BoylanWebb.U ℓ (Vl ℓ ei * y) := fun y =>
      (U_expand_mul ℓ hℓp.out.ne_zero ei y).symm
    have hhq : hh * BoylanWebb.U ℓ (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f) =
        (hh * e) * (ei * BoylanWebb.U ℓ (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f)) := by
      linear_combination (-(hh * BoylanWebb.U ℓ (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f))) * hee
    rw [hhq, hU]
    congr 2
    have hs : (ei * ei) ^ sN ℓ = ei ^ (ℓ + 1) := by
      rw [← sq, ← pow_mul, two_sN hℓ]
    rw [← hEi, hs]
    calc Vl ℓ ei * (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f)
        = Vl ℓ ei * (hh ^ ℓ * Dl ℓ ^ BoylanWebb.δ ℓ * f) * (e * ei) ^ (ℓ + 1) := by
          rw [hee, one_pow, mul_one]
      _ = _ := by ring


/-! ### (DB) -/

variable (ℓ) in
/-- the sharp class `⌈ℓm/(ℓ+1)⌉` (`B_E(r^ℓ)` for all `v(r) < 1/(ℓ+1)`). -/
noncomputable def Bp (m : ℕ) : ℕ := (⌈(ℓ : ℚ) * m / ((ℓ : ℚ) + 1)⌉).toNat

lemma Bp_mul (k l m : ℕ) (h : m ≤ k + l) : Bp ℓ m ≤ Bp ℓ k + Bp ℓ l := by
  unfold Bp
  have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
  have h1 : ⌈(ℓ : ℚ) * m / ((ℓ : ℚ) + 1)⌉ ≤
      ⌈(ℓ : ℚ) * k / ((ℓ : ℚ) + 1)⌉ + ⌈(ℓ : ℚ) * l / ((ℓ : ℚ) + 1)⌉ := by
    refine le_trans (Int.ceil_mono ?_) (Int.ceil_add_le _ _)
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have : (m : ℚ) ≤ k + l := by exact_mod_cast h
    nlinarith [(Nat.cast_nonneg ℓ : (0 : ℚ) ≤ ℓ)]
  have := Int.self_le_toNat ⌈(ℓ : ℚ) * k / ((ℓ : ℚ) + 1)⌉
  have := Int.self_le_toNat ⌈(ℓ : ℚ) * l / ((ℓ : ℚ) + 1)⌉
  omega

lemma Bp_zero : Bp ℓ 0 = 0 := by simp [Bp]

lemma Bq0_le_Bp (m : ℕ) : Bq ℓ 0 m ≤ Bp ℓ m := by
  unfold Bq Bp
  refine Int.toNat_le_toNat (Int.ceil_mono (div_le_div_of_nonneg_right ?_ (by positivity)))
  have : (1 : ℚ) ≤ ℓ := by exact_mod_cast (by have := hℓp.out.two_le; omega : 1 ≤ ℓ)
  have : (0 : ℚ) ≤ m := by positivity
  rw [sub_zero]; nlinarith

/-- **(DB) from (UB) and the sharp (I2) `HQ`** (every prime `ℓ ≥ 5`); no `V(Q)` needed. -/
theorem DB_of_UB_HQ (hUB : UB ℓ hℓ) (hQ : HQ ℓ hℓ) : DB ℓ hℓ := by
  obtain ⟨qh, gh, hq2, hg2, hmq, hmg, hD⟩ := D_eq hℓ
  have hQap : Ap hℓ (Bp ℓ) (Ql ℓ hℓ) := by
    obtain ⟨c, hc, hcb⟩ := hQ
    exact Ap_of_isKatz hc fun i => hcb i
  have hqh : Ap hℓ (Bp ℓ) qh := sqrt_Ap Bp_mul Bp_zero
    (Dvd_of_map (by rw [map_sub, hmq, map_one, sub_self])) (by rw [hq2]; exact hQap)
  have hgh : Ap hℓ (Bq ℓ 0) gh := sqrt_Ap B1_mul B1_zero
    (Dvd_of_map (by rw [map_sub, hmg, map_one, sub_self]))
    (by rw [hg2]; exact Ap_of_InB1 hℓ (HG_holds hℓ))
  have hqh1 : Ap hℓ (Bq ℓ 0) qh := Ap_mono (fun m => Bq0_le_Bp m) hqh
  have hW' : Ap hℓ (Bq ℓ 0) (qh ^ ℓ * gh) :=
    Ap_mul B1_mul (Ap_pow hℓ B1_mul B1_zero hqh1 ℓ) hgh
  intro j x hx
  have hs : ((sN ℓ : ℕ) : ℚ) = AtkinOBrien.s ℓ := by
    have := two_sN hℓ
    rw [AtkinOBrien.s]
    have h' : (2 : ℚ) * (sN ℓ : ℚ) = (ℓ : ℚ) + 1 := by exact_mod_cast this
    linarith
  set inner := qh ^ ℓ * gh * (Dl ℓ ^ BoylanWebb.δ ℓ * Einv ℓ hℓ ^ sN ℓ) *
    (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) with hinner
  have hin : Ap hℓ (Bq ℓ (sN ℓ + 0 + j)) inner := by
    have := Ap_mul (Bq_mul _ _) (Ap_mul (Bq_mul _ _) (Ap_Delta hℓ) hW') (Ap_x hℓ j hx)
    exact Ap_congr (by rw [hinner]; ring) this
  set γ : ℕ → ℤ := fun k => ⌈((k : ℚ) - j - AtkinOBrien.s ℓ) / ((ℓ : ℚ) + 1)⌉ with hγ
  have hEnv : Env ℓ hℓ 0 γ inner := by
    rw [env_iff_Ap]
    refine Ap_mono (fun k => le_of_eq ?_) hin
    rw [toNat_max, sub_zero, hγ, Bq, hs]
    congr 3
    ring_nf
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
  -- multiply by `Q^{1/2} ∈ B_E(r^ℓ)`
  have hprod : Ap hℓ (fun i => (d ℓ i j).toNat) (qh * Ulin ℓ inner) := by
    refine Ap_mul (fun k l m hm => ?_) hqh hT
    simp only [add_sub_cancel_right]
    have hpos : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
    have h1 : ⌈((ℓ : ℚ) * m - j - AtkinOBrien.s ℓ) / ((ℓ : ℚ) + 1)⌉ ≤
        ⌈(ℓ : ℚ) * k / ((ℓ : ℚ) + 1)⌉ + ⌈((ℓ : ℚ) * l - j - AtkinOBrien.s ℓ) / ((ℓ : ℚ) + 1)⌉ := by
      refine le_trans (Int.ceil_mono ?_) (Int.ceil_add_le _ _)
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hpos.le
      have : (m : ℚ) ≤ k + l := by exact_mod_cast hm
      nlinarith [(Nat.cast_nonneg ℓ : (0 : ℚ) ≤ ℓ)]
    have := Int.self_le_toNat ⌈(ℓ : ℚ) * k / ((ℓ : ℚ) + 1)⌉
    have := Int.self_le_toNat (d ℓ l j)
    simp only [Bp, d, toNat_max] at h1 this ⊢
    omega
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap hprod
  refine ⟨c, ?_, hcb⟩
  have e : BoylanWebb.U ℓ (Φl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) = qh * Ulin ℓ inner := by
    rw [hD, hinner]; rfl
  rw [e]; exact hc

theorem atkin_obrien_13''' (hUB : UB 13 (by norm_num)) (hQ : HQ 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13 hUB (DB_of_UB_HQ _ hUB hQ)

theorem atkin_obrien_17''' (hUB : UB 17 (by norm_num)) (hQ : HQ 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17 hUB (DB_of_UB_HQ _ hUB hQ)

theorem atkin_obrien_19''' (hUB : UB 19 (by norm_num)) (hQ : HQ 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19 hUB (DB_of_UB_HQ _ hUB hQ)

theorem atkin_obrien_23''' (hUB : UB 23 (by norm_num)) (hQ : HQ 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23 hUB (DB_of_UB_HQ _ hUB hQ)

end VLayer
