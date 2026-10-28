import RamanujanTau.SharpHQ.Radius

/-!
# The sharp (I2): `Q ∈ B_E(r^ℓ)` from pointwise bounds on the `Δ`-modular equation

This reruns the Hensel argument of `VLayer.Ap_Q12` / `VLayer.Ap_Q` in the sharp class `Bp ℓ`
(`v_m ≥ ⌈ℓm/(ℓ+1)⌉`). The level-`ℓ` modular equation of `Δ` (`VLayer.modular_equation`, `P = Δ`,
`w = 12`) has classical coefficients `f_k` of weight `12k`. Divided by `ℓ^{12}Δ^{ℓ+1}` it reads

  `c − (h/E^{12}) Q^{12} + Σ_{k<ℓ} b_k Q^{12(ℓ+1−k)} = 0`,
  `b_k = ±ℓ^{12(ℓ−k)} f_k Δ^{ℓ(ℓ−k)−1}/E^{12(ℓ+1−k)}`,   `f_ℓ = Δ·h`.

The coefficients are finite Katz series. By `Ap_Bp_of_pointwise` they lie in the sharp class as soon as
they are bounded by `1` pointwise on the break region. That is the hypothesis

* **`CoeffBound φ f`**: for every test curve `W` with `v(E(W)) < ℓ/(ℓ+1)` and every `k ≤ ℓ`,
  `‖ℓ‖^{12(ℓ−k)}·‖f_k(W)‖ ≤ ‖E(W)‖^{12(ℓ+1−k)}`.

Results:
* `Ap_Q12_sharp`: `Q^{12} ∈ Bp`;
* `Ap_Q_sharp`: `Q ∈ Bp`, via a Hensel 12th root;
* **`HQ_of_coeffBound`**: `HQ ℓ hℓ`.

All three need `ℓ ≥ 11`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SharpHQ
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound VLayer KatzForms Igusa

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- `‖Δ(W)‖ = 1` on test curves. -/
lemma norm_Pdisc (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) {W : WeierstrassCurve K} (hW : IsTest W) :
    ‖MvPolynomial.eval (pt W) (MvPolynomial.map φ (Pdisc hℓ))‖ = 1 := by
  have hg := (good_pt φ hφ hℓ hW).2
  have hu : ‖φ (↑(isUnit_1728_Zp (p := ℓ) hℓ).unit⁻¹ : ℤ_[ℓ])‖ = 1 :=
    norm_phi_unit φ hφ (Units.isUnit _)
  simp only [Pdisc, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.eval_X, norm_mul, hu, one_mul]
  exact hg

variable (ℓ) in
/-- **The pointwise coefficient bound** for the `Δ`-modular equation: on the break region
`v(E(W)) < ℓ/(ℓ+1)`, `v(f_k(W)) ≥ 12(ℓ+1−k)·v(E(W)) − 12(ℓ−k)` for `k ≤ ℓ`. -/
def CoeffBound (φ : ℤ_[ℓ] →+* K) (f : ℕ → Poly ℓ) : Prop :=
  ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W → ∀ k, k ≤ ℓ →
    ‖(ℓ : K)‖ ^ (12 * (ℓ - k)) * ‖MvPolynomial.eval (pt W) (MvPolynomial.map φ (f k))‖ ≤
      ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ (12 * (ℓ + 1 - k))

/-- **`Q^{12}` in the sharp class**, from the pointwise coefficient bound. -/
theorem Ap_Q12_sharp (h11 : 11 ≤ ℓ) [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (hsum : ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k * ev ℤ_[ℓ] (f k) *
      (C ((ℓ : ℤ_[ℓ]) ^ 12) * expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] (Pdisc hℓ))) ^ (ℓ + 1 - k) = 0)
    (hB : CoeffBound ℓ hℓ φ f) : Ap hℓ (Bp ℓ) (Ql ℓ hℓ ^ 12) := by
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
  have hB0 : Bp ℓ 0 = 0 := Bp_zero
  -- the pointwise inputs
  have hptb : ∀ k, k < ℓ → ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
      ‖(ℓ : K)‖ ^ (12 * (ℓ - k)) *
        ‖MvPolynomial.eval (pt W) (MvPolynomial.map φ (f k * Pdisc hℓ ^ (ℓ * (ℓ - k) - 1)))‖ ≤
        ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ (12 * (ℓ + 1 - k)) := by
    intro k hk W hW hBr
    rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, norm_Pdisc hℓ φ hφ hW, one_pow,
      mul_one]
    exact hB W hW hBr k hk.le
  have hpth : ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
      ‖(ℓ : K)‖ ^ 0 * ‖MvPolynomial.eval (pt W) (MvPolynomial.map φ h)‖ ≤
        ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12 := by
    intro W hW hBr
    have := hB W hW hBr ℓ le_rfl
    rwa [hfh, map_mul, map_mul, norm_mul, norm_Pdisc hℓ φ hφ hW, one_mul, Nat.sub_self, mul_zero,
      show ℓ + 1 - ℓ = 1 by omega, mul_one] at this
  have hAb : ∀ k ∈ Finset.range ℓ, Ap hℓ (Bp ℓ) (b k) := by
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
    exact Ap_smul _ (Ap_Bp_of_pointwise hℓ φ hφ hε hpK hiso (hptb k hk'))
  have hAh : Ap hℓ (Bp ℓ) (1 - ev ℤ_[ℓ] h * D ^ 12) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ]]
    have := Ap_Bp_of_pointwise hℓ φ hφ hε hpK (e := 0) hh' hpth
    rw [pow_zero, one_smul] at this
    exact Ap_add (Ap_one hB0) (Ap_smul _ this)
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
    refine Ap_add (Ap_add (Ap_mul Bp_mul hAh hY) ?_) ?_
    · refine Finset.sum_induction _ (Ap hℓ (Bp ℓ)) (fun _ _ => Ap_add) ?_ fun k hk =>
        Ap_mul Bp_mul (hAb k hk) (Ap_pow hℓ Bp_mul Bp_zero hY _)
      simpa using Ap_smul (0 : ℤ_[ℓ]) (Ap_one (hℓ := hℓ) (B := Bp ℓ) hB0)
    · rw [show (C c' : PS ℓ) = c' • (1 : PS ℓ) by rw [smul_eq_C_mul, mul_one]]
      exact Ap_smul _ (Ap_one hB0)
  · dsimp only
    linear_combination hid


/-- **`Q` in the sharp class** (`ℓ ≥ 11`), from the pointwise coefficient bound. -/
theorem Ap_Q_sharp (h11 : 11 ≤ ℓ) [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (hsum : ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k * ev ℤ_[ℓ] (f k) *
      (C ((ℓ : ℤ_[ℓ]) ^ 12) * expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] (Pdisc hℓ))) ^ (ℓ + 1 - k) = 0)
    (hB : CoeffBound ℓ hℓ φ f) : Ap hℓ (Bp ℓ) (Ql ℓ hℓ) := by
  have hW := Ap_Q12_sharp hℓ h11 φ hφ hε hpK hζ f hf hJ hsum hB
  obtain ⟨u, hu⟩ := isUnit_twelve hℓ
  set i : ℤ_[ℓ] := ↑u⁻¹ with hi
  have hi12 : i * 12 = 1 := by rw [hi, ← hu, Units.inv_mul]
  have hB0 : Bp ℓ 0 = 0 := Bp_zero
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
    exact Ap_add hY (Ap_smul _ (Ap_add (Ap_pow hℓ Bp_mul Bp_zero hY 12) (Ap_smul _ hW)))
  · dsimp only; rw [sub_self, smul_zero, sub_zero]

/-- **The sharp (I2)**, `HQ`, from the pointwise coefficient bound on the `Δ`-modular equation
(`ℓ ≥ 11`). -/
theorem HQ_of_coeffBound (h11 : 11 ≤ ℓ) [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    {ζ : PadicAlgCl ℓ} (hζ : IsPrimitiveRoot ζ ℓ) (f : ℕ → Poly ℓ) (hf : ∀ k, Iso (f k) (k * 12))
    (hJ : ∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k))
    (hsum : ∑ k ∈ Finset.range (ℓ + 2), (-1) ^ k * ev ℤ_[ℓ] (f k) *
      (C ((ℓ : ℤ_[ℓ]) ^ 12) * expand ℓ (ell_ne_zero' ℓ) (ev ℤ_[ℓ] (Pdisc hℓ))) ^ (ℓ + 1 - k) = 0)
    (hB : CoeffBound ℓ hℓ φ f) : HQ ℓ hℓ := by
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap (Ap_Q_sharp hℓ h11 φ hφ hε hpK hζ f hf hJ hsum hB)
  exact ⟨c, hc, hcb⟩

end SharpHQ
