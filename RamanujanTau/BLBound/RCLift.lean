import RamanujanTau.BLBound.ThetaFiltration

/-!
# The Rankin–Cohen lift of `θ`

Let `E = E_{ℓ-1} = 1 + ℓe`. For a series `g` and `k` prime to `ℓ`, the bracket `F = k g θE - (ℓ-1) E θg` reduces to `θg`,
its `U` image is divisible by `ℓ`, and

`(UF)/ℓ ≡ (1/k) θ(Ug) + ((k-1)/k) (∂(Ug) - U(∂g))`, where `∂ = θ - (k/12) E₂`.

When `g` has weight `k` the bracket has weight `k + ℓ + 1`, and the last term has weight `k + 2`. So on `θ` of weight `k`,
modulo weight `k + 2`, the operator `U/ℓ` is `(1/k) U`. The inputs are `θe ≡ (E₂ - VE₂)/12`, `U(a Vb) = b Ua` and `Uθ ≡ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries Igusa BoylanWebb

noncomputable section

section Ring
variable {R : Type*} [CommRing R]

lemma U_mul_expand (ℓ : ℕ) (hℓ : ℓ ≠ 0) (a b : PowerSeries R) :
    U ℓ (a * PowerSeries.expand ℓ hℓ b) = b * U ℓ a := by
  ext n
  rw [coeff_U, coeff_mul, mul_comm b, coeff_mul]
  simp only [coeff_U]
  symm
  refine Finset.sum_of_injOn (fun x : ℕ × ℕ => (ℓ * x.1, ℓ * x.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x₁, x₂⟩ - ⟨y₁, y₂⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h.1)
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h.2)
  · rintro ⟨x₁, x₂⟩ hx
    have hx' : x₁ + x₂ = n := Finset.mem_antidiagonal.mp hx
    exact Finset.mem_antidiagonal.mpr (by rw [← mul_add, hx'])
  · rintro ⟨i, j⟩ hij hne
    have hs : i + j = ℓ * n := Finset.mem_antidiagonal.mp hij
    simp only
    rw [PowerSeries.coeff_expand]
    split_ifs with hd
    · exfalso
      apply hne
      obtain ⟨t, rfl⟩ := hd
      have hi : ℓ ∣ i := (Nat.dvd_add_left (dvd_mul_right ℓ t)).mp (hs ▸ dvd_mul_right ℓ n)
      obtain ⟨s, rfl⟩ := hi
      refine ⟨(s, t), Finset.mem_coe.mpr (Finset.mem_antidiagonal.mpr ?_), rfl⟩
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) (by rw [mul_add, hs])
    · simp
  · rintro ⟨s, t⟩ -
    simp only
    rw [PowerSeries.coeff_expand, if_pos (dvd_mul_right ℓ t), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]

lemma U_theta (ℓ : ℕ) (f : PowerSeries R) : U ℓ (theta f) = (ℓ : PowerSeries R) * theta (U ℓ f) := by
  ext n
  rw [coeff_U, coeff_theta, ← map_natCast (C (R := R)), coeff_C_mul, coeff_theta, coeff_U]
  push_cast
  ring

lemma U_natCast_mul (ℓ m : ℕ) (f : PowerSeries R) : U ℓ ((m : PowerSeries R) * f) = (m : PowerSeries R) * U ℓ f := by
  rw [← map_natCast (C (R := R)), U_C_mul]

lemma U_sub (ℓ : ℕ) (f g : PowerSeries R) : U ℓ (f - g) = U ℓ f - U ℓ g := by
  ext n
  simp [coeff_U]

end Ring

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `∂ = θ - (k/12) E₂` on `𝔽_ℓ⟦q⟧`. -/
def serreBar (k : ℕ) (f : PowerSeries (ZMod ℓ)) : PowerSeries (ZMod ℓ) :=
  theta f - C ((k : ZMod ℓ) * 12⁻¹) * (E2 (ZMod ℓ) * f)

lemma natCast_self_series : ((ℓ : ℕ) : PowerSeries (ZMod ℓ)) = 0 := by
  rw [← map_natCast (C (R := ZMod ℓ)), CharP.cast_eq_zero, map_zero]

/-- The algebra of the lift, given the value of `θe`. -/
lemma rc_core (k : ℕ) (hk : (k : ZMod ℓ) ≠ 0) (a e : PowerSeries (ZMod ℓ))
    (he : theta e = C (12⁻¹ : ZMod ℓ) * (E2 (ZMod ℓ) - PowerSeries.expand ℓ hℓ.out.ne_zero (E2 (ZMod ℓ)))) :
    theta (U ℓ a) + U ℓ (C (k : ZMod ℓ) * (a * theta e) + e * theta a - theta a) =
      C (k : ZMod ℓ)⁻¹ * theta (U ℓ a) + C (((k : ZMod ℓ) - 1) * (k : ZMod ℓ)⁻¹) *
        (serreBar k (U ℓ a) - U ℓ (serreBar k a)) := by
  have hUθ : ∀ f : PowerSeries (ZMod ℓ), U ℓ (theta f) = 0 := fun f => by
    rw [U_theta, natCast_self_series, zero_mul]
  have hx : e * theta a = theta (e * a) - a * theta e := by
    rw [theta_mul]
    ring
  have hV := U_mul_expand ℓ hℓ.out.ne_zero a (E2 (ZMod ℓ))
  have hae : a * theta e = C (12⁻¹ : ZMod ℓ) * (a * E2 (ZMod ℓ) -
      a * PowerSeries.expand ℓ hℓ.out.ne_zero (E2 (ZMod ℓ))) := by
    rw [he]
    ring
  set A := U ℓ a with hA
  set W := U ℓ (a * E2 (ZMod ℓ)) with hW
  have hE : E2 (ZMod ℓ) * a = a * E2 (ZMod ℓ) := mul_comm _ _
  have h1 : U ℓ (a * theta e) = C (12⁻¹ : ZMod ℓ) * (W - E2 (ZMod ℓ) * A) := by
    rw [hae, U_C_mul, U_sub, hV]
  have h2 : U ℓ (C (k : ZMod ℓ) * (a * theta e) + e * theta a - theta a) =
      (C (k : ZMod ℓ) - 1) * (C (12⁻¹ : ZMod ℓ) * (W - E2 (ZMod ℓ) * A)) := by
    rw [hx, U_sub, U_add, U_C_mul, U_sub, hUθ, hUθ, h1]
    ring
  have h3 : U ℓ (serreBar k a) = -(C ((k : ZMod ℓ) * 12⁻¹) * W) := by
    rw [serreBar, U_sub, hUθ, U_C_mul, hE]
    ring
  have hxy : C (k : ZMod ℓ) * C (k : ZMod ℓ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  rw [h2, h3, serreBar]
  simp only [map_mul, map_sub, map_one]
  linear_combination (-(theta A + (C (k : ZMod ℓ) - 1) * C (12⁻¹ : ZMod ℓ) * (W - E2 (ZMod ℓ) * A))) * hxy

/-! ### The value of `θe` -/

open scoped ArithmeticFunction.sigma in
/-- `n σ_{ℓ-2}(n) ≡ σ₁(n) - σ₁(n/ℓ)`, the last term only when `ℓ ∣ n`. -/
lemma sigma_mul_mod (hℓ3 : 3 ≤ ℓ) (n : ℕ) (hn : n ≠ 0) :
    (n : ZMod ℓ) * (σ (ℓ - 2) n : ℕ) = (σ 1 n : ℕ) - (if ℓ ∣ n then ((σ 1 (n / ℓ) : ℕ) : ZMod ℓ) else 0) := by
  have hp := hℓ.out
  have hterm : ∀ d ∈ n.divisors, (n : ZMod ℓ) * (d : ZMod ℓ) ^ (ℓ - 2) =
      ((n / d : ℕ) : ZMod ℓ) * (if ℓ ∣ d then 0 else 1) := by
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hn' : n = (n / d) * d := (Nat.div_mul_cancel hdn).symm
    split_ifs with hl
    · have : (d : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hl
      conv_lhs => rw [hn']
      push_cast
      rw [this]
      simp
    · have hne : (d : ZMod ℓ) ≠ 0 := fun h => hl ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have hf := ZMod.pow_card_sub_one_eq_one hne
      conv_lhs => rw [hn']
      push_cast
      rw [mul_assoc, ← pow_succ', show ℓ - 2 + 1 = ℓ - 1 by omega, hf]
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
  have hsum : ∑ d ∈ n.divisors, (d : ZMod ℓ) ^ 1 = ∑ d ∈ n.divisors, ((n / d : ℕ) : ZMod ℓ) := by
    have := Nat.sum_div_divisors n (fun d => (d : ZMod ℓ))
    simp only [pow_one]
    exact this.symm
  rw [hsum]
  have hsplit : ∑ d ∈ n.divisors, ((n / d : ℕ) : ZMod ℓ) * (if ℓ ∣ d then 0 else 1) =
      ∑ d ∈ n.divisors, ((n / d : ℕ) : ZMod ℓ) - ∑ d ∈ n.divisors.filter (ℓ ∣ ·), ((n / d : ℕ) : ZMod ℓ) := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [hsplit]
  congr 1
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    rw [Nat.mul_div_cancel_left _ hp.pos, ArithmeticFunction.sigma_apply]
    push_cast
    have := Nat.sum_div_divisors m (fun d => (d : ZMod ℓ))
    simp only [pow_one]
    rw [← this]
    symm
    refine Finset.sum_of_injOn (fun d => ℓ * d) ?_ ?_ ?_ ?_
    · intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro d hd
      have hdm := Nat.dvd_of_mem_divisors (Finset.mem_coe.mp hd)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left ℓ hdm, Nat.mul_ne_zero hp.ne_zero hm⟩, dvd_mul_right _ _⟩)
    · intro d hd hne
      obtain ⟨hd1, t, rfl⟩ := Finset.mem_filter.mp hd
      exfalso
      apply hne
      have hdvd := Nat.dvd_of_mem_divisors hd1
      exact ⟨t, Finset.mem_coe.mpr (Nat.mem_divisors.mpr
        ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd, hm⟩), rfl⟩
    · intro d _
      simp only
      rw [Nat.mul_div_mul_left _ _ hp.pos]
  · refine Finset.sum_eq_zero fun d hd' => ?_
    obtain ⟨hd1, hl⟩ := Finset.mem_filter.mp hd'
    exact absurd (hl.trans (Nat.dvd_of_mem_divisors hd1)) hd

lemma coeff_E2_bar (n : ℕ) :
    coeff n (E2 (ZMod ℓ)) = (if n = 0 then 1 else 0) - 24 * ((ArithmeticFunction.sigma 1 n : ℕ) : ZMod ℓ) := by
  rw [E2, coeff_map, e2Z, map_sub, coeff_one, show (24 : PowerSeries ℤ) = C 24 from (map_ofNat C 24).symm,
    coeff_C_mul, coeff_mk]
  simp only [eq_intCast]
  push_cast
  rfl

/-- The unit `ℓ B_{ℓ-1} ≡ -1` as a `ℓ`-adic integer, with the coefficient of `E_{ℓ-1}` read through it. -/
lemma exists_coeff_hasse (hℓ3 : 3 ≤ ℓ) : ∃ u : ℤ_[ℓ], PadicInt.toZMod u = -1 ∧ ∀ n : ℕ, n ≠ 0 →
    u * coeff n (TateCurve.EhasseZp ℓ hℓ3) = ((ℓ : ℤ_[ℓ])) * (-(2 * ((ℓ - 1 : ℕ) : ℤ_[ℓ]) *
      ((ArithmeticFunction.sigma (ℓ - 2) n : ℕ) : ℤ_[ℓ]))) := by
  have hp := hℓ.out
  have hB0 : bernoulli (ℓ - 1) ≠ 0 := TateCurve.bernoulli_sub_one_ne_zero hℓ3
  have hadd := TateCurve.padicNorm_p_mul_bernoulli_add_one (p := ℓ) hℓ3
  have hle1 : ‖(((ℓ : ℚ) * bernoulli (ℓ - 1) : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [Padic.eq_padicNorm]
    exact_mod_cast (TateCurve.padicNorm_p_mul_bernoulli_eq_one (p := ℓ) hℓ3).le
  let u : ℤ_[ℓ] := ⟨(((ℓ : ℚ) * bernoulli (ℓ - 1) : ℚ) : ℚ_[ℓ]), hle1⟩
  refine ⟨u, ?_, ?_⟩
  · have hlt : ‖u + 1‖ < 1 := by
      change ‖((((ℓ : ℚ) * bernoulli (ℓ - 1) : ℚ) : ℚ_[ℓ]) + 1)‖ < 1
      have : ((((ℓ : ℚ) * bernoulli (ℓ - 1) : ℚ) : ℚ_[ℓ]) + 1) = (((ℓ : ℚ) * bernoulli (ℓ - 1) + 1 : ℚ) : ℚ_[ℓ]) := by
        push_cast
        rfl
      rw [this, Padic.eq_padicNorm]
      have hq : ((padicNorm ℓ ((ℓ : ℚ) * bernoulli (ℓ - 1) + 1) : ℚ) : ℝ) ≤ ((ℓ : ℚ)⁻¹ : ℚ) := by exact_mod_cast hadd
      refine lt_of_le_of_lt hq ?_
      have hl : (1 : ℝ) < ℓ := by exact_mod_cast hp.one_lt
      push_cast
      exact inv_lt_one_of_one_lt₀ hl
    have hz : PadicInt.toZMod (u + 1) = 0 := by
      have : u + 1 ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] :=
        (IsLocalRing.mem_maximalIdeal _).mpr (PadicInt.mem_nonunits.mpr hlt)
      rwa [← PadicInt.ker_toZMod, RingHom.mem_ker] at this
    rw [map_add, map_one] at hz
    exact eq_neg_of_add_eq_zero_left hz
  · intro n hn
    apply PadicInt.ext
    have hc : ((coeff n (TateCurve.EhasseZp ℓ hℓ3) : ℤ_[ℓ]) : ℚ_[ℓ]) = ((coeff n (TateCurve.Ehasse ℓ) : ℚ) : ℚ_[ℓ]) := by
      simp [TateCurve.EhasseZp, coeff_mk]
    have hq : ((ℓ : ℚ) * bernoulli (ℓ - 1)) * coeff n (TateCurve.Ehasse ℓ) =
        (ℓ : ℚ) * (-(2 * ((ℓ - 1 : ℕ) : ℚ) * ((ArithmeticFunction.sigma (ℓ - 2) n : ℕ) : ℚ))) := by
      rw [TateCurve.Ehasse, TateCurve.coeff_Eis, if_neg hn, TateCurve.kappa, show ℓ - 1 - 1 = ℓ - 2 by omega]
      field_simp
      ring
    have hu' : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (((ℓ : ℚ) * bernoulli (ℓ - 1) : ℚ) : ℚ_[ℓ]) := rfl
    rw [PadicInt.coe_mul, hc, hu', ← Rat.cast_mul, hq]
    push_cast
    rfl

/-- **`θe ≡ (E₂ - VE₂)/12`.** -/
theorem theta_e (hℓ5 : 5 ≤ ℓ) (e : PowerSeries ℤ_[ℓ])
    (he : TateCurve.EhasseZp ℓ (by omega) = 1 + (ℓ : PowerSeries ℤ_[ℓ]) * e) :
    theta (PowerSeries.map (PadicInt.toZMod (p := ℓ)) e) =
      C (12⁻¹ : ZMod ℓ) * (E2 (ZMod ℓ) - PowerSeries.expand ℓ hℓ.out.ne_zero (E2 (ZMod ℓ))) := by
  have hp := hℓ.out
  have h3 : 3 ≤ ℓ := by omega
  have h12 : (12 : ZMod ℓ) ≠ 0 := by
    intro h
    have : (((12 : ℕ) : ZMod ℓ)) = 0 := by exact_mod_cast h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp this
    have h2 : ℓ ∣ 2 ^ 2 * 3 := by simpa using hd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  obtain ⟨u, hu, hcoef⟩ := exists_coeff_hasse (ℓ := ℓ) h3
  have hen : ∀ n : ℕ, n ≠ 0 → PadicInt.toZMod (coeff n e) =
      -2 * ((ArithmeticFunction.sigma (ℓ - 2) n : ℕ) : ZMod ℓ) := by
    intro n hn
    have hE : coeff n (TateCurve.EhasseZp ℓ h3) = (ℓ : ℤ_[ℓ]) * coeff n e := by
      rw [he, map_add, coeff_one, if_neg hn, zero_add, ← map_natCast (C (R := ℤ_[ℓ])), coeff_C_mul]
    have h := hcoef n hn
    rw [hE, mul_left_comm] at h
    have hc := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (ℓ : ℤ_[ℓ]) ≠ 0) h
    have hz := congrArg (PadicInt.toZMod (p := ℓ)) hc
    simp only [map_mul, map_neg, map_natCast, map_ofNat, hu] at hz
    have hl1 : (((ℓ - 1 : ℕ) : ZMod ℓ)) = -1 := by
      rw [Nat.cast_sub hp.one_le, CharP.cast_eq_zero]
      simp
    rw [hl1] at hz
    linear_combination (-1 : ZMod ℓ) * hz
  ext n
  rw [coeff_theta, coeff_map, coeff_C_mul, map_sub, coeff_E2_bar, PowerSeries.coeff_expand]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_E2_bar]
  rw [hen n hn, if_neg hn]
  have hs := sigma_mul_mod (ℓ := ℓ) h3 n hn
  have h12' : (12 : ZMod ℓ)⁻¹ * 24 = 2 := by
    field_simp
    norm_num
  split_ifs with hd
  · have hm : n / ℓ ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ hp.pos]
      rintro rfl
      simp at hn
    rw [coeff_E2_bar, if_neg hm]
    rw [if_pos hd] at hs
    linear_combination (-2 : ZMod ℓ) * hs + (((ArithmeticFunction.sigma 1 n : ℕ) : ZMod ℓ) -
      ((ArithmeticFunction.sigma 1 (n / ℓ) : ℕ) : ZMod ℓ)) * h12'
  · rw [if_neg hd] at hs
    linear_combination (-2 : ZMod ℓ) * hs + ((ArithmeticFunction.sigma 1 n : ℕ) : ZMod ℓ) * h12'

/-- **The Rankin–Cohen lift of `θ`.** For `g` over `ℤ_ℓ`, the bracket `F = k g θE - (ℓ-1) E θg` of `g` with `E = E_{ℓ-1}`
reduces to `θḡ`, and `(UF)/ℓ` reduces to `(1/k) θ(Uḡ) + ((k-1)/k)(∂(Uḡ) - U(∂ḡ))`. -/
theorem rc_lift (hℓ5 : 5 ≤ ℓ) (k : ℕ) (hk : (k : ZMod ℓ) ≠ 0) (g : PowerSeries ℤ_[ℓ]) :
    let E := TateCurve.EhasseZp ℓ (by omega)
    let F := (k : PowerSeries ℤ_[ℓ]) * g * theta E - ((ℓ : PowerSeries ℤ_[ℓ]) - 1) * E * theta g
    let φ := PowerSeries.map (PadicInt.toZMod (p := ℓ))
    φ F = theta (φ g) ∧ ∃ G : PowerSeries ℤ_[ℓ], U ℓ F = (ℓ : PowerSeries ℤ_[ℓ]) * G ∧
      φ G = C (k : ZMod ℓ)⁻¹ * theta (U ℓ (φ g)) + C (((k : ZMod ℓ) - 1) * (k : ZMod ℓ)⁻¹) *
        (serreBar k (U ℓ (φ g)) - U ℓ (serreBar k (φ g))) := by
  intro E F φ
  have hE1 : φ E = 1 := TateCurve.map_toZMod_EhasseZp (by omega)
  obtain ⟨e, he⟩ : ∃ e : PowerSeries ℤ_[ℓ], E = 1 + (ℓ : PowerSeries ℤ_[ℓ]) * e := by
    obtain ⟨e, he⟩ := AtkinOBrienFinal.PS_dvd_of_map (E - 1) (by rw [map_sub, hE1, map_one, sub_self])
    refine ⟨e, ?_⟩
    rw [sub_eq_iff_eq_add'.mp he, PowerSeries.smul_eq_C_mul, map_natCast]
  have hθ := theta_e hℓ5 e he
  have hl0 : φ (ℓ : PowerSeries ℤ_[ℓ]) = 0 := by
    rw [map_natCast, natCast_self_series]
  have hk' : φ (k : PowerSeries ℤ_[ℓ]) = C (k : ZMod ℓ) := by
    rw [map_natCast, map_natCast]
  have hθE : theta E = (ℓ : PowerSeries ℤ_[ℓ]) * theta e := by
    rw [he, theta_add, theta_one, zero_add, theta_natCast_mul]
  have hFe : F = theta g + (ℓ : PowerSeries ℤ_[ℓ]) * ((k : PowerSeries ℤ_[ℓ]) * (g * theta e) +
      (((ℓ : PowerSeries ℤ_[ℓ]) - 1) * -1) * (e * theta g) - theta g) := by
    change (k : PowerSeries ℤ_[ℓ]) * g * theta E - ((ℓ : PowerSeries ℤ_[ℓ]) - 1) * E * theta g = _
    rw [hθE, he]
    ring
  refine ⟨?_, ?_⟩
  · rw [hFe, map_add, map_mul, hl0, zero_mul, add_zero, map_theta]
  · set H := (k : PowerSeries ℤ_[ℓ]) * (g * theta e) + (((ℓ : PowerSeries ℤ_[ℓ]) - 1) * -1) * (e * theta g) -
      theta g with hH
    refine ⟨theta (U ℓ g) + U ℓ H, ?_, ?_⟩
    · rw [hFe, U_add, U_theta, U_natCast_mul, mul_add]
    · have hHb : φ H = C (k : ZMod ℓ) * (φ g * theta (φ e)) + φ e * theta (φ g) - theta (φ g) := by
        have hm : ∀ x, φ (theta x) = theta (φ x) := fun x => map_theta _ x
        rw [hH]
        simp only [map_sub, map_add, map_mul, map_neg, map_one, hl0, hk', hm]
        ring
      have hc := rc_core (ℓ := ℓ) k hk (φ g) (φ e) hθ
      rw [map_add, map_theta, map_U, map_U, hHb]
      exact hc

end

end RamanujanTau.BLBound
