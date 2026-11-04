import RamanujanTau.FiniteArithmetic.ExactAtkin
import RamanujanTau.FiniteArithmetic.Bernoulli28
import RamanujanTau.FiniteArithmetic.ChunkedCertificate

/-! Generic precision-`ℓ²` inputs for `ExactAtkin`: the Hasse lift `E_{ℓ−1}` and its inverse
modulo `ℓ²` from one Bernoulli value, and a builder for `StepData` from coefficient tables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.ExactAtkinPrecision
open PowerSeries AtkinOBrienFinal BoylanWebb AtkinOBrien ExactAtkin

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- The integer series `1 + c Σ σ_{ℓ−2}(n) qⁿ`. -/
noncomputable def EintG (ℓ : ℕ) (c : ℤ) : PowerSeries ℤ := PowerSeries.mk fun n =>
  (if n = 0 then 1 else 0) + c * (ArithmeticFunction.sigma (ℓ - 2) n : ℤ)

lemma coeff_EintG (c : ℤ) (n : ℕ) : coeff n (EintG ℓ c) =
    (if n = 0 then 1 else 0) + c * (ArithmeticFunction.sigma (ℓ - 2) n : ℤ) := coeff_mk _ _

lemma E_scalar (hℓ : 5 ≤ ℓ) (num den : ℤ) (hk : (den : ℚ) * TateCurve.kappa (ℓ - 1) = num) (n : ℕ) :
    (den : ℤ_[ℓ]) * coeff n (E ℓ hℓ) =
      (if n = 0 then (den : ℤ_[ℓ]) else 0) + num * (ArithmeticFunction.sigma (ℓ - 2) n : ℤ_[ℓ]) := by
  have h : (den : ℚ) * coeff n (TateCurve.Eis (ℓ - 1)) =
      (if n = 0 then (den : ℚ) else 0) + num * (ArithmeticFunction.sigma (ℓ - 2) n : ℚ) := by
    rw [TateCurve.coeff_Eis, show ℓ - 1 - 1 = ℓ - 2 by omega, mul_add, ← mul_assoc, hk]
    split_ifs <;> ring
  have he : ((coeff n (E ℓ hℓ) : ℤ_[ℓ]) : ℚ_[ℓ]) =
      ((coeff n (TateCurve.Eis (ℓ - 1)) : ℚ) : ℚ_[ℓ]) := by
    simp only [E, TateCurve.EhasseZp, coeff_mk]
  have hq := congrArg (fun x : ℚ => (x : ℚ_[ℓ])) h
  apply PadicInt.ext
  rw [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_mul, he]
  split_ifs at hq ⊢ <;> push_cast at hq ⊢ <;> linear_combination hq

theorem map_E_sq (hℓ : 5 ≤ ℓ) (num den c : ℤ) (hk : (den : ℚ) * TateCurve.kappa (ℓ - 1) = num)
    (hu : IsUnit (den : ZMod (ℓ ^ 2))) (hc : ((den * c : ℤ) : ZMod (ℓ ^ 2)) = num) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (E ℓ hℓ) = Ψ (ℓ ^ 2) (EintG ℓ c) := by
  ext n
  have h := congrArg (PadicInt.toZModPow (p := ℓ) 2) (E_scalar hℓ num den hk n)
  rw [coeff_map]
  change _ = (Int.castRingHom (ZMod (ℓ ^ 2))) (coeff n (EintG ℓ c))
  rw [coeff_EintG]
  obtain ⟨u, hu⟩ := hu
  apply u.isUnit.mul_left_cancel
  rw [hu]
  have h' : (den : ZMod (ℓ ^ 2)) * PadicInt.toZModPow 2 (coeff n (E ℓ hℓ)) =
      (if n = 0 then (den : ZMod (ℓ ^ 2)) else 0) +
        (num : ZMod (ℓ ^ 2)) * (ArithmeticFunction.sigma (ℓ - 2) n : ZMod (ℓ ^ 2)) := by
    have := h
    simp only [map_mul, map_intCast, map_add, map_natCast] at this
    rw [this]
    split_ifs <;> simp
  rw [h']
  have hc' : (den : ZMod (ℓ ^ 2)) * c = num := by exact_mod_cast hc
  simp only [map_add, map_mul, eq_intCast]
  split_ifs <;> push_cast <;>
    linear_combination (-(ArithmeticFunction.sigma (ℓ - 2) n : ZMod (ℓ ^ 2))) * hc'

lemma EintG_unit (c : ℤ) : IsUnit (EintG ℓ c) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_EintG]
  simp

noncomputable def EintInvG (ℓ : ℕ) (c : ℤ) : PowerSeries ℤ := Ring.inverse (EintG ℓ c)

lemma EintG_mul_inv (c : ℤ) : EintG ℓ c * EintInvG ℓ c = 1 := Ring.mul_inverse_cancel _ (EintG_unit c)

theorem map_Einv_sq (hℓ : 5 ≤ ℓ) (c : ℤ)
    (hE : PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (E ℓ hℓ) = Ψ (ℓ ^ 2) (EintG ℓ c)) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (Einv ℓ hℓ) = Ψ (ℓ ^ 2) (EintInvG ℓ c) := by
  have h := congrArg (PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2)) (E_mul_Einv ℓ hℓ)
  rw [map_mul, map_one, hE] at h
  have h' := congrArg (Ψ (ℓ ^ 2)) (EintG_mul_inv (ℓ := ℓ) c)
  rw [map_mul, map_one] at h'
  calc _ = Ψ (ℓ ^ 2) (EintInvG ℓ c) * (Ψ (ℓ ^ 2) (EintG ℓ c) *
        PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (Einv ℓ hℓ)) := by
          rw [← mul_assoc, mul_comm (Ψ (ℓ ^ 2) (EintInvG ℓ c)), h', one_mul]
    _ = _ := by rw [h, mul_one]

lemma map_int_sq (F : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (PowerSeries.map (Int.castRingHom ℤ_[ℓ]) F) =
      Ψ (ℓ ^ 2) F := by
  ext n
  simp only [coeff_map, Int.coe_castRingHom, map_intCast]

/-- A congruence modulo `ℓ²` is one modulo `ℓ`. -/
lemma Cg_of_sq {d : ℕ} {F G : PowerSeries ℤ} (h : Cg (ℓ ^ 2) d F G) : Cg ℓ d F G := by
  obtain ⟨q, hq⟩ := h
  have hd : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
  refine ⟨PowerSeries.map (ZMod.castHom hd (ZMod ℓ)) q, ?_⟩
  have := congrArg (PowerSeries.map (ZMod.castHom hd (ZMod ℓ))) hq
  simp only [map_sub, map_mul, map_pow, PowerSeries.map_X] at this
  convert this using 2 <;> ext n <;> simp [coeff_map]

/-! ### Building step data from coefficient tables -/

theorem mkStep {n r K : ℕ} (hK : 1 < K) (Top : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ)
    (G : Fin n → PS ℓ) (w : Fin r → ℕ → ℤ) (cv : Fin n → ℕ → ℤ)
    (hcv : ∀ k m, m < K → PadicInt.toZModPow 2 (coeff m (Top (G k))) = (cv k m : ZMod (ℓ ^ 2)))
    (tau : Fin r → Fin n → ℕ)
    (hdiv : ∀ j k, ((∑ m ∈ Finset.range K, w j m * cv k m : ℤ) : ZMod (ℓ ^ 2)) =
      ((ℓ * tau j k : ℕ) : ZMod (ℓ ^ 2)))
    (check : ∀ c : Fin n → ZMod ℓ, c ≠ 0 → ∑ k, c k * (cv k 1 : ZMod ℓ) = 0 →
      ∃ j, ∑ k, c k * (tau j k : ZMod ℓ) ≠ 0) :
    Nonempty (StepData n r K Top G w) := by
  refine ⟨⟨fun k => (cv k 1 : ZMod ℓ), tau, fun k => ?_, fun j k => ?_, check⟩⟩
  · have h := hcv k 1 hK
    rw [show ((cv k 1 : ℤ) : ZMod (ℓ ^ 2)) = PadicInt.toZModPow 2 ((cv k 1 : ℤ) : ℤ_[ℓ]) by
      rw [map_intCast]] at h
    rw [PadicDivision.mod_pow_eq_iff_dvd] at h
    have h1 : (ℓ : ℤ_[ℓ]) ∣ coeff 1 (Top (G k)) - (cv k 1 : ℤ_[ℓ]) :=
      (dvd_pow_self _ two_ne_zero).trans h
    rw [← PadicDivision.mod_eq_iff_dvd, map_intCast] at h1
    exact h1
  · rw [obs_apply, map_sum]
    have : ∀ m ∈ Finset.range K, PadicInt.toZModPow 2 ((w j m : ℤ_[ℓ]) * coeff m (Top (G k))) =
        ((w j m * cv k m : ℤ) : ZMod (ℓ ^ 2)) := fun m hm => by
      rw [map_mul, hcv k m (Finset.mem_range.mp hm), map_intCast]; push_cast; ring
    rw [Finset.sum_congr rfl this, ← Int.cast_sum, hdiv]
    simp

/-! ### From list certificates to operator coefficients -/

theorem coeff_U_of_list (hℓ : 5 ≤ ℓ) (c : ℤ)
    (hE : PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (E ℓ hℓ) = Ψ (ℓ ^ 2) (EintG ℓ c))
    (B : Poly ℓ) (bk : PowerSeries ℤ) (hev : ModP.ev ℤ_[ℓ] B = PowerSeries.map (Int.castRingHom ℤ_[ℓ]) bk)
    {d : ℕ} {L : List ℤ} (hL : Cg (ℓ ^ 2) d (bk * (EintInvG ℓ c * EintInvG ℓ c)) (toPS L))
    (m : ℕ) (hm : ℓ * m ≤ d) :
    PadicInt.toZModPow 2 (coeff m (Ulin ℓ (ModP.ev ℤ_[ℓ] B * Einv ℓ hℓ ^ 2))) =
      ((coeffList L (ℓ * m) : ℤ) : ZMod (ℓ ^ 2)) := by
  have hmap : PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (ModP.ev ℤ_[ℓ] B * Einv ℓ hℓ ^ 2) =
      Ψ (ℓ ^ 2) (bk * (EintInvG ℓ c * EintInvG ℓ c)) := by
    simp only [map_mul, map_pow, hev, map_int_sq, map_Einv_sq hℓ c hE]; ring
  rw [Ulin_apply, BoylanWebb.coeff_U, ← coeff_map, hmap]
  exact Cg_coeff hL hm

theorem coeff_D_of_list (hℓ : 5 ≤ ℓ) (c : ℤ)
    (hE : PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2) (E ℓ hℓ) = Ψ (ℓ ^ 2) (EintG ℓ c))
    (B : Poly ℓ) (bk : PowerSeries ℤ) (hev : ModP.ev ℤ_[ℓ] B = PowerSeries.map (Int.castRingHom ℤ_[ℓ]) bk)
    {d : ℕ} {L : List ℤ}
    (hL : Cg (ℓ ^ 2) d (BoylanWebb.Φ ℓ * (bk * (EintInvG ℓ c * EintInvG ℓ c))) (toPS L))
    (m : ℕ) (hm : ℓ * m ≤ d) :
    PadicInt.toZModPow 2 (coeff m (Dlin ℓ (ModP.ev ℤ_[ℓ] B * Einv ℓ hℓ ^ 2))) =
      ((coeffList L (ℓ * m) : ℤ) : ZMod (ℓ ^ 2)) := by
  have hmap : PowerSeries.map (PadicInt.toZModPow (p := ℓ) 2)
      (Φl ℓ * (ModP.ev ℤ_[ℓ] B * Einv ℓ hℓ ^ 2)) =
      Ψ (ℓ ^ 2) (BoylanWebb.Φ ℓ * (bk * (EintInvG ℓ c * EintInvG ℓ c))) := by
    simp only [map_mul, map_pow, hev, Φl, map_int_sq, map_Einv_sq hℓ c hE]; ring
  rw [Dlin_apply, BoylanWebb.coeff_U, ← coeff_map, hmap]
  exact Cg_coeff hL hm

end RamanujanTau.FiniteArithmetic.ExactAtkinPrecision
