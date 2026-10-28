import RamanujanTau.ModP.Structure
import RamanujanTau.ModP.SwinnertonDyer
import RamanujanTau.HeckeQExp

/-!
# Integral level-one modular forms, `T_ℓ`, and Sturm's bound mod `ℓ`

* `IntForm k a`: the integer series `a ∈ ℤ⟦q⟧` is the q-expansion of a level-one modular form of
  weight `k`. It is closed under `+`, `−`, integer scalars, products and powers. It contains
  `Δ = q∏(1−qⁿ)²⁴`, `E₄`, `E₆` and the monomials `E₄ᵃE₆ᵇ`.
* `IntForm.hecke`: `T_ℓ` acts on integral cusp forms by
  `a ↦ Σ_m (a(ℓm) + ℓ^{k−1}[ℓ ∣ m] a(m/ℓ)) qᵐ`.
* **`sturm`** (Sturm's bound mod `ℓ` in level one): if `a` is integral of weight `k` and its first
  `⌊k/12⌋ + 1` coefficients vanish mod `ℓ`, then `a ≡ 0 (mod ℓ)`.
* `exists_hasse_lift`: an integral form `A` of weight `ℓ − 1` with `A ≡ 1 (mod ℓ)` (a lift of the
  Swinnerton-Dyer Hasse polynomial `ModP.hasseBar`).
* **`U_eq_of_sturm`**: if `a` is an integral cusp form of weight `k ≥ 2` and `b` an integral form of
  weight `k` with `a(ℓn) ≡ b(n)` for `n ≤ k/12`, then `U_ℓ a ≡ b (mod ℓ)` as q-series.
-/

set_option autoImplicit false

namespace BoylanWebb
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane ModP
open scoped MatrixGroups
open RamanujanTau.DiscriminantBridge (Δmod)
open RamanujanTau.Mod691 (p4 p6)

/-- reduction `ℤ⟦q⟧ → (ℤ/ℓ)⟦q⟧`. -/
noncomputable abbrev Ψ (ℓ : ℕ) : PowerSeries ℤ →+* PowerSeries (ZMod ℓ) :=
  PowerSeries.map (Int.castRingHom (ZMod ℓ))

/-- `U_ℓ : Σ aₙ qⁿ ↦ Σ a_{ℓn} qⁿ`. -/
noncomputable def U {R : Type*} [CommRing R] (ℓ : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => PowerSeries.coeff (ℓ * n) f

lemma coeff_U {R : Type*} [CommRing R] (ℓ n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n (U ℓ f) = PowerSeries.coeff (ℓ * n) f := by
  rw [U, PowerSeries.coeff_mk]

/-- `a ∈ ℤ⟦q⟧` is the q-expansion of a level-one modular form of weight `k`. -/
def IntForm (k : ℤ) (a : PowerSeries ℤ) : Prop :=
  ∃ F : ModularForm 𝒮ℒ k, qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) a

/-- the Hecke operator `T_ℓ` in weight `e + 1`, on integer q-series. -/
noncomputable def heckeSeries (ℓ e : ℕ) (a : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => PowerSeries.coeff (ℓ * m) a +
    (ℓ : ℤ) ^ e * (if ℓ ∣ m then PowerSeries.coeff (m / ℓ) a else 0)

lemma map_injC : Function.Injective (PowerSeries.map (Int.castRingHom ℂ)) :=
  PowerSeries.map_injective _ (RingHom.injective_int _)

namespace IntForm
variable {k k' : ℤ} {a b : PowerSeries ℤ}

lemma cast (h : k = k') (ha : IntForm k a) : IntForm k' a := by subst h; exact ha

lemma zero : IntForm k 0 := ⟨0, by rw [ModularForm.coe_zero, qExpansion_zero, map_zero]⟩

lemma one : IntForm 0 1 := ⟨1, by rw [ModularForm.qExpansion_one, map_one]⟩

lemma add (ha : IntForm k a) (hb : IntForm k b) : IntForm k (a + b) := by
  obtain ⟨F, hF⟩ := ha; obtain ⟨G, hG⟩ := hb
  exact ⟨F + G, by rw [ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos
    one_mem_strictPeriods_SL, hF, hG, map_add]⟩

lemma sub (ha : IntForm k a) (hb : IntForm k b) : IntForm k (a - b) := by
  obtain ⟨F, hF⟩ := ha; obtain ⟨G, hG⟩ := hb
  exact ⟨F - G, by rw [ModularForm.coe_sub, ModularFormClass.qExpansion_sub one_pos
    one_mem_strictPeriods_SL, hF, hG, map_sub]⟩

lemma C_mul (c : ℤ) (ha : IntForm k a) : IntForm k (PowerSeries.C c * a) := by
  obtain ⟨F, hF⟩ := ha
  refine ⟨(c : ℂ) • F, ?_⟩
  rw [show (((c : ℂ) • F : ModularForm 𝒮ℒ k) : ℍ → ℂ) = (c : ℂ) • (F : ℍ → ℂ) from rfl,
    ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF, map_mul,
    PowerSeries.map_C, PowerSeries.smul_eq_C_mul]
  rfl

lemma mul (ha : IntForm k a) (hb : IntForm k' b) : IntForm (k + k') (a * b) := by
  obtain ⟨F, hF⟩ := ha; obtain ⟨G, hG⟩ := hb
  exact ⟨F.mul G, by rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF, hG,
    map_mul]⟩

lemma pow (ha : IntForm k a) (n : ℕ) : IntForm (n * k) (a ^ n) := by
  induction n with
  | zero => simpa using (one : IntForm 0 1)
  | succ n ih => rw [pow_succ]; exact (ih.mul ha).cast (by push_cast; ring)

lemma disc : IntForm 12 (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24) :=
  ⟨Δmod, RamanujanTau.TauModular.qExpansion_discriminant_eq⟩

lemma E4 : IntForm 4 p4 := ⟨E₄, by rw [qExpansion_E4]; rfl⟩

lemma E6 : IntForm 6 p6 := ⟨E₆, by rw [qExpansion_E6]; rfl⟩

lemma mono (a b : ℕ) : IntForm ((4 * a + 6 * b : ℕ) : ℤ) (p4 ^ a * p6 ^ b) := by
  obtain ⟨F, hF⟩ := exists_mono_form a b
  refine ⟨F, ?_⟩
  rw [hF, map_mul, map_pow, map_pow]; rfl

/-- `T_ℓ` preserves integral cusp forms of weight `e + 1`. -/
lemma hecke (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ) (hk : k = e + 1) (ha : IntForm k a)
    (h0 : PowerSeries.coeff 0 a = 0) : IntForm k (heckeSeries ℓ e a) := by
  obtain ⟨F, hF⟩ := ha
  have hF0 : (qExpansion 1 F).coeff 0 = 0 := by rw [hF, PowerSeries.coeff_map, h0, map_zero]
  set gc := ModularForm.toCuspForm F hF0
  refine ⟨CuspForm.toModularFormₗ (RamanujanTau.Hecke.heckeCusp ℓ gc), ?_⟩
  ext m
  change (qExpansion 1 (RamanujanTau.Hecke.heckeCusp ℓ gc)).coeff m = _
  rw [RamanujanTau.Hecke.qExpansion_hecke, PowerSeries.coeff_map, heckeSeries, PowerSeries.coeff_mk]
  have hq : qExpansion 1 gc = qExpansion 1 F := rfl
  rw [hq, hF, PowerSeries.coeff_map, hk, show ((e : ℤ) + 1 - 1) = (e : ℤ) by ring, zpow_natCast]
  split_ifs <;> simp [PowerSeries.coeff_map]

end IntForm

section Sturm
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

lemma Ψ_eq_zero_of_form_zero {k : ℤ} {a : PowerSeries ℤ} (F : ModularForm 𝒮ℒ k)
    (hF : qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) a) (h0 : (F : ℍ → ℂ) = 0) :
    Ψ ℓ a = 0 := by
  have : PowerSeries.map (Int.castRingHom ℂ) a = 0 := by rw [← hF, h0, qExpansion_zero]
  rw [show a = 0 from map_injC (by rw [this, map_zero]), map_zero]

/-- **Sturm's bound mod `ℓ`, level one.** -/
theorem sturm : ∀ (N : ℕ) (k : ℤ), k < 12 * N → ∀ a : PowerSeries ℤ, IntForm k a →
    (PowerSeries.X : PowerSeries (ZMod ℓ)) ^ (k.toNat / 12 + 1) ∣ Ψ ℓ a → Ψ ℓ a = 0 := by
  intro N
  induction N with
  | zero =>
    intro k hk a ⟨F, hF⟩ _
    exact Ψ_eq_zero_of_form_zero ℓ F hF (levelOne_neg_weight_eq_zero (by omega) F)
  | succ N ih =>
    intro k hk a ⟨F, hF⟩ hdvd
    rcases lt_or_ge k 0 with hneg | hnn
    · exact Ψ_eq_zero_of_form_zero ℓ F hF (levelOne_neg_weight_eq_zero hneg F)
    rcases Int.even_or_odd k with hev | hodd
    swap
    · exact Ψ_eq_zero_of_form_zero ℓ F hF (by rw [levelOne_odd_weight_eq_zero hodd F,
        ModularForm.coe_zero])
    by_cases h2 : k = 2
    · subst h2
      have := levelOne_weight_two_rank_zero
      rw [rank_zero_iff_forall_zero] at this
      exact Ψ_eq_zero_of_form_zero ℓ F hF (by rw [this F, ModularForm.coe_zero])
    set n := k.toNat with hn
    have hkn : k = (n : ℤ) := by omega
    have hn' : 4 * bexp0 n + 6 * bexp1 n = n := by
      obtain ⟨m, hm⟩ := hev
      unfold bexp0 bexp1; omega
    set m := p4 ^ bexp0 n * p6 ^ bexp1 n with hm
    have hmF : IntForm k m := (IntForm.mono _ _).cast (by rw [hn', hkn])
    have hm0 : PowerSeries.constantCoeff m = 1 := by
      rw [hm, map_mul, map_pow, map_pow]
      have h4 : PowerSeries.constantCoeff p4 = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p4]; simp
      have h6 : PowerSeries.constantCoeff p6 = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p6]; simp
      rw [h4, h6, one_pow, one_pow, one_mul]
    set c := PowerSeries.coeff 0 a with hc
    set r := a - PowerSeries.C c * m with hr
    have hrF : IntForm k r := (IntForm.sub ⟨F, hF⟩ (hmF.C_mul c))
    have hr0 : PowerSeries.constantCoeff r = 0 := by
      rw [hr, map_sub, map_mul, PowerSeries.constantCoeff_C, hm0, mul_one,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
    obtain ⟨r', hr'⟩ := PowerSeries.X_dvd_iff.mpr hr0
    obtain ⟨Fr, hFr⟩ := hrF
    have hFr0 : (qExpansion 1 Fr).coeff 0 = 0 := by
      rw [hFr, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hr0, map_zero]
    set gc := ModularForm.toCuspForm Fr hFr0 with hgc
    set h := CuspForm.divDiscriminant gc with hh
    have hfun : (Fr : ℍ → ℂ) = (Δmod : ℍ → ℂ) * (h : ℍ → ℂ) := by
      ext z
      have := congrArg (fun F : CuspForm 𝒮ℒ k => F z) (CuspForm.discriminantEquiv.left_inv gc)
      simp only at this
      change _ = Δmod z * h z
      rw [← ModularForm.toCuspForm_apply Fr hFr0 z, ← hgc]
      exact this.symm
    have hqgh : qExpansion 1 Fr = PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24) * qExpansion 1 h := by
      rw [hfun, UpperHalfPlane.qExpansion_mul (analytic _ Δmod) (analytic _ h),
        RamanujanTau.TauModular.qExpansion_discriminant_eq]
    obtain ⟨W, hW⟩ := exists_inv_U
    set b := W * r' with hb
    have hbq : qExpansion 1 h = PowerSeries.map (Int.castRingHom ℂ) b := by
      have e1 : PowerSeries.map (Int.castRingHom ℂ) r =
          PowerSeries.X * (PowerSeries.map (Int.castRingHom ℂ) (MockTheta5.JTP.qfacInf ^ 24) *
            qExpansion 1 h) := by
        rw [← hFr, hqgh, map_mul, PowerSeries.map_X, mul_assoc]
      rw [hr', map_mul, PowerSeries.map_X] at e1
      have e2 := PowerSeries.X_mul_cancel e1
      have hW' : PowerSeries.map (Int.castRingHom ℂ) W *
          PowerSeries.map (Int.castRingHom ℂ) (MockTheta5.JTP.qfacInf ^ 24) = 1 := by
        rw [← map_mul, mul_comm, hW, map_one]
      rw [hb, map_mul, e2, ← mul_assoc, hW', one_mul]
    -- reduction mod ℓ
    have hc0 : (c : ZMod ℓ) = 0 := by
      have := (PowerSeries.X_pow_dvd_iff.mp hdvd) 0 (by omega)
      rwa [PowerSeries.coeff_map] at this
    have hΨr : Ψ ℓ r = Ψ ℓ a := by
      rw [hr, map_sub, map_mul, PowerSeries.map_C]; simp [hc0]
    have hΨr' : (PowerSeries.X : PowerSeries (ZMod ℓ)) ^ (n / 12) ∣ Ψ ℓ r' := by
      have h1 : (PowerSeries.X : PowerSeries (ZMod ℓ)) * PowerSeries.X ^ (n / 12) ∣
          PowerSeries.X * Ψ ℓ r' := by
        rw [← pow_succ', ← PowerSeries.map_X (Int.castRingHom (ZMod ℓ)), ← map_mul, ← hr', hΨr,
          PowerSeries.map_X]
        exact hdvd
      exact (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp h1
    have hfin : Ψ ℓ r' = 0 → Ψ ℓ a = 0 := by
      intro h0
      rw [← hΨr, hr', map_mul, h0, mul_zero]
    have hr'b : r' = MockTheta5.JTP.qfacInf ^ 24 * b := by
      rw [hb, ← mul_assoc, hW, one_mul]
    by_cases hk12 : k < 12
    · have hh0 : (h : ℍ → ℂ) = 0 := levelOne_neg_weight_eq_zero (by omega) h
      apply hfin
      have : b = 0 := map_injC (by rw [← hbq, hh0, qExpansion_zero, map_zero])
      rw [hr'b, this, mul_zero, map_zero]
    · have hb0 : Ψ ℓ b = 0 := by
        refine ih (k - 12) (by push_cast at hk; omega) b ⟨h, hbq⟩ ?_
        have : (k - 12).toNat / 12 + 1 = n / 12 := by omega
        rw [this, hb, map_mul]
        exact Dvd.dvd.mul_left hΨr' _
      apply hfin
      rw [hr'b, map_mul, hb0, mul_zero]

/-- every isobaric `P ∈ 𝔽_ℓ[E₄,E₆]` lifts to an integral form. -/
theorem lift_iso (k : ℕ) (P : MvPolynomial (Fin 2) (ZMod ℓ)) (hP : Iso P k) :
    ∃ a, IntForm k a ∧ Ψ ℓ a = ev (ZMod ℓ) P := by
  have key : ∀ s : Finset (Fin 2 →₀ ℕ), s ⊆ P.support → ∃ a, IntForm k a ∧
      Ψ ℓ a = ev (ZMod ℓ) (∑ d ∈ s, MvPolynomial.monomial d (MvPolynomial.coeff d P)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, IntForm.zero, by simp⟩
    | insert d s hds ih =>
      intro hsub
      obtain ⟨a, ha, hae⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hd : MvPolynomial.coeff d P ≠ 0 := MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self _ _))
      have hw : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP hd
      refine ⟨PowerSeries.C ((MvPolynomial.coeff d P).val : ℤ) * (p4 ^ d 0 * p6 ^ d 1) + a,
        (((IntForm.mono (d 0) (d 1)).cast (by rw [hw])).C_mul _).add ha, ?_⟩
      rw [Finset.sum_insert hds, map_add, map_add, hae, monomial_eq_two, map_mul, map_mul, map_mul,
        map_mul, map_pow, map_pow, map_pow, map_pow, ev_X0, ev_X1, ev_C, PowerSeries.map_C]
      congr 2
      · simp
  obtain ⟨a, ha, hae⟩ := key P.support subset_rfl
  exact ⟨a, ha, by rw [hae, ← MvPolynomial.as_sum]⟩

/-- an integral form of weight `ℓ − 1` congruent to `1` mod `ℓ`. -/
theorem exists_hasse_lift (hℓ5 : 5 ≤ ℓ) : ∃ A, IntForm ((ℓ - 1 : ℕ) : ℤ) A ∧ Ψ ℓ A = 1 := by
  obtain ⟨A, hA, hAe⟩ := lift_iso ℓ (ℓ - 1) (hasseBar ℓ hℓ5) (iso_hasseBar hℓ5)
  exact ⟨A, hA, by rw [hAe, ev_hasseBar]⟩

lemma Ψ_hecke (e : ℕ) (he : 1 ≤ e) (a : PowerSeries ℤ) : Ψ ℓ (heckeSeries ℓ e a) = U ℓ (Ψ ℓ a) := by
  ext m
  rw [PowerSeries.coeff_map, heckeSeries, PowerSeries.coeff_mk, coeff_U, PowerSeries.coeff_map]
  have h0 : (Int.castRingHom (ZMod ℓ)) (ℓ : ℤ) = 0 := by simp
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, h0, zero_pow (by omega), zero_mul, add_zero]

/-- **`U_ℓ` on a cusp form, mod `ℓ`, by Sturm.** -/
theorem U_eq_of_sturm (e : ℕ) (he : 1 ≤ e) (a b : PowerSeries ℤ) (ha : IntForm ((e + 1 : ℕ) : ℤ) a)
    (ha0 : PowerSeries.coeff 0 a = 0) (hb : IntForm ((e + 1 : ℕ) : ℤ) b)
    (hcoef : ∀ n, n ≤ (e + 1) / 12 →
      PowerSeries.coeff (ℓ * n) (Ψ ℓ a) = PowerSeries.coeff n (Ψ ℓ b)) :
    U ℓ (Ψ ℓ a) = Ψ ℓ b := by
  have hT := ha.hecke ℓ e (by push_cast; ring) ha0
  have hd := sturm ℓ ((e + 1) / 12 + 1) _ (by push_cast; omega) _ (hT.sub hb) ?_
  · rw [map_sub, Ψ_hecke ℓ e he, sub_eq_zero] at hd
    exact hd
  · rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, Ψ_hecke ℓ e he, map_sub, coeff_U, Int.toNat_natCast] at *
    rw [hcoef n (by omega), sub_self]

end Sturm

end BoylanWebb
