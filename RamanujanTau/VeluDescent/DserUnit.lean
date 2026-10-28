/-
# `Dser = c · U` with `U ∈ 𝒪⟦z⟧ˣ` and `‖c‖ = ‖μ‖³`
-/
import RamanujanTau.VeluDescent.Denominator

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "jK" => Subring.subtype (CanonicalIsogeny.integers K)

variable {a b : ↥(CanonicalIsogeny.integers K)}

lemma map_rho_sub {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    MvPowerSeries.map jK (C (rhoh a b h) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) =
      C ((rhoh a b h : 𝒪) : K) * uQs (Pt a b h) := by
  have e := rhoh_mul_xc (a := a) (b := b) h0 hh
  have e1 : MvPowerSeries.map jK (X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) =
      X () ^ 2 * vv (a : K) (b : K) := by rw [map_mul, map_pow, map_X, map_v_short]
  rw [map_sub, map_C, e1, uQs, Subring.subtype_apply]
  have : C ((rhoh a b h : 𝒪) : K) * C (Velu.xc (Pt a b h)) = (1 : MvPowerSeries Unit K) := by
    rw [← map_mul, e, map_one]
  linear_combination (X () ^ 2 * vv (a : K) (b : K)) * this

lemma isUnit_one_sub (r : 𝒪) :
    IsUnit (1 - C r * X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) := by
  rw [isUnit_iff_constantCoeff]
  simp

variable (S : Lubin.FinSub (formalGroup (shortO a b))) (κ : Velu.Kernel (a : K) (b : K))
  (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) =
    Pt a b '' (S.H : Set ↥(CanonicalIsogeny.integers K)))

include hκ

/-- **`Dser = c · U`**, `U` a unit, `‖c‖ = ‖μ‖³`. -/
theorem Dser_eq [IsAlgClosed K] (hΔ : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0) :
    ∃ c : 𝒪, ‖(c : K)‖ = ‖((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K)‖ ^ 3 ∧
      ∃ U : MvPowerSeries Unit 𝒪, IsUnit U ∧ Dser S = C c * U := by
  classical
  obtain ⟨e, hinj, he⟩ := exists_roots (K := K) (A := (a : K)) (B := (b : K)) hΔ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hpair : ∀ Q ∈ κ.S, ∃ U : MvPowerSeries Unit 𝒪, IsUnit U ∧
      wh a b (hQ S Q) * wh a b (-hQ S Q) =
        (C (rhoh a b (hQ S Q)) - X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) ^ 3 * U :=
    fun Q hQ' => wh_pair S (hQ_spec S κ hκ hQ').1 (hQ_ne S κ hκ hQ')
  choose! UQ hUQ hUQe using hpair
  set P3 := (Finset.univ : Finset (Fin 3)) ×ˢ κ.S with hP3
  have hr : ∀ p ∈ P3, ‖Kernel'.rr h2 hΔ he p‖ ≤ 1 := by
    intro p hp
    have hp2 := (Finset.mem_product.1 hp).2
    have hs := hQ_spec S κ hκ hp2
    refine norm_rr_aux (a := a) (norm_root_le (b := b) (he p.1)) ?_
      (Kernel'.xc_add_two_torsion κ h2 hΔ (he p.1) hp2)
    rw [← hs.2]; exact norm_xc_Pt (hQ_ne S κ hκ hp2) (norm_lt_one_of_tn (S.tn _ hs.1))
  set r' : Fin 3 × (Velu.short (a : K) (b : K)).Point → 𝒪 := fun p =>
    if hp : p ∈ P3 then ⟨Kernel'.rr h2 hΔ he p, hr p hp⟩ else 0 with hr'
  have hr'v : ∀ p ∈ P3, ((r' p : 𝒪) : K) = Kernel'.rr h2 hΔ he p := by
    intro p hp; simp only [hr', dif_pos hp]
  set ρQ : (Velu.short (a : K) (b : K)).Point → 𝒪 := fun Q => rhoh a b (hQ S Q) with hρQ
  have hcoe : ((∏ Q ∈ κ.S, ρQ Q ^ 3 : 𝒪) : K) = ∏ Q ∈ κ.S, ((ρQ Q : 𝒪) : K) ^ 3 := by
    rw [SubmonoidClass.coe_finsetProd]
    exact Finset.prod_congr rfl (fun Q _ => SubmonoidClass.coe_pow _ _)
  refine ⟨∏ Q ∈ κ.S, ρQ Q ^ 3, ?_,
    (∏ p ∈ P3, (1 - C (r' p) * X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪))) *
      ∏ Q ∈ κ.S, UQ Q, ?_, ?_⟩
  · -- the norm
    rw [norm_coeff_pis S κ hκ, ← Finset.prod_pow,
      hcoe, norm_prod]
    refine Finset.prod_congr rfl fun Q hQ' => ?_
    have hs := hQ_spec S κ hκ hQ'
    rw [norm_pow, hρQ]
    simp only [rhoh, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow,
      norm_vpt (norm_lt_one_of_tn (S.tn _ hs.1)), mul_one]
  · exact (IsUnit.prod_iff.2 fun p _ => isUnit_one_sub (r' p)).mul
      (IsUnit.prod_iff.2 fun Q hQ' => hUQ Q hQ')
  · apply VeluLubin.map_inj jK Subtype.val_injective
    rw [map_Dser S κ hκ, Wst_eq S κ hκ, map_prod]
    have hQm : ∀ Q ∈ κ.S, MvPowerSeries.map jK (wh a b (hQ S Q) * wh a b (-hQ S Q)) =
        (C ((ρQ Q : 𝒪) : K) * uQs Q) ^ 3 * MvPowerSeries.map jK (UQ Q) := by
      intro Q hQ'
      have hs := hQ_spec S κ hκ hQ'
      rw [hUQe Q hQ', map_mul, map_pow, map_rho_sub (hQ_ne S κ hκ hQ')
        (norm_lt_one_of_tn (S.tn _ hs.1)), hs.2]
    have hP : ∏ p ∈ P3, MvPowerSeries.map jK
        (1 - C (r' p) * X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) =
        ∏ p ∈ P3, (1 - C (Kernel'.rr h2 hΔ he p) * rho (a : K) (b : K)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have e1 : MvPowerSeries.map jK (C (r' p) * X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪)) =
          C ((r' p : 𝒪) : K) * (X () ^ 2 * vv (a : K) (b : K)) := by
        rw [map_mul, map_mul, map_C, map_pow, map_X, map_v_short, Subring.subtype_apply, mul_assoc]
      rw [map_sub, map_one, e1, hr'v p hp, rho]
    have hXd := Xd_mul_prod κ h2 hΔ he hinj
    set Cρ := ∏ Q ∈ κ.S, C (((ρQ Q : 𝒪) : K)) ^ 3 with hCρ
    have hL : Xd κ * ∏ Q ∈ κ.S, MvPowerSeries.map jK (wh a b (hQ S Q) * wh a b (-hQ S Q)) =
        Cρ * (Xd κ * ∏ Q ∈ κ.S, uQs Q ^ 3) * ∏ Q ∈ κ.S, MvPowerSeries.map jK (UQ Q) := by
      rw [Finset.prod_congr rfl hQm, Finset.prod_mul_distrib, Finset.prod_congr rfl
        (fun Q _ => mul_pow (C ((ρQ Q : 𝒪) : K)) (uQs Q) 3), Finset.prod_mul_distrib]
      ring
    have hR : MvPowerSeries.map jK (C (∏ Q ∈ κ.S, ρQ Q ^ 3) *
        ((∏ p ∈ P3, (1 - C (r' p) * X () ^ 2 * (v (shortO a b) : MvPowerSeries Unit 𝒪))) *
          ∏ Q ∈ κ.S, UQ Q)) =
        Cρ * (∏ p ∈ P3, (1 - C (Kernel'.rr h2 hΔ he p) * rho (a : K) (b : K))) *
          ∏ Q ∈ κ.S, MvPowerSeries.map jK (UQ Q) := by
      rw [map_mul, map_mul, map_C, Subring.subtype_apply, hcoe,
        map_prod (MvPowerSeries.map jK) _ P3, map_prod (MvPowerSeries.map jK) _ κ.S, hP,
        map_prod (C : K →+* MvPowerSeries Unit K) _ κ.S, hCρ]
      simp only [map_pow]
      ring
    rw [hL, hR, hXd]

end VeluDescent
