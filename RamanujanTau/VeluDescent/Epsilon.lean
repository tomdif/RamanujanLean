/-
# `μ³ w'(φ) = π³ · ε(π)` with `ε ∈ 𝒪⟦T⟧`

With `Dser = c · U` (`Dser_eq`), the integral series `ε̃ = (μ³/c) · Vall · U⁻¹` satisfies
`Dser · ε̃ = μ³ · Vall`; it is `S`-invariant, hence (Lubin's descent) `ε̃ = ε(π)`. Since
`Dser = Xd · Wst` and `Wall = w · Wst = π³ · Vall`:
  `μ³ · w'(φ(z)) = μ³ · w/Xd = π(z)³ · ε(π(z))`         (`exists_eps`)
where `w'(φ) = wphi κ` is the `w`-series of the Vélu curve at the formal Vélu map.
-/
import RamanujanTau.VeluDescent.DserUnit

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "jK" => Subring.subtype (CanonicalIsogeny.integers K)

variable {a b : ↥(CanonicalIsogeny.integers K)}

variable (S : Lubin.FinSub (formalGroup (shortO a b))) (κ : Velu.Kernel (a : K) (b : K))
  (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) =
    Pt a b '' (S.H : Set ↥(CanonicalIsogeny.integers K)))

lemma Dser_ne : Dser S ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [Dser, map_sum, map_zero] at this
  -- the constant term is `∏_{h≠0} w(h) ≠ 0`
  have e : ∀ h ∈ S.H, constantCoeff (∏ h' ∈ S.H, (if h' = h then 1 else wh a b h')) =
      if h = 0 then ∏ h' ∈ S.H.erase 0, wz a b h' else 0 := by
    intro h hh
    rw [map_prod]
    by_cases h0 : h = 0
    · rw [if_pos h0, ← Finset.mul_prod_erase _ _ hh, if_pos rfl, map_one, one_mul, h0]
      refine Finset.prod_congr rfl fun h' hh' => ?_
      rw [if_neg (Finset.ne_of_mem_erase hh'), cc_wh (S.tn h' (Finset.mem_of_mem_erase hh'))]
    · rw [if_neg h0]
      apply Finset.prod_eq_zero S.zero_mem
      rw [if_neg (Ne.symm h0), wh_zero, show constantCoeff (w (shortO a b) : MvPowerSeries Unit 𝒪) =
        PowerSeries.constantCoeff (w (shortO a b)) from rfl, cc_w]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' S.H 0, if_pos S.zero_mem] at this
  rcases Finset.prod_eq_zero_iff.1 this with ⟨h', hh', e0⟩
  have nh := norm_lt_one_of_tn (S.tn h' (Finset.mem_of_mem_erase hh'))
  exact wz_ne_zero a b nh (Finset.ne_of_mem_erase hh') (by rw [e0]; rfl)

include hκ

/-- **`μ³ · w'(φ) = π³ · ε(π)`**. -/
theorem exists_eps [IsAlgClosed K] (hΔ : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0) :
    ∃ ε : MvPowerSeries Unit 𝒪,
      C (((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) ^ 3) * wphi κ =
        MvPowerSeries.map jK (Lubin.pis S) ^ 3 *
          sb (MvPowerSeries.map jK (Lubin.pis S)) (MvPowerSeries.map jK ε) := by
  classical
  obtain ⟨c, hc, U, hU, hD⟩ := Dser_eq S κ hκ hΔ
  set μ : 𝒪 := coeff (Finsupp.single () 1) (Lubin.pis S) with hμ
  have hμ0 : ((μ : 𝒪) : K) ≠ 0 := by
    rw [hμ, coeff_pis, SubmonoidClass.coe_finsetProd]
    exact Finset.prod_ne_zero_iff.2 fun h hh => fun e => Finset.ne_of_mem_erase hh (Subtype.ext e)
  have hc0 : ((c : 𝒪) : K) ≠ 0 := by
    intro e; rw [e, norm_zero] at hc
    exact pow_ne_zero 3 (norm_ne_zero_iff.2 hμ0) hc.symm
  have hk : ‖((μ : K) ^ 3 / (c : K))‖ ≤ 1 := by
    rw [norm_div, norm_pow, hc, div_self (pow_ne_zero 3 (norm_ne_zero_iff.2 hμ0))]
  set k : 𝒪 := ⟨(μ : K) ^ 3 / (c : K), hk⟩ with hkd
  have hck : c * k = μ ^ 3 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_pow, hkd]
    field_simp
  set Ui : MvPowerSeries Unit 𝒪 := ((hU.unit⁻¹ : (MvPowerSeries Unit 𝒪)ˣ) : MvPowerSeries Unit 𝒪)
  have hUi : U * Ui = 1 := hU.mul_val_inv
  set et : MvPowerSeries Unit 𝒪 := C k * Vall S * Ui with het
  have hDe : Dser S * et = C (μ ^ 3) * Vall S := by
    rw [hD, het, ← hck, map_mul]
    linear_combination (C c * C k * Vall S) * hUi
  -- invariance and descent
  have hinv : Lubin.Inv S () et := by
    intro h hh
    have hE := adm_trs (a := a) (b := b) (S.tn h hh)
    have h1 := congrArg (Lubin.E (Lubin.trs (F := formalGroup (shortO a b)) () h)) hDe
    rw [Lubin.E_mul hE (Dser S) et, Lubin.E_mul hE (C (μ ^ 3)) (Vall S), Lubin.E_C, inv_Dser S h hh,
      inv_Vall S h hh, ← hDe] at h1
    exact mul_left_cancel₀ (Dser_ne S) h1
  obtain ⟨ε, hε⟩ := Lubin.descent S () hinv
  have hbs : Lubin.bs S () = fun _ : Unit => Lubin.pis S := by
    funext u; cases u; rw [Lubin.bs_self]; rfl
  rw [hbs, Lubin.E_eq_subst (fun _ => Lubin.cc_pis S)] at hε
  refine ⟨ε, ?_⟩
  rw [← map_sb jK (Lubin.cc_pis S), sb, hε]
  -- compare after multiplying by `Dser`
  have hDK : MvPowerSeries.map jK (Dser S) ≠ 0 := by
    intro e
    exact Dser_ne S (VeluLubin.map_inj jK Subtype.val_injective (e.trans (map_zero _).symm))
  apply mul_right_cancel₀ hDK
  have hL : C (((μ : 𝒪) : K) ^ 3) * wphi κ * MvPowerSeries.map jK (Dser S) =
      C (((μ : 𝒪) : K) ^ 3) * MvPowerSeries.map jK (Wall S) := by
    rw [map_Dser S κ hκ, Wall_eq_w_mul, map_mul, map_w_short, wphi]
    have := Xd_mul_inv κ
    linear_combination (C (((μ : 𝒪) : K) ^ 3) * ww (a : K) (b : K) * MvPowerSeries.map jK (Wst S)) *
      this
  rw [hL, ← map_pow, ← map_mul, ← map_mul, mul_assoc, mul_comm et, hDe, Wall_eq_pis, map_mul,
    map_mul, map_mul, map_C, map_pow (Subring.subtype _), Subring.subtype_apply]
  ring

end VeluDescent
