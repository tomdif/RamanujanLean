/-
# Quotient models and Lie/Δ valuations for every order-`p` subgroup `C ⊂ F_W[p]`

`W : y² = x³ + ax + b` over `𝒪` (`K` complete, algebraically closed, ultrametric, char `0`),
`p ≥ 5`, `0 < ‖p‖ < 1`, `‖Δ_W‖ = 1`, `‖a_W‖ < 1` (supersingular reduction).

* **`model_of_finSub`**: for **any** finite subgroup `C` of `F_W` of order `p` (canonical or not) and
  any Vélu kernel `κ` with `κ.G = Pt(C)`, the `μ`-scaled Vélu curve (`μ = Lie π_C`) is integral with
  good reduction, and its formal group maps to Lubin's `F_W/C` by `ψ` with `Lie ψ = 1`.
  (Canonicity is never used: `VeluDescent.exists_integral_descent` holds for every `S`.)
* **`norm_Δ_velu`**: `‖Δ(E/C)‖ = ‖Lie π_C‖^12` (Vélu normalization `φ^*ω' = ω`), also for
  `veluC κ.G` (`SubgroupSum`).
* `norm_lie_pis`: `‖Lie π_C‖ = ∏_{c ∈ C∖0} ‖c‖`.
* **`lie_noncanonical`**: `‖Lie π_C‖^p = ‖a‖` (`v(Lie π_C) = v/p`) for `C` with no canonical point.
* **`lie_canonical`**: `‖Lie π_C‖·‖a‖ = ‖p‖` (`v(Lie π_C) = 1 − v`) for `C` of canonical points.
* **`lie_dual`**: `π̌_C ∘ π_C = [p]` with `‖Lie π̌_C‖·‖Lie π_C‖ = ‖p‖`.
-/
import RamanujanTau.AllQuotients.Model
import RamanujanTau.QuotientHasse.Main

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "ι" => Subring.subtype (CanonicalIsogeny.integers K)

section Lie
variable [CompleteSpace K] [CharZero K] [DecidableEq K]

/-- `‖Lie π_C‖ = ∏_{c ∈ C∖0} ‖c‖`. -/
lemma norm_lie_pis {a b : 𝒪} (C : Lubin.FinSub (formalGroup (shortO a b))) :
    ‖((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)‖ = ∏ c ∈ C.H.erase 0, ‖(c : K)‖ := by
  rw [VeluDescent.coeff_pis, SubmonoidClass.coe_finsetProd, norm_prod]

lemma lie_pis_ne_zero {a b : 𝒪} (C : Lubin.FinSub (formalGroup (shortO a b))) :
    ((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K) ≠ 0 := by
  rw [VeluDescent.coeff_pis, SubmonoidClass.coe_finsetProd]
  exact Finset.prod_ne_zero_iff.2 fun h hh => fun e => Finset.ne_of_mem_erase hh (Subtype.ext e)

end Lie

/-! ### The quotient model -/

section Model
variable [CompleteSpace K] [IsAlgClosed K] [CharZero K] [DecidableEq K]

/-- **Quotient model for every order-`p` subgroup** (canonical or not). -/
theorem model_of_finSub (a b : 𝒪) (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (C : Lubin.FinSub (formalGroup (shortO a b))) (hcard : C.H.card = p)
    (κ : Velu.Kernel (a : K) (b : K))
    (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (C.H : Set 𝒪)) :
    ∃ (A'' B'' : 𝒪) (ψ : MvPowerSeries Unit 𝒪),
      toK (shortO A'' B'') = ((⟨Units.mk0 _ (lie_pis_ne_zero C), 0, 0, 0⟩ :
        WeierstrassCurve.VariableChange K) • (κ.curve : WeierstrassCurve K)) ∧
      ‖(((shortO A'' B'').Δ : 𝒪) : K)‖ = 1 ∧
      Hom (formalGroup (shortO A'' B'')) (Lubin.quot C) ψ ∧
      coeff (Finsupp.single () 1) ψ = 1 := by
  have hu := HeightEll.topc_norm_eq_one (shortO a b) p hp5 hp1 hΔ ha
  obtain ⟨huG, haG⟩ := quot_height (formalGroup (shortO a b)) p hu ha hp1 C hcard
  have h2n : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3n : ‖(3 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0 := by
    intro h0
    have e : (((shortO a b).Δ : 𝒪) : K) = -16 * (4 * (a : K) ^ 3 + 27 * (b : K) ^ 2) := by
      have := congrArg (fun W : WeierstrassCurve K => W.Δ) (toK_shortO (K := K) a b)
      simp only [toK, WeierstrassCurve.map_Δ] at this
      rw [Subring.subtype_apply] at this
      rw [this, Velu.short_Δ]
    rw [e, h0, mul_zero, norm_zero] at hΔ
    exact zero_ne_one hΔ
  have hπ : Hom (formalGroup (shortO a b)) (Lubin.quot C) (Lubin.pis C) :=
    ⟨Lubin.cc_pis C, Lubin.pis_hom C⟩
  obtain ⟨θ, hθ⟩ := VeluDescent.exists_integral_descent a b C κ hκ (Lubin.quot C) hπ hΔ' h2n h3n
  exact exists_model_of_descent p hp5 hp1 a b κ (Lubin.quot C) huG haG (Lubin.pis C) hπ
    (lie_pis_ne_zero C) θ hθ

/-- **Vélu-normalized discriminant**: `‖Δ(E/C)‖ = ‖Lie π_C‖^12`. -/
theorem norm_Δ_velu (a b : 𝒪) (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (C : Lubin.FinSub (formalGroup (shortO a b))) (hcard : C.H.card = p)
    (κ : Velu.Kernel (a : K) (b : K))
    (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (C.H : Set 𝒪)) :
    ‖(κ.curve : WeierstrassCurve K).Δ‖ =
        ‖((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)‖ ^ 12 ∧
      ‖(SubgroupSum.veluC κ.G).Δ‖ =
        ‖((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)‖ ^ 12 := by
  obtain ⟨A'', B'', ψ, hK, hΔ'', -, -⟩ := model_of_finSub a b p hp5 hp1 hΔ ha C hcard κ hκ
  have e := congrArg (fun W : WeierstrassCurve K => ‖W.Δ‖) hK
  simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
  rw [hΔ'', EllipticI2.norm_Δ_scale, Units.val_mk0] at e
  set μ := ((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)
  have hμ : 0 < ‖μ‖ := norm_pos_iff.2 (lie_pis_ne_zero C)
  have h1 : ‖(κ.curve : WeierstrassCurve K).Δ‖ = ‖μ‖ ^ 12 := by
    rw [inv_pow] at e
    field_simp at e
    linarith
  refine ⟨h1, ?_⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [← SubgroupSum.Kernel.curve_eq_veluC h2 κ]
  exact h1

end Model

/-! ### Lie valuations -/

section Val
variable [CompleteSpace K] [IsAlgClosed K] [DecidableEq K]

/-- **non-canonical `C`**: `(∏_{c ∈ C∖0} ‖c‖)^p = ‖a‖`, i.e. `v(Lie π_C) = v/p`. -/
theorem prod_noncanonical (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse F p‖ ^ (p + 1))
    (C : Lubin.FinSub F) (hCp : ∀ c ∈ C.H, Lubin.pt (fun _ : Unit => c) (FGL.nmul F p) = 0)
    (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 → ‖hasse F p‖ * ‖(c : K)‖ ^ (p - 1) ≠ ‖(p : K)‖) :
    (∏ c ∈ C.H.erase 0, ‖(c : K)‖) ^ p = ‖hasse F p‖ := by
  have hp2 := hp.out.two_le
  have hα0 : 0 < ‖hasse F p‖ := alpha_pos (by omega) hε (norm_nonneg _) hbreak
  have hp1 : ‖(p : K)‖ < 1 := hp_lt_one (by omega) (norm_nonneg _) ha.le hε.le hbreak
  have hCbig : ∀ c ∈ C.H, c ≠ 0 → ‖(c : K)‖ ^ (p * (p - 1)) = ‖hasse F p‖ := by
    intro c hc hc0
    rcases (classify' F p hu ha hε hp1 hc0 (QuotientHasse.norm_lt_one_of_tn (C.tn c hc))
      (hCp c hc)).1 hbreak with h | h
    · exact absurd h (hCH c hc hc0)
    · exact h
  set P0 := ∏ c ∈ C.H.erase 0, ‖(c : K)‖ with hP0
  have hP0pos : 0 < P0 := Finset.prod_pos fun c hc => norm_pos_of_ne (Finset.ne_of_mem_erase hc)
  have h1 : (P0 ^ p) ^ (p - 1) = ‖hasse F p‖ ^ (p - 1) := by
    rw [← pow_mul, hP0, ← Finset.prod_pow, Finset.prod_congr rfl (fun c hc =>
      hCbig c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)), Finset.prod_const,
      Finset.card_erase_of_mem C.zero_mem, hcard]
  exact (pow_left_inj₀ (by positivity) hα0.le (by omega)).mp h1

/-- **canonical `C`**: `(∏_{c ∈ C∖0} ‖c‖)·‖a‖ = ‖p‖`, i.e. `v(Lie π_C) = 1 − v`. -/
theorem prod_canonical (F : FormalGroup 𝒪) (p : ℕ) [hp : Fact p.Prime]
    (C : Lubin.FinSub F) (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 → ‖hasse F p‖ * ‖(c : K)‖ ^ (p - 1) = ‖(p : K)‖) :
    (∏ c ∈ C.H.erase 0, ‖(c : K)‖) * ‖hasse F p‖ = ‖(p : K)‖ := by
  have hp2 := hp.out.two_le
  have h1 : ((∏ c ∈ C.H.erase 0, ‖(c : K)‖) * ‖hasse F p‖) ^ (p - 1) = ‖(p : K)‖ ^ (p - 1) := by
    rw [mul_pow, ← Finset.prod_pow]
    have : ‖hasse F p‖ ^ (p - 1) = ∏ _c ∈ C.H.erase 0, ‖hasse F p‖ := by
      rw [Finset.prod_const, Finset.card_erase_of_mem C.zero_mem, hcard]
    rw [this, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun c hc => (mul_comm _ _).trans
      (hCH c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc))),
      Finset.prod_const, Finset.card_erase_of_mem C.zero_mem, hcard]
  exact (pow_left_inj₀ (by positivity) (norm_nonneg _) (by omega)).mp h1

end Val

/-! ### The dual isogeny -/

section Dual
variable [CompleteSpace K]

/-- **the dual `π̌_C`**: `π̌_C ∘ π_C = [p]`, `π̌_C : F/C → F`, `‖Lie π̌_C‖·‖Lie π_C‖ = ‖p‖`. -/
theorem lie_dual (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (C : Lubin.FinSub F) (hCp : ∀ c ∈ C.H, Lubin.pt (fun _ : Unit => c) (FGL.nmul F p) = 0) :
    ∃ πd : MvPowerSeries Unit 𝒪,
      subst (fun _ : Unit => Lubin.pis C) πd = FGL.nmul F p ∧
      ‖((coeff (Finsupp.single () 1) πd : 𝒪) : K)‖ *
        ‖((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)‖ = ‖(p : K)‖ := by
  obtain ⟨πd, hπd, -⟩ := Lubin.exists_dual C p hCp
  refine ⟨πd, hπd, ?_⟩
  have hπd0 : constantCoeff πd = 0 := by
    have := congrArg constantCoeff hπd
    rwa [FGL.cc_subst _ (fun _ => Lubin.cc_pis C), FGL.cc_nmul] at this
  have hl := congrArg (coeff (Finsupp.single () 1)) hπd
  rw [lin_sb hπd0 (Lubin.cc_pis C), FGL.coeff_one_nmul] at hl
  have hl' := congrArg (fun x : 𝒪 => ‖(x : K)‖) hl
  simp only [Subring.coe_mul, norm_mul, Subring.coe_natCast] at hl'
  exact hl'

end Dual

end AllQuotients
