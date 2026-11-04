import RamanujanTau.StepanovAS.Main
import RamanujanTau.Stepanov.Salie
import RamanujanTau.WeilKloosterman.Assembly
import RamanujanTau.TauBound.Unconditional

/-! # Discharging the Kloosterman-sum hypotheses

The `τ`-bound track has named hypotheses `TauBound.KloostermanBound α`, `TauBound.PoincareFormula`,
`WeilKloosterman.{PrimeKlBound, SaliePrimeBound, WeilPrimeBound, LocalKlBound}`,
`KloostermanL.{StepanovKloosterman, StepanovKloostermanEventually}`.
`Stepanov.saliePrimeBound`, `StepanovAS.weilPrimeBound`, `StepanovAS.stepanovKloostermanEventually`,
`WeilKloosterman.poincareFormula` already prove the main ones; the τ-exponent corollaries
`tau_isBigO_{47_8,35_6,23_4}_unconditional` exist. What was missing, provided here:

* `stepanovKloosterman_unconditional` — the **uniform** Stepanov bound `|K_r(1,b;p)| ≤ 2 p^{r/2}` for all
  `r ≥ 1` (the hypothesis `KloostermanL.StepanovKloosterman`, previously without proof), from the eventual
  form plus amplification (`|α|, |β| ≤ √p`).
* `primeKlBound_half_unconditional`, `localKlBound_half_unconditional`,
  `kloostermanBound_half_unconditional` (`KloostermanBound (1/2 + δ)` for all `δ > 0`, i.e. Weil's bound
  for composite moduli up to `c^δ`), and `kloostermanBound_twoThirds_unconditional` (Salié).
-/

set_option autoImplicit false

namespace RamanujanTau.Discharge.Kloosterman
open RamanujanTau KloostermanL WeilKloosterman

/-- **Uniform Stepanov–Weil bound**: `‖K_r(1,b;p)‖ ≤ 2 p^{r/2}` for every prime `p`, `r ≥ 1`, `b ≠ 0`. -/
theorem stepanovKloosterman_unconditional : StepanovKloosterman := by
  refine ⟨2, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro r hr b hb
  obtain ⟨C, r₀, hC⟩ := StepanovAS.stepanovKloostermanEventually p hp b hb
  obtain ⟨α, β, -, hαβ, hK⟩ := klGF_eq_neg_pow_add p hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hamp := norm_add_le_two_sqrt_of_powSum_bound (α := α) (β := β) (C := C) hp0
    (by rw [hαβ]; push_cast; rfl) (max r₀ 1) (fun r hr => by
      have := hC r (le_of_max_le_left hr)
      rwa [hK r (le_of_max_le_right hr), norm_neg] at this)
  rw [hK r hr, norm_neg]
  calc ‖α ^ r + β ^ r‖ ≤ ‖α‖ ^ r + ‖β‖ ^ r := by
        rw [← norm_pow, ← norm_pow]; exact norm_add_le _ _
    _ ≤ Real.sqrt p ^ r + Real.sqrt p ^ r := by
        gcongr
        · exact hamp.1
        · exact hamp.2.1
    _ = 2 * Real.sqrt p ^ r := by ring

theorem primeKlBound_half_unconditional : PrimeKlBound (1 / 2) :=
  primeKlBound_half_of_weil StepanovAS.weilPrimeBound

theorem localKlBound_half_unconditional : ∃ C : ℝ, 1 ≤ C ∧ LocalKlBound (1 / 2) C :=
  localKlBound_half primeKlBound_half_unconditional

/-- **Weil's bound for all moduli** (up to `c^δ`): `|S(1,n;c)| ≤ A_δ c^{1/2+δ}`. -/
theorem kloostermanBound_half_unconditional (δ : ℝ) (hδ : 0 < δ) :
    TauBound.KloostermanBound (1 / 2 + δ) :=
  kloostermanBound_half_of_weil StepanovAS.weilPrimeBound δ hδ

theorem kloostermanBound_twoThirds_unconditional (δ : ℝ) (hδ : 0 < δ) :
    TauBound.KloostermanBound (2 / 3 + δ) :=
  kloostermanBound_twoThirds_of_salie Stepanov.saliePrimeBound δ hδ

end RamanujanTau.Discharge.Kloosterman

#print axioms RamanujanTau.Discharge.Kloosterman.stepanovKloosterman_unconditional
#print axioms RamanujanTau.Discharge.Kloosterman.primeKlBound_half_unconditional
#print axioms RamanujanTau.Discharge.Kloosterman.localKlBound_half_unconditional
#print axioms RamanujanTau.Discharge.Kloosterman.kloostermanBound_half_unconditional
#print axioms RamanujanTau.Discharge.Kloosterman.kloostermanBound_twoThirds_unconditional
#print axioms RamanujanTau.WeilKloosterman.poincareFormula
