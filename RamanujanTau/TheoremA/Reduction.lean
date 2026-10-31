import RamanujanTau.TheoremA.Series
import RamanujanTau.TheoremA.Signs
import RamanujanTau.TheoremA.ThetaCycle
import RamanujanTau.TheoremA.WeightSix

/-!
# A conditional reduction of the ordinarity argument to modular-form inputs

The conclusion concerns the actual coefficient-extraction operator on an
actual power series. This early interface retains explicit
filtration laws and a weight-six Hecke relation. `WeightSixIdentity` proves
the latter on the actual classical cusp space; `LiftedOrdinarity` applies it
to coefficient reductions. `BinaryOrdinarity` subsequently proves the filtration laws and uses an obstruction
on the full weight-six modular space, removing the lifting input. The newform
sign and half-integral-weight comparisons still remain, so this is not full Theorem A.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries

/-- The polynomial expected to annihilate weight-six level-six cusp forms,
acting on the ambient space of all formal power series. It does not annihilate
that ambient space. -/
noncomputable def weightSixAnnihilator {K : Type*} [CommRing K] :
    Module.End K (PowerSeries K) :=
  (uOperator 3 + (9 : K) • 1) *
    (uOperator 2 ^ 2 + (6 : K) • uOperator 2 + (32 : K) • 1)

/-- Once the geometric filtration laws and weight-six operator identity have
been supplied, the proposed Atkin–Lehner eigenvalues force ordinarity.
The theorem works over arbitrary residue fields of characteristic `p`. -/
theorem U_ne_zero_of_filtration_data (p : ℕ) [Fact p.Prime] (hp : 13 ≤ p)
    {K : Type*} [Field K] [CharP K p] (f : PowerSeries K)
    (hf : coeff 1 f ≠ 0) (filtration : PowerSeries K → ℤ) (drop : ℕ → ℤ)
    (hstart : filtration f = (p : ℤ) - 3)
    (hweight : ∀ i ≤ p - 1, 0 ≤ filtration ((theta ^ i) f))
    (hdrop_nonneg : ∀ i < p - 1, 0 ≤ drop i)
    (hstep : ∀ i < p - 1, filtration ((theta ^ (i + 1)) f) =
      filtration ((theta ^ i) f) + p + 1 - drop i * (p - 1 : ℤ))
    (hdrop : ∀ i < p - 1, ¬ (p : ℤ) ∣ filtration ((theta ^ i) f) → drop i = 0)
    (hweightSix : ∀ i, filtration ((theta ^ i) f) = 6 →
      weightSixAnnihilator ((theta ^ i) f) = 0)
    (hU2 : BoylanWebb.U 2 f =
      ((legendreSym p 2 : K) * (2 : K) ^ ((p - 5) / 2)) • f)
    (hU3 : BoylanWebb.U 3 f =
      ((legendreSym p 3 : K) * (3 : K) ^ ((p - 5) / 2)) • f) :
    BoylanWebb.U p f ≠ 0 := by
  intro hu
  have hcycle := (U_eq_zero_iff_theta_cycle f).mp hu
  have hw6 : filtration ((theta ^ 4) f) = 6 :=
    theta_cycle_weight_six p hp (fun i => filtration ((theta ^ i) f)) drop
      hweight hdrop_nonneg hstep hdrop (by simpa using hstart) (by simp [hcycle])
  have h2 : uOperator 2 ((theta ^ 4) f) = (4 : K) • ((theta ^ 4) f) := by
    rw [uOperator_apply, U_theta_pow, hU2, map_smul, smul_smul]
    have h := theta_four_eigenvalue p (by omega) K 2
    norm_num at h ⊢
    rw [h]
  have h3 : uOperator 3 ((theta ^ 4) f) = (9 : K) • ((theta ^ 4) f) := by
    rw [uOperator_apply, U_theta_pow, hU3, map_smul, smul_smul]
    have h := theta_four_eigenvalue p (by omega) K 3
    norm_num at h ⊢
    rw [h]
  exact theta_pow_ne_zero f hf 4
    (eigenvector_eq_zero_of_annihilated (uOperator 2) (uOperator 3) ((theta ^ 4) f)
      (hweightSix 4 hw6) (obstruction_scalar_ne_zero p (by omega)) h2 h3)

end RamanujanTau.TheoremA
