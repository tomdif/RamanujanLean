import RamanujanTau.TheoremA.BinaryFiltrationCycle
import RamanujanTau.TheoremA.ModularWeightSixIdentity
import RamanujanTau.TheoremA.Signs

/-!
# Ordinarity on the specified sign eigenspace of the level-six model

For every prime p≥13, a nonzero series represented in weight p−3 and with
the two prescribed bad-prime eigenvalues cannot be killed by U_p.
The filtration laws, weight-six comparison, and operator obstruction are
all proved. Identifying actual newforms and the half-integral-weight space
with this sign eigenspace remains separate from this theorem.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA

/-- Universal injectivity on the stated bad-prime sign eigenspace of the binary model. -/
theorem U_ne_zero_of_binary_sign_eigenvalues (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    {F : Type*} [Field F] [CharP F p] (f : PowerSeries F)
    (hf : BinaryRep f ((p - 3) / 2)) (hf0 : f ≠ 0)
    (hU2 : BoylanWebb.U 2 f =
      ((legendreSym p 2 : F) * (2 : F) ^ ((p - 5) / 2)) • f)
    (hU3 : BoylanWebb.U 3 f =
      ((legendreSym p 3 : F) * (3 : F) ^ ((p - 5) / 2)) • f) :
    BoylanWebb.U p f ≠ 0 := by
  intro hu
  have h6 := theta_four_binaryRep hp13 f hf hf0 hu
  have h2 : uOperator 2 ((theta ^ 4) f) = (4 : F) • ((theta ^ 4) f) := by
    rw [uOperator_apply, U_theta_pow, hU2, map_smul, smul_smul]
    have h := theta_four_eigenvalue p (by omega) F 2
    norm_num at h ⊢
    rw [h]
  have h3 : uOperator 3 ((theta ^ 4) f) = (9 : F) • ((theta ^ 4) f) := by
    rw [uOperator_apply, U_theta_pow, hU3, map_smul, smul_smul]
    have h := theta_four_eigenvalue p (by omega) F 3
    norm_num at h ⊢
    rw [h]
  exact theta_pow_ne_zero_of_closed_cycle f hf0 hu (by omega : 4 ≤ p - 1)
    (eq_zero_of_binary_weightSix_eigenpair hp13 _ h6 h2 h3)

end RamanujanTau.TheoremA
