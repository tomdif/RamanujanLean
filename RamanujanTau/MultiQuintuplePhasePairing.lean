import RamanujanTau.MultiQuintupleDualCompression
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cancellation forces opposite-phase balance without a shell-size bound

At a primitive prime-order root, a vanishing integer coefficient sum has
constant coefficients. If one coefficient is zero, they must all be zero.
For a complete Watson shell the compressed antipodal law is
`E(-w) = 3*p - E(w)`. It balances the zero and half-turn phase buckets.
Consequently, after regrouping opposite phases, cancellation forces every
bucket to balance. There is no weight restriction.

This establishes phase multiplicity balance, not that vector partners are
unique or that one linear isometry realizes the pairings on all shells.
-/

namespace Ramanujan.MultiQuintuple

/-- One zero coefficient eliminates the constant cyclotomic relation at
prime order. No sparsity or weight bound is required. -/
theorem prime_phase_sum_zero_iff_coefficients_zero
    {K : Type*} [Field K] [CharZero K] {p : ℕ} (hp : p.Prime)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (a : Fin p → ℤ) (j : Fin p) (hj : a j = 0) :
    (∑ i, (a i : K) * zeta ^ i.val) = 0 ↔ ∀ i, a i = 0 := by
  rw [hzeta.sum_eq_zero_iff_forall_eq_int hp]
  constructor
  · intro h i
    exact (h i j).trans hj
  · intro h i k
    rw [h i, h k]

/-- In opposite-phase coordinates, equal multiplicities in one bucket
force equal multiplicities everywhere whenever the whole sum cancels. -/
theorem prime_phase_sum_zero_iff_bucket_balance
    {K : Type*} [Field K] [CharZero K] {p : ℕ} (hp : p.Prime)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (positive negative : Fin p → ℕ) (j : Fin p)
    (hj : positive j = negative j) :
    (∑ i, ((positive i : K) - negative i) * zeta ^ i.val) = 0 ↔
      ∀ i, positive i = negative i := by
  have h := prime_phase_sum_zero_iff_coefficients_zero hp hzeta
    (fun i => (positive i : ℤ) - negative i) j (by simp [hj])
  simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Nat.cast_inj] using h

/-- A phase multiplicity in a finite shell. -/
noncomputable def shellPhaseMultiplicity {I G : Type*} [Fintype I]
    (phase : I → G) (a : G) : ℕ := by
  classical
  exact Fintype.card {i // phase i = a}

/-- The twisted antipodal law balances the zero and half-turn buckets.
The equivalence may be the vector antipode, but involutivity is not needed. -/
theorem antipodal_zero_bucket_balance {I G : Type*} [Fintype I] [AddGroup G]
    (phase : I → G) (antipode : I ≃ I) (halfTurn : G)
    (hphase : ∀ i, phase (antipode i) = halfTurn - phase i) :
    shellPhaseMultiplicity phase 0 = shellPhaseMultiplicity phase halfTurn := by
  classical
  apply Fintype.card_congr
  exact antipode.subtypeEquiv (fun i => by rw [hphase]; simp)

/-- The full multiplicity statement for compressed Watson phases, indexed
as the even phases `2*j` and their opposites `2*j+p` modulo `2*p`.
The sum here is already regrouped at a primitive p-th root. -/
theorem antipodal_shell_sum_zero_iff_pair_balance
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    {p : ℕ} (hp : p.Prime) {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (phase : I → ZMod (2 * p)) (antipode : I ≃ I)
    (hphase : ∀ i, phase (antipode i) = (p : ZMod (2 * p)) - phase i) :
    (∑ j : Fin p,
      ((shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) : K) -
        shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p)) *
          zeta ^ j.val) = 0 ↔
      ∀ j : Fin p,
        shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) =
          shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p) := by
  apply prime_phase_sum_zero_iff_bucket_balance hp hzeta _ _ ⟨0, hp.pos⟩
  simpa using antipodal_zero_bucket_balance phase antipode (p : ZMod (2 * p)) hphase

/-- The same result for actual powers of a `2*p`-th root. The two summands
are the contributions of phases `2*j` and `2*j+p`. For odd p these exhaust
all phase classes. The factorization into prime-order coefficients is proved
here, rather than supplied as a hypothesis. -/
theorem antipodal_shell_amplitude_zero_iff_pair_balance
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    {p : ℕ} (hp : p.Prime) {rho : K}
    (hrho : rho ^ p = -1) (hprimitive : IsPrimitiveRoot (rho ^ 2) p)
    (phase : I → ZMod (2 * p)) (antipode : I ≃ I)
    (hphase : ∀ i, phase (antipode i) = (p : ZMod (2 * p)) - phase i) :
    (∑ j : Fin p,
      ((shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) : K) *
          rho ^ (2 * j.val) +
        shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p) *
          rho ^ (2 * j.val + p))) = 0 ↔
      ∀ j : Fin p,
        shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) =
          shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p) := by
  have hfactor :
      (∑ j : Fin p,
        ((shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) : K) *
            rho ^ (2 * j.val) +
          shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p) *
            rho ^ (2 * j.val + p))) =
      ∑ j : Fin p,
        ((shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p))) : K) -
          shellPhaseMultiplicity phase (2 * (j.val : ZMod (2 * p)) + p)) *
            (rho ^ 2) ^ j.val := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, hrho, pow_mul]
    ring
  rw [hfactor]
  exact antipodal_shell_sum_zero_iff_pair_balance hp hprimitive phase antipode hphase

end Ramanujan.MultiQuintuple
