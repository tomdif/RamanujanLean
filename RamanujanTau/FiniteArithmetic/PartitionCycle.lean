import RamanujanTau.FiniteArithmetic.Orbit
import RamanujanTau.BoylanWebb.Assemble

/-!
# Actual partition orbits from a finite modular cycle

The two parity classes may occupy different lines. Three identities of full
power series construct a one-state `OrbitModel` for the odd subsequence and
give a partition-count recurrence for both parities. The modular certificate
checker can supply these identities from finite lists.
-/

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic
open PowerSeries BoylanWebb

variable (p : ℕ) [Fact p.Prime]

/-- Coefficient decimation as a linear operator. -/
noncomputable def decimate : Module.End (ZMod p) (PowerSeries (ZMod p)) where
  toFun := U p
  map_add' := U_add p
  map_smul' := by
    intro a f
    simp only [RingHom.id_apply, PowerSeries.smul_eq_C_mul, U_C_mul]

/-- The genuine odd-to-odd partition operator modulo `p`: `D ∘ U`. -/
noncomputable def partitionStep : Module.End (ZMod p) (PowerSeries (ZMod p)) :=
  (decimate p).comp ((LinearMap.mulLeft (ZMod p) (Ψ p (Dz ^ δ p))).comp (decimate p))

lemma odd_iterates (h24 : 24 * δ p + 1 = p ^ 2) (n : ℕ) :
    Ψ p (L p (2 * n + 1)) = (partitionStep p ^ n) (Ψ p (L p 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega, L_succ,
      Ψ_T_even p h24 _ (by convert even_2b (n + 1) using 1),
      show 2 * n + 2 = (2 * n + 1) + 1 by omega, L_succ,
      Ψ_T_odd p _ (not_even_2b1 n), ih, pow_succ', Module.End.mul_apply]
    rfl

variable (f g : PowerSeries (ZMod p)) (c k : ZMod p)

/-- The finite representation is tied to full arithmetic series by `h1`
and `h2`; they are not finite-prefix assumptions. The initial identification
is supplied by `h0` in `partition_cycle_values`. -/
noncomputable def partitionCycleModel
    (h1 : U p f = g) (h2 : U p (Ψ p (Dz ^ δ p) * g) = C k * f) :
    OrbitModel (partitionStep p) (c • f) :=
  eigenlineModel (partitionStep p) f c k (by
    change U p (Ψ p (Dz ^ δ p) * U p f) = k • f
    rw [h1, h2, PowerSeries.smul_eq_C_mul])

/-- Both parity classes are scalar orbits, though their basis series may differ. -/
theorem partition_cycle_values (h24 : 24 * δ p + 1 = p ^ 2)
    (h0 : U p (Ψ p (Dz ^ δ p)) = C c * f)
    (h1 : U p f = g) (h2 : U p (Ψ p (Dz ^ δ p) * g) = C k * f) (n : ℕ) :
    Ψ p (L p (2 * n + 1)) = C (c * k ^ n) * f ∧
      Ψ p (L p (2 * n + 2)) = C (c * k ^ n) * g := by
  have hseed : Ψ p (L p 1) = c • f := by
    rw [show 1 = 0 + 1 from rfl, L_succ, Ψ_T_even p h24 0 (even_2b 0)]
    simpa only [show L p 0 = 1 from rfl, map_one, mul_one,
      PowerSeries.smul_eq_C_mul] using h0
  have horbit : (partitionStep p ^ n) (c • f) = (c * k ^ n) • f := by
    have h := (partitionCycleModel p f g c k h1 h2).realizes n
    have hcoords : ∀ j : ℕ,
        ((partitionCycleModel p f g c k h1 h2).transition ^ j)
          (fun _ => c) = fun _ => c * k ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        ext i
        change k * (c * k ^ j) = c * k ^ (j + 1)
        ring
    change (partitionStep p ^ n) (c • f) =
      (eigenlineModel (partitionStep p) f c k _).synthesize
        (((partitionCycleModel p f g c k h1 h2).transition ^ n) (fun _ => c)) at h
    rw [hcoords] at h
    exact h
  have ho : Ψ p (L p (2 * n + 1)) = C (c * k ^ n) * f := by
    rw [odd_iterates p h24, hseed, horbit, PowerSeries.smul_eq_C_mul]
  refine ⟨ho, ?_⟩
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, L_succ,
    Ψ_T_odd p _ (not_even_2b1 n), ho, U_C_mul, h1]

/-- A full-series two-step relation from the finite representation. -/
theorem partition_cycle_two_step (h24 : 24 * δ p + 1 = p ^ 2)
    (h0 : U p (Ψ p (Dz ^ δ p)) = C c * f)
    (h1 : U p f = g) (h2 : U p (Ψ p (Dz ^ δ p) * g) = C k * f)
    (b : ℕ) (hb : 1 ≤ b) :
    Ψ p (L p (b + 2)) = C k * Ψ p (L p b) := by
  have H := partition_cycle_values p f g c k h24 h0 h1 h2
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' b
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [(H (i + 1)).2, show 2 * (i + 1) = 2 * i + 2 by omega, (H i).2,
      ← mul_assoc, ← map_mul]
    congr 2
    ring
  · rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega,
      (H (j + 1)).1, (H j).1, ← mul_assoc, ← map_mul]
    congr 2
    ring

end RamanujanTau.FiniteArithmetic
