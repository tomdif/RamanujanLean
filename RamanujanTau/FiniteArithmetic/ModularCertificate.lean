import RamanujanTau.BoylanWebb.Assemble

/-!
# Finite certificates for modular operator images

Unlike `BoylanWebb.assemble`, this checker allows distinct source and target
forms and uses the actual Sturm bound at any weight. A Hasse lift aligns the
weights. The checked list equality therefore determines every coefficient of
the operator image, not just the supplied prefix.
-/

set_option autoImplicit false

namespace BoylanWebb
open PowerSeries RamanujanTau

lemma Cg.add {p d : ℕ} {a b a' b' : PowerSeries ℤ}
    (ha : Cg p d a a') (hb : Cg p d b b') : Cg p d (a + b) (a' + b') := by
  unfold Cg at *
  rw [map_add, map_add, show Ψ p a + Ψ p b - (Ψ p a' + Ψ p b') =
    (Ψ p a - Ψ p a') + (Ψ p b - Ψ p b') by ring]
  exact dvd_add ha hb

lemma Cg_linear_combination {p d : ℕ} {a b : PowerSeries ℤ} {la lb : List ℤ}
    (ha : Cg p d a (toPS la)) (hb : Cg p d b (toPS lb)) (c e : ℤ) :
    Cg p d (C c * a + C e * b)
      (toPS (red p (addList (scaleList c la) (scaleList e lb)))) := by
  refine (((Cg.refl (C c)).mul ha).add ((Cg.refl (C e)).mul hb)).trans ?_
  rw [← toPS_scaleList, ← toPS_scaleList, ← toPS_addList]
  exact (Cg_red _).symm

end BoylanWebb

namespace RamanujanTau.FiniteArithmetic
open PowerSeries BoylanWebb

/-- Certify `U a = c b` modulo a prime from finite lists. The source is cuspidal
of weight `e+1`; multiplying the target by a Hasse lift aligns its weight
without changing its reduction. -/
theorem U_eq_of_certificate (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : ℕ) (he : 1 ≤ e) (w : ℤ) (m : ℕ)
    (hw : w + (m : ℤ) * ((p - 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ))
    (a b : PowerSeries ℤ) (ha : IntForm ((e + 1 : ℕ) : ℤ) a)
    (ha0 : coeff 0 a = 0) (hb : IntForm w b)
    (d : ℕ) (hd : p * ((e + 1) / 12) ≤ d)
    (la lb : List ℤ) (hca : Cg p d a (toPS la)) (hcb : Cg p d b (toPS lb))
    (c : ℤ)
    (check : ∀ n, n < (e + 1) / 12 + 1 →
      (coeffList la (p * n) - c * coeffList lb n) % (p : ℤ) = 0) :
    U p (Ψ p a) = C (c : ZMod p) * Ψ p b := by
  obtain ⟨A, hA, hAe⟩ := exists_hasse_lift p hp
  have htarget : Ψ p (C c * (b * A ^ m)) = C (c : ZMod p) * Ψ p b := by
    rw [map_mul, map_mul, map_pow, hAe, one_pow, mul_one, PowerSeries.map_C]
    rfl
  have h := U_eq_of_sturm p e he a (C c * (b * A ^ m)) ha ha0
    (((hb.mul (hA.pow m)).C_mul c).cast hw) (fun n hn => by
      rw [htarget, coeff_C_mul]
      exact coeff_of_chk p hca hcb c _ hd check n hn)
  exact h.trans htarget

end RamanujanTau.FiniteArithmetic
