import RamanujanTau.LehmerSmall.Congruences
import RamanujanTau.Congruences.Mod7
import RamanujanTau.Congruences.Mod5
import RamanujanTau.Congruences.Mod23

/-! # Discharging the congruence hypothesis classes `TauMod7`, `TauMod25`, `TauMod23`

* `TauMod7`  ← `LehmerSmall.tau_mod7_all` (Ramanujan's ODEs mod 7),
* `TauMod25` ← `LehmerSmall.tau_mod25_all` (Ramanujan's ODEs mod 25),
* `TauMod23` ← `TauCong.tau_mod23` (Wilton, via Frobenius + Euler pentagonal).

The `LehmerSmall` / `TauCong` statements are about `TauCong.tauPS n = [qⁿ] q(q;q)²⁴` and Mathlib's `σ k`;
the classes are about the computable `RamanujanTau.tau` and the hand-rolled `sigma3`, `sigma9`.
The bridges are `tau_eq_tauPS` and `sigma{3,9}_eq` below.

The proved statements are **stronger** than the classes: no coprimality hypothesis for mod 7 / mod 25
(`tau_mod7_unconditional`, `tau_mod25_unconditional`), and for mod 23 every `n` (not only primes) that is a
non-square mod 23 (`tau_mod23_unconditional`).
-/

set_option autoImplicit false

namespace RamanujanTau.Discharge
open RamanujanTau
open scoped ArithmeticFunction.sigma

lemma sigma3_eq (n : ℕ) : sigma3 n = ((σ 3 n : ℕ) : ℤ) := by
  rw [sigma3, ArithmeticFunction.sigma_apply]; push_cast; rfl

lemma sigma9_eq (n : ℕ) : sigma9 n = ((σ 9 n : ℕ) : ℤ) := by
  rw [sigma9, ArithmeticFunction.sigma_apply]; push_cast; rfl

/-- **Ramanujan mod 7, all `n ≥ 1`** (no coprimality condition). -/
theorem tau_mod7_unconditional {n : ℕ} (hn : 1 ≤ n) : τ n ≡ (n : ℤ) * sigma3 n [ZMOD 7] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 7).mp ?_
  rw [tau_eq_tauPS, sigma3_eq]
  have := LehmerSmall.tau_mod7_all (n := n) (by omega)
  push_cast; exact this

/-- **Ramanujan mod 25, all `n ≥ 1`** (no coprimality condition). -/
theorem tau_mod25_unconditional {n : ℕ} (hn : 1 ≤ n) : τ n ≡ (n : ℤ) * sigma9 n [ZMOD 25] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 25).mp ?_
  rw [tau_eq_tauPS, sigma9_eq]
  have := LehmerSmall.tau_mod25_all (n := n) (by omega)
  push_cast; exact this

instance tauMod7 : TauMod7 := ⟨fun hn _ => tau_mod7_unconditional hn⟩

instance tauMod25 : TauMod25 := ⟨fun hn _ => tau_mod25_unconditional hn⟩

/-- The non-squares of `ZMod 23` are exactly the residues `{5,7,10,11,14,15,17,19,20,21,22}`. -/
lemma nonsq23 : ∀ x : ZMod 23, ¬ IsSquare x →
    x.val ∈ ({5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22} : Finset ℕ) := by decide

/-- **Wilton mod 23, all `n`**: `23 ∣ τ(n)` whenever `n` is a non-square mod 23. -/
theorem tau_mod23_unconditional {n : ℕ} (h : ¬ IsSquare ((n : ZMod 23))) : τ n ≡ 0 [ZMOD 23] := by
  have hv := nonsq23 _ h
  rw [ZMod.val_natCast] at hv
  exact (Int.modEq_zero_iff_dvd).mpr (tau_mod23' hv)

instance tauMod23 : TauMod23 := ⟨fun _ _ h => tau_mod23_unconditional h⟩

end RamanujanTau.Discharge

#print axioms RamanujanTau.Discharge.tau_mod7_unconditional
#print axioms RamanujanTau.Discharge.tau_mod25_unconditional
#print axioms RamanujanTau.Discharge.tau_mod23_unconditional
#print axioms RamanujanTau.Discharge.tauMod7
#print axioms RamanujanTau.Discharge.tauMod25
#print axioms RamanujanTau.Discharge.tauMod23
