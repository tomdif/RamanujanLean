/-
# Sign changes of Ramanujan's τ — headlines (see `docs/TAU_SIGN_CHANGES.md`)
-/
import RamanujanTau.TauSigns.Count

namespace RamanujanTau.TauSigns

/-- Headline 1: τ changes sign infinitely often. -/
example : ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ N ≤ n ∧ 0 < tau m ∧ tau n < 0 := tau_sign_changes

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.exists_Δ_iy_bdd
#print axioms RamanujanTau.TauSigns.not_eventually_signed
#print axioms RamanujanTau.TauSigns.tau_sign_changes
#print axioms RamanujanTau.TauSigns.hecke_partial_sum
#print axioms RamanujanTau.TauSigns.tau_sign_change_short_interval
#print axioms RamanujanTau.TauSigns.exists_signChange_between
#print axioms RamanujanTau.TauSigns.card_signChanges_ge
