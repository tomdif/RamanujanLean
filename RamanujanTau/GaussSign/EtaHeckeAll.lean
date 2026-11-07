import RamanujanTau.GaussSign.Landsberg
import RamanujanTau.HalfHecke.EtaHecke

/-!
# Gauss's sign of the quadratic Gauss sum, and `EtaHecke Q k 1` for every prime `Q ≥ 5`

* `gQ_eq_sum_sq`: `gQ Q = Σ_{r mod Q} e(r²/Q)`.
* `gQ_eval`: **`gQ Q = √Q` if `Q ≡ 1 (mod 4)`, `gQ Q = i√Q` if `Q ≡ 3 (mod 4)`**
  (from `gaussQuad_eval`, the theta-function proof).
* `gaussSign_of_even`: the hypothesis `HalfHecke.GaussSign Q k` holds for every prime `Q ≥ 5`
  and every even `k`. (For odd `k` and `Q ≡ 3 (mod 4)` it is false as stated, but then
  `S_k(SL₂ℤ) = 0`.)
* `etaHecke_all`: **`EtaHecke Q k 1` for every prime `Q ≥ 5` and every `k ≥ 2`.**
-/

set_option autoImplicit false

namespace RamanujanTau.GaussSign
open Complex Finset ZMod
open RamanujanTau.HalfHecke RamanujanTau.ThetaLift RamanujanTau.AtkinSporadic
open MockTheta5.JTP (partitionGF)
open scoped Real

noncomputable section

variable (Q : ℕ) [hQ : Fact Q.Prime]

/-- `Σ_r ψ(r²) = Σ_x (1 + χ(x)) ψ(x) = g(χ, ψ)`. -/
theorem gQ_eq_sum_sq (h3 : 3 ≤ Q) : gQ Q = ∑ r : ZMod Q, (stdAddChar (r ^ 2) : ℂ) := by
  have hc : ringChar (ZMod Q) ≠ 2 := two_ne_Q Q h3
  rw [← Finset.sum_fiberwise' Finset.univ (fun r : ZMod Q => r ^ 2) (fun x => (stdAddChar x : ℂ))]
  have hcard : ∀ x : ZMod Q, ∑ r ∈ Finset.univ.filter (fun r : ZMod Q => r ^ 2 = x),
      (stdAddChar x : ℂ) = (chiQ Q x + 1) * stdAddChar x := by
    intro x
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have := quadraticChar_card_sqrts hc x
    rw [Set.toFinset_setOf] at this
    rw [chiQ_apply]
    exact_mod_cast this
  simp only [hcard, add_mul, one_mul, Finset.sum_add_distrib]
  have hne : (stdAddChar : AddChar (ZMod Q) ℂ) ≠ 1 := by
    intro h
    have h1 := congrArg (fun ψ : AddChar (ZMod Q) ℂ => ψ 1) h
    simp only [AddChar.one_apply] at h1
    rw [← (stdAddChar : AddChar (ZMod Q) ℂ).map_zero_eq_one] at h1
    have := injective_stdAddChar h1
    exact one_ne_zero this
  rw [AddChar.sum_eq_zero_of_ne_one hne, add_zero, gQ, gaussSum]

/-- **Gauss's sign.** `gQ Q = √Q` if `Q ≡ 1 (mod 4)`, `i√Q` otherwise (`Q` an odd prime). -/
theorem gQ_eval (h3 : 3 ≤ Q) :
    gQ Q = if Q % 4 = 1 then ((Real.sqrt Q : ℝ) : ℂ) else I * ((Real.sqrt Q : ℝ) : ℂ) := by
  rw [gQ_eq_sum_sq Q h3]
  haveI : NeZero Q := ⟨hQ.out.ne_zero⟩
  exact gaussQuad_eval Q (hQ.out.odd_of_ne_two (by omega))

lemma e24_zero' : e24 0 = 1 := by simp [e24]

lemma e24_eighteen : e24 18 = -I := by
  rw [show (18 : ℤ) = 12 + 6 by norm_num, e24_add, e24_twelve, e24_six]; ring

/-- The unit `ε` with `gQ Q = ε √Q`. -/
def epsQ : ℂ := if Q % 4 = 1 then 1 else I

lemma gQ_eq_eps (h3 : 3 ≤ Q) : gQ Q = epsQ Q * ((Real.sqrt Q : ℝ) : ℂ) := by
  rw [gQ_eval Q h3, epsQ]; split_ifs <;> simp

/-- `(2/Q) · e((Q−1)/8) · ε = 1`. -/
lemma key_sign (hQ5 : 5 ≤ Q) :
    ((legendreSym Q 2 : ℤ) : ℂ) * e24 (3 * (Q : ℤ) - 3) * epsQ Q = 1 := by
  have hodd : Q % 2 = 1 := Nat.odd_iff.mp (hQ.out.odd_of_ne_two (by omega))
  rw [legendreSym.at_two (by omega), χ₈_nat_eq_if_mod_eight, if_neg (by omega), epsQ]
  rcases (by omega : Q % 8 = 1 ∨ Q % 8 = 3 ∨ Q % 8 = 5 ∨ Q % 8 = 7) with h | h | h | h
  · rw [if_pos (by omega), if_pos (by omega), e24_eq_of_dvd (b := 0) (by omega), e24_zero']
    simp
  · rw [if_neg (by omega), if_neg (by omega), e24_eq_of_dvd (b := 6) (by omega), e24_six]
    push_cast; linear_combination (-1 : ℂ) * I_sq
  · rw [if_neg (by omega), if_pos (by omega), e24_eq_of_dvd (b := 12) (by omega), e24_twelve]
    push_cast; ring
  · rw [if_pos (by omega), if_neg (by omega), e24_eq_of_dvd (b := 18) (by omega), e24_eighteen]
    push_cast; linear_combination (-1 : ℂ) * I_sq

/-- **The hypothesis `GaussSign Q k` holds for every prime `Q ≥ 5` and every even `k ≥ 2`.** -/
theorem gaussSign_of_even (hQ5 : 5 ≤ Q) (k : ℕ) (hk2 : 2 ≤ k) (hk : Even k) : GaussSign Q k := by
  unfold GaussSign cMd
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hchi : chiQ Q (-24) = ((legendreSym Q (-1) * legendreSym Q 2 * legendreSym Q 12 : ℤ) : ℂ) := by
    rw [show (-24 : ZMod Q) = ((-1 * 2 * 12 : ℤ) : ZMod Q) by push_cast; ring, chiQ_intCast,
      legendreSym.mul, legendreSym.mul]
  have hhs : heckeSign Q (k - 1) = legendreSym Q 12 * legendreSym Q (-1) := by
    rw [heckeSign, Odd.neg_one_pow (Nat.Even.sub_odd (by omega) hk odd_one)]
  have hz : (Q : ℂ) ^ ((k : ℤ) - 3) * Q = (Q : ℂ) ^ (k - 2) := by
    rw [← zpow_add_one₀ hQ0, ← zpow_natCast]
    congr 1; push_cast [Nat.cast_sub hk2]; ring
  have hs : ((Real.sqrt Q : ℝ) : ℂ) * ((Real.sqrt Q : ℝ) : ℂ) = Q := by
    rw [← ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hkey := key_sign Q hQ5
  rw [gQ_eq_eps Q (by omega), hchi, hhs]
  push_cast
  linear_combination ((Q : ℂ) ^ ((k : ℤ) - 3) * (legendreSym Q (-1) : ℂ) * (legendreSym Q 12 : ℂ) *
      (legendreSym Q 2 : ℂ) * e24 (3 * (Q : ℤ) - 3) * epsQ Q) * hs +
    ((Q : ℂ) ^ ((k : ℤ) - 3) * Q * (legendreSym Q (-1) : ℂ) * (legendreSym Q 12 : ℂ)) * hkey +
    ((legendreSym Q (-1) : ℂ) * (legendreSym Q 12 : ℂ)) * hz

/-- **`T(Q²)` preserves `η^{−1} S_k(SL₂ℤ)` (integral q-expansions) for every prime `Q ≥ 5` and
every `k ≥ 2`**, unconditionally. Even `k`: `etaHecke_of_sign` + `gaussSign_of_even`.
Odd `k`: level-one forms of odd weight vanish. -/
theorem etaHecke_all (hQ5 : 5 ≤ Q) (k : ℕ) (hk : 2 ≤ k) : EtaHecke Q k 1 := by
  rcases Nat.even_or_odd k with he | ho
  · exact etaHecke_of_sign Q hQ5 k hk (gaussSign_of_even Q hQ5 k hk he)
  · intro a ha ha0
    obtain ⟨F, hF⟩ := ha
    have hF0 : F = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho) F
    have ha' : a = 0 := by
      apply BoylanWebb.map_injC
      rw [← hF, hF0, map_zero, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    refine ⟨a, ⟨F, hF⟩, ha0, ?_⟩
    subst ha'
    ext n
    simp [coeff_heckeHalf]

end

end RamanujanTau.GaussSign
