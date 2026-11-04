import RamanujanTau.AtkinTwisted.Group1
import RamanujanTau.AtkinTwisted.Group2
import RamanujanTau.AtkinTwisted.Group3
import RamanujanTau.AtkinTwisted.Group4

/-!
# Atkin's twisted class modulo 13: every prime `5 ≤ Q < 500`

`eigen_all`: for **every** prime `5 ≤ Q < 500`, `Q ≠ 13`, the twisted series
`F̄ = Σ_{((24N−1)/13) = −1} p(N) qᴺ (mod 13)` is a `T(Q²)`-eigenform. The eigenvalue list is
`allPairs`; the congruence families (Atkin type and Ono type) are in `Group1`–`Group4`.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinTwisted
open PowerSeries BoylanWebb RamanujanTau.AtkinSporadic
open Twist13

/-- All certified pairs `(Q, μ)`. -/
def allPairs : List (ℕ × ZMod 13) := G1.pairs ++ G2.pairs ++ G3.pairs ++ G4.pairs

/-- Every prime `5 ≤ Q < 500`, `Q ≠ 13`, occurs in `allPairs`. -/
theorem allPairs_cover : (List.range 500).all (fun Q => !decide (Nat.Prime Q) || decide (Q < 5) ||
    Q == 13 || allPairs.any (fun p => p.1 == Q)) = true := by
  decide +kernel

theorem eigen_of_mem (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) (μ : ZMod 13) (hmem : (Q, μ) ∈ allPairs) :
    TT Q = C μ * Ψ 13 twPGF := by
  simp only [allPairs, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact G1.eigen Q hQ5 μ h
  · exact G2.eigen Q hQ5 μ h
  · exact G3.eigen Q hQ5 μ h
  · exact G4.eigen Q hQ5 μ h

/-- **`F̄` is a `T(Q²)`-eigenform modulo 13 for every prime `5 ≤ Q < 500`, `Q ≠ 13`.** -/
theorem eigen_all (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q) (hQ500 : Q < 500) (hQ13 : Q ≠ 13) :
    ∃ μ : ZMod 13, TT Q = C μ * Ψ 13 twPGF := by
  have h := List.all_eq_true.mp allPairs_cover Q (List.mem_range.mpr hQ500)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at h
  rcases h with ((h | h) | h) | ⟨p, hp, hpQ⟩
  · exact absurd hQ.out h
  · omega
  · exact absurd h hQ13
  · obtain ⟨Q', μ⟩ := p
    simp only at hpQ
    subst hpQ
    exact ⟨μ, eigen_of_mem Q' hQ5 μ hp⟩

end RamanujanTau.AtkinTwisted
