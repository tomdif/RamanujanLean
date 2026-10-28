/-
# Buzzard 3.3 (ii)/(iv) in one inequality, including the boundary `v = 1/(p+1)`

**`hasse_quot_canonical_le`**: for the canonical quotient `G = F/C` (break region),
`‖a_G‖ · ‖a_F‖ ≤ max(‖a_F‖^{p+1}, ‖p‖)`, i.e. `v(a_G) ≥ min(p·v, 1 − v)`.

Off the boundary this is `QuotientHasse.hasse_quot_canonical` (ii)/(iv). At the boundary
`‖a_F‖^{p+1} = ‖p‖` we classify the image `π(y)` of a non-canonical torsion point: either `G` is in
its break region, and then `‖a_G‖ = ‖a_F‖^p`, or it is not, and then
`‖a_G‖^{p+1} ≤ ‖p‖^p = (‖a_F‖^p)^{p+1}`.
-/
import RamanujanTau.QuotientHasse.Main

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotE
open MvPowerSeries CanonicalIsogeny WeierstrassSupply Lubin QuotientHasse

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **`v(a_{F/H}) ≥ min(p v, 1 − v)`** for the canonical subgroup `H` (break region). -/
theorem hasse_quot_canonical_le [IsAlgClosed K] (F : FormalGroup ↥(integers K)) [F.IsComm]
    (p : ℕ) [hp : Fact p.Prime] (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hbreak : ‖(p : K)‖ ^ p < ‖hasse F p‖ ^ (p + 1))
    (C : FinSub F) (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 → ‖hasse F p‖ * ‖(c : K)‖ ^ (p - 1) = ‖(p : K)‖) :
    ‖hasse (quot C) p‖ * ‖hasse F p‖ ≤ max (‖hasse F p‖ ^ (p + 1)) ‖(p : K)‖ := by
  have hp2 := hp.out.two_le
  have hq := hasse_quot_canonical F p hu ha hε hbreak C hcard hCH
  set ε := ‖(p : K)‖ with hεd
  set α := ‖hasse F p‖ with hαd
  set αG := ‖hasse (quot C) p‖ with hαGd
  have hα0 : 0 < α := alpha_pos (by omega) hε (norm_nonneg _) hbreak
  rcases lt_trichotomy ε (α ^ (p + 1)) with hlt | heq | hgt
  · obtain ⟨h1, -⟩ := hq.2.2.1 hlt
    rw [h1, ← pow_succ]; exact le_max_left _ _
  · -- the boundary
    have hp1 : ε < 1 := hp_lt_one (by omega) (norm_nonneg _) ha.le hε.le hbreak
    obtain ⟨huG, haG⟩ := quot_height F p hu ha hp1 C hcard
    obtain ⟨-, ⟨yb, hyb0, hyb1, hybp, hybb⟩⟩ := torsion_exists F p hu ha hε hp1 hbreak
    obtain ⟨-, e2n, -⟩ := nat_aux p (by omega)
    rw [e2n] at hybb
    have hgt' : ∀ c ∈ C.H, c ≠ 0 → ‖(c : K)‖ < ‖(yb : K)‖ := fun c hc hc0 =>
      can_lt_big hα0 (norm_nonneg _) hbreak (hCH c hc hc0) hybb
    have hL := norm_pt_pis_of_gt C hyb1 hgt'
    rw [hcard] at hL
    have hne : pt (fun _ : Unit => yb) (pis C) ≠ 0 :=
      pt_pis_ne_zero C (by rw [hL]; exact pow_pos (norm_pos_iff.2 (fun h => hyb0
        (Subtype.ext (by simpa using h)))) _)
    have cl := classify' (quot C) p huG haG hε hp1 hne (pt_pis_lt_one C hyb1)
      (pt_nmul_quot C p hyb1 hybp)
    rw [hL] at cl
    set u := ‖(yb : K)‖
    have hq1 : (u ^ p) ^ (p - 1) = α := by rw [← pow_mul]; exact hybb
    have hq2 : (u ^ p) ^ (p * (p - 1)) = α ^ p := by
      rw [show α = u ^ (p * (p - 1)) from hybb.symm]; ring
    rw [hq1, hq2] at cl
    rw [← hεd, ← hαGd] at cl
    by_cases hbG : ε ^ p < αG ^ (p + 1)
    · rcases cl.1 hbG with h | h
      · rw [h]; exact le_max_right _ _
      · rw [← h, ← pow_succ]; exact le_max_left _ _
    · push Not at hbG
      have h1 : αG ^ (p + 1) ≤ (α ^ p) ^ (p + 1) := by
        rw [← pow_mul, mul_comm, pow_mul, ← heq]; exact hbG
      have h2 : αG ≤ α ^ p := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity)
        (by omega)).mp h1
      calc αG * α ≤ α ^ p * α := mul_le_mul_of_nonneg_right h2 hα0.le
        _ = α ^ (p + 1) := (pow_succ _ _).symm
        _ ≤ _ := le_max_left _ _
  · obtain ⟨h1, -⟩ := hq.2.2.2 hgt
    rw [h1]; exact le_max_right _ _

end QuotE
