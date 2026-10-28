/-
# (UB) in shifted form, and (UB) from formal-group models

* `UB_shift`: `gnorm b ≤ ‖p‖^e` gives `‖(a_i)_d‖ ≤ ‖p‖^{e + u(i,j)}`. This is the norm form of the
  hypothesis `hUB` of `AtkinOBrien.U_maps` ("`ϖ^e ∣ x ⇒ ϖ^{e+u(i,j)} ∣ U_{ij} x`").
* `UB_of_models`: `UB` with `QuotHyp` replaced by the formal-group data of `quotHyp_of_models`
  (non-canonical subgroups of `F_W[p]` + good-reduction quotient models with unit-Lie maps to
  Lubin's quotient), plus the ordinary-locus statement. The q-expansion principle for `U_p` (`hU`)
  remains a hypothesis.
-/
import RamanujanTau.UpContraction.Transport

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UpContraction
open KatzForms Igusa MvPolynomial Filter Topology CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime]

/-- **(UB), shifted**: if `‖b‖ ≤ ‖p‖^e` then `‖(a_i)_d‖ ≤ ‖p‖^{e + u(i,j)}`. Hypotheses as in `UB`. -/
theorem UB_shift [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(p : K)‖) (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p)
    (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K) (hQ : QuotHyp p (Eh φ hp5) Q)
    (e : ℕ) (j : ℕ) (bj : MvPolynomial (Fin 2) K) (hbj : gnorm bj ≤ ‖(p : K)‖ ^ e)
    (a : ℕ → MvPolynomial (Fin 2) K) (haB : ∀ i, a i ∈ katzPiece φ (Bz p hp5 0) i)
    (hrat : ∀ i d, ∃ (x : ℤ_[p]) (k : ℕ), (a i).coeff d = φ x / (p : K) ^ k)
    (hdec : ∀ s : K, ‖(p : K)‖ ^ p < ‖s‖ ^ (p + 1) → ‖s‖ < 1 →
      Tendsto (fun i => gnorm (a i) / ‖s‖ ^ i) atTop (𝓝 0))
    (hU : ∀ W, IsTest W → Brk p (Eh φ hp5) W →
      (p : K) * kval (Eh φ hp5) a (pt W) =
        ∑ c, eval (pt (Q W c)) bj / eval (pt (Q W c)) (Eh φ hp5) ^ j) :
    ∀ i d, ‖(a i).coeff d‖ ≤ ‖(p : K)‖ ^ ((e : ℤ) + AtkinOBrien.u p i j) := by
  intro i d
  have hp0 : (p : K) ≠ 0 := norm_pos_iff.mp hε
  set c : K := ((p : K) ^ e)⁻¹
  have hc : ‖c‖ = (‖(p : K)‖ ^ e)⁻¹ := by rw [norm_inv, norm_pow]
  have hpe : 0 < ‖(p : K)‖ ^ e := pow_pos hε e
  set b' := C c * bj
  set a' : ℕ → MvPolynomial (Fin 2) K := fun l => C c * a l
  have hb' : gnorm b' ≤ 1 := by
    refine (gnorm_C_mul_le c bj).trans ?_
    rw [hc, inv_mul_le_iff₀ hpe, mul_one]; exact hbj
  have haB' : ∀ l, a' l ∈ katzPiece φ (Bz p hp5 0) l := fun l => by
    simp only [a']; rw [C_mul']; exact Submodule.smul_mem _ _ (haB l)
  have hrat' : ∀ l d, ∃ (x : ℤ_[p]) (k : ℕ), (a' l).coeff d = φ x / (p : K) ^ k := by
    intro l d
    obtain ⟨x, k, hx⟩ := hrat l d
    refine ⟨x, k + e, ?_⟩
    simp only [a', coeff_C_mul, hx, c, pow_add]
    field_simp
  have hdec' : ∀ s : K, ‖(p : K)‖ ^ p < ‖s‖ ^ (p + 1) → ‖s‖ < 1 →
      Tendsto (fun l => gnorm (a' l) / ‖s‖ ^ l) atTop (𝓝 0) := by
    intro s hs hs1
    have h := (hdec s hs hs1).const_mul ‖c‖
    rw [mul_zero] at h
    refine squeeze_zero (fun l => div_nonneg (gnorm_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (fun l => ?_) h
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (gnorm_C_mul_le _ _) (pow_nonneg (norm_nonneg _) _)
  have hU' : ∀ W, IsTest W → Brk p (Eh φ hp5) W →
      (p : K) * kval (Eh φ hp5) a' (pt W) =
        ∑ c', eval (pt (Q W c')) b' / eval (pt (Q W c')) (Eh φ hp5) ^ j := by
    intro W hW hB
    have hl : kval (Eh φ hp5) a' (pt W) = c * kval (Eh φ hp5) a (pt W) := by
      simp only [kval, a', map_mul, eval_C]
      rw [← tsum_mul_left]
      congr 1; ext l; ring
    rw [hl, mul_left_comm, hU W hW hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [b', map_mul, eval_C]; ring
  have h := UB φ hφ hε hpK hp5 Q hQ j b' hb' a' haB' hrat' hdec' hU' i d
  simp only [a', coeff_C_mul, norm_mul, hc] at h
  rw [inv_mul_le_iff₀ hpe] at h
  rw [zpow_add₀ hε.ne', zpow_natCast]
  exact h

/-- **(UB) from formal-group models** (the remaining hypothesis on the geometry of `U` is `hU`). -/
theorem UB_of_models [CompleteSpace K] [IsAlgClosed K] [Algebra ℤ_[p] (integers K)]
    (φ : ℤ_[p] →+* K) (hφ : ∀ x, (((algebraMap ℤ_[p] (integers K) x) : integers K) : K) = φ x)
    (hε : 0 < ‖(p : K)‖) (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p)
    (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K)
    (hss : ∀ W, IsTest W → Brk p (Eh φ hp5) W → ‖eval (pt W) (Eh φ hp5)‖ < 1 → SSData p W (Q W))
    (hord : ∀ W, IsTest W → ‖eval (pt W) (Eh φ hp5)‖ = 1 → ∀ c,
      IsTest (Q W c) ∧ ‖eval (pt (Q W c)) (Eh φ hp5)‖ = 1)
    (e : ℕ) (j : ℕ) (bj : MvPolynomial (Fin 2) K) (hbj : gnorm bj ≤ ‖(p : K)‖ ^ e)
    (a : ℕ → MvPolynomial (Fin 2) K) (haB : ∀ i, a i ∈ katzPiece φ (Bz p hp5 0) i)
    (hrat : ∀ i d, ∃ (x : ℤ_[p]) (k : ℕ), (a i).coeff d = φ x / (p : K) ^ k)
    (hdec : ∀ s : K, ‖(p : K)‖ ^ p < ‖s‖ ^ (p + 1) → ‖s‖ < 1 →
      Tendsto (fun i => gnorm (a i) / ‖s‖ ^ i) atTop (𝓝 0))
    (hU : ∀ W, IsTest W → Brk p (Eh φ hp5) W →
      (p : K) * kval (Eh φ hp5) a (pt W) =
        ∑ c, eval (pt (Q W c)) bj / eval (pt (Q W c)) (Eh φ hp5) ^ j) :
    ∀ i d, ‖(a i).coeff d‖ ≤ ‖(p : K)‖ ^ ((e : ℤ) + AtkinOBrien.u p i j) := by
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x => by rw [← hφ x]; exact (algebraMap ℤ_[p] (integers K) x).2
  exact UB_shift φ hφ1 hε hpK hp5 Q (quotHyp_of_models φ hφ hp5 hε Q hss hord) e j bj hbj a haB hrat
    hdec hU

end UpContraction
