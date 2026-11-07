/-
# Selberg's key lemma, seventh pass: `QuadOffHyp (1/300) 13` proved; off-diagonal clause unconditional

* `quadOffHyp : SelbergKey5.QuadOffHyp (1/300) 13` (level 1):
  `‖Σ'_p ∫_{T/2}^{3T} Fq‖ ≤ C T^{299/300} (abcd)^{13}` for `T ≥ 4`, all quadruples, `0 ≤ x ≤ 1`, `|v| ≤ 1`.
  Split `Σ'_p = Σ_{Near} + Σ'_{Nearᶜ}`:
  * Near (`near_bound`): `1 ≤ |ℓ| ≤ T^{1/100}`, `T^{399/400} < m ≤ T^{401/400}`; pointwise in `t`,
    regroup along lines `Pm − Qn = ℓ` (`near_sum_eq`), Abel summation (`abel_line`) against
    `lineSum` (`abs_lineSum_le`, i.e. `scs2_general`), weight derivative from `Wxi_bound`
    (`Hl_deriv`): `≪ (PQ)^{13} T^{1−11/2100}`.
  * Far (`far_bound`): termwise `term_integral_bound` (A = 3), `|ω| ≥ |ℓ|/max(Pm,Qn)`, and the
    Rankin–Selberg majorant (`far_pt_real`, `sum_box_Maj`): `≪ (PQ)^6 T^{299/300}`.
* `offLag_bound`: the off-diagonal clause of `SKSplitHyp'` for the window `φ_T`, for every
  `0 ≤ θ < 1/16800` (in particular `θ ≤ 1/81600`), unconditionally.
* `skSplitHyp'_of_diagHypT`: `DiagHypT θ ⟹ SKSplitHyp' θ`;
  `tauL_positive_proportion_of_SKQF'`: positive proportion on `QFHyp ∧ SKQFHyp θ ∧ DiagApproxHyp θ`
  (the `QuadOffHyp` hypothesis of `SelbergKeyDiag.tauL_positive_proportion_of_SKQF` is discharged).
-/
import RamanujanTau.SelbergKey7.NearBound
import RamanujanTau.SelbergKeyDiag.Assemble

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex Finset RamanujanTau.SelbergKey RamanujanTau.SelbergKey4 RamanujanTau.SelbergKey5
open scoped Real

/-- **`QuadOffHyp (1/300) 13`, unconditionally.** -/
theorem quadOffHyp : QuadOffHyp (1 / 300) 13 := by
  obtain ⟨KN, hKN0, hKN⟩ := near_bound
  obtain ⟨KF, hKF0, hKF⟩ := far_bound
  refine ⟨KN + KF, 4, by positivity, fun T hT q ha hb hc hd x v hx0 hx1 hv => ?_⟩
  obtain ⟨a, b, c, d⟩ := q
  simp only at ha hb hc hd ⊢
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set X : ℕ × ℕ → ℂ := fun p => ∫ t in (T / 2)..(3 * T), Fq T x v (a, b, c, d) p t
  have hs : Summable X := summable_integral_Fq T x v hT0.le (a, b, c, d)
  set S := nearSet (a * c) (b * d) T
  rw [← hs.sum_add_tsum_compl (s := S), _root_.tsum_subtype]
  have hsn : Summable fun p => ‖((↑S : Set (ℕ × ℕ))ᶜ).indicator X p‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_indicator_le_norm_self X p) hs.norm
  have hfar := (norm_tsum_le_tsum_norm hsn).trans (hKF a b c d T x v ha hb hc hd hT1 hx0 hx1 hv)
  have hnear := hKN a b c d T x v ha hb hc hd hT hx0 hx1 hv
  set W := ((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)
  have hW1 : 1 ≤ W := by
    have h1 : (1 : ℝ) ≤ ((a * c : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : (1 : ℝ) ≤ ((b * d : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hW : W = ((a * b * c * d : ℕ) : ℝ) := by simp only [W]; push_cast; ring
  have h613 : W ^ 6 ≤ W ^ 13 := pow_le_pow_right₀ hW1 (by norm_num)
  have hTp : 0 ≤ T ^ (299 / 300 : ℝ) := by positivity
  have key : ‖∑ p ∈ S, X p + ∑' p, ((↑S : Set (ℕ × ℕ))ᶜ).indicator X p‖ ≤
      (KN + KF) * T ^ (299 / 300 : ℝ) * W ^ 13 := by
   calc ‖∑ p ∈ S, X p + ∑' p, ((↑S : Set (ℕ × ℕ))ᶜ).indicator X p‖
      ≤ ‖∑ p ∈ S, X p‖ + ‖∑' p, ((↑S : Set (ℕ × ℕ))ᶜ).indicator X p‖ := norm_add_le _ _
    _ ≤ KN * W ^ 13 * T ^ (299 / 300 : ℝ) + KF * W ^ 6 * T ^ (299 / 300 : ℝ) := add_le_add hnear hfar
    _ ≤ KN * W ^ 13 * T ^ (299 / 300 : ℝ) + KF * W ^ 13 * T ^ (299 / 300 : ℝ) := by gcongr
    _ = (KN + KF) * T ^ (299 / 300 : ℝ) * W ^ 13 := by ring
  rw [hW] at key
  convert key using 3
  · norm_num
  · rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The off-diagonal clause of `SKSplitHyp'`, unconditionally** (window `φ_T` on `[T/2, 3T]`,
`h = K/log T`), for `0 ≤ θ < 1/16800`. -/
theorem offLag_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 16800) :
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      lagInt (OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (phiT T) (T / 2) (3 * T) (K / Real.log T) ≤
        1 / Real.sqrt K * T * (K / Real.log T) ^ 2 :=
  offLag_bound_of_quad (by norm_num) hθ0 (by linarith) quadOffHyp

/-- `θ ≤ 1/81600` (the range of `selbergMollHyp_of_QF_split`) is covered. -/
theorem offLag_bound_81600 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 81600) :
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      lagInt (OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (phiT T) (T / 2) (3 * T) (K / Real.log T) ≤
        1 / Real.sqrt K * T * (K / Real.log T) ^ 2 :=
  offLag_bound hθ0 (by linarith)

/-- **`SKSplitHyp' θ` from the diagonal clause alone.** -/
theorem skSplitHyp'_of_diagHypT {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 16800) (hD : DiagHypT θ) :
    SelbergKey2.SKSplitHyp' θ :=
  skSplitHyp'_of_diag (by norm_num) hθ0 (by linarith) hD quadOffHyp

/-- **Positive proportion on `QFHyp ∧ SKQFHyp θ ∧ DiagApproxHyp θ`** (no off-diagonal hypothesis). -/
theorem tauL_positive_proportion_of_SKQF' {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : HafnerBridge.QFHyp) (hS : SelbergKey.SKQFHyp θ) (hD : SelbergKeyDiag.DiagApproxHyp θ) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ HeckeL.tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  SelbergKeyDiag.tauL_positive_proportion_of_SKQF hθ0 hθ (B := 13) (η := 1 / 300) (by norm_num)
    (by linarith) hQ hS hD quadOffHyp

end RamanujanTau.SelbergKey7

open RamanujanTau.SelbergKey7

#print axioms quadOffHyp
#print axioms offLag_bound
#print axioms offLag_bound_81600
#print axioms skSplitHyp'_of_diagHypT
#print axioms tauL_positive_proportion_of_SKQF'
#print axioms far_bound
#print axioms near_bound
#print axioms line_bound
#print axioms abel_line
#print axioms Hl_deriv
#print axioms near_sum_eq
#print axioms Fq_eq
#print axioms far_pt
#print axioms far_pt_real
#print axioms sum_box_Maj
#print axioms sum_lam_sq_rpow_le
