/-
# Page 206 (Rebák's Theorem 4.1) from the single gap `SepticSonCore`

`page206_of_sonCore : SepticSonCore → Page206Evaluation`. Every other step is proved:

1. Lemma 2.1 (`rebak_lemma_2_1`, Mathlib's theta transformation) at `n = 343` and `n = 7`. This gives
   `φ(e^{−7π√7}) = 7^{−3/4} φ(x₀)` with `x₀ = e^{−π/(7√7)}`, and `R = φ⁴(x₀⁷)/φ⁴(x₀⁴⁹) = 7`.
2. Entry 1.1(i), the 7-dissection `φ = a + 2b + 2c + 2d`, and the quaternion identity (A), both
   transferred to real `x₀` by the evaluation ring homomorphism (`RealTransfer`).
3. (iii) with `R = 7` gives `(1−p)((1−p)² + 35) = 0`, hence `p = 1`. This replaces `G₇ = 2^{1/4}`.
4. (A), (B) and `p = 1` show that `s₁ = u³v, s₂ = v³w, s₃ = w³u` have elementary symmetric functions
   `6, 5, 1`, i.e. they are the roots of `ξ³ − 6ξ² + 5ξ − 1`.
5. The roots are `1/(4cos²(kπ/7))` (`Cubic`, via Chebyshev `U₆`). The crude enclosures of `Bounds`
   (`s₁ > 1 > s₂ > s₃`) pin `s₁, s₂, s₃` to `1/(4cos²(3π/7)), 1/(4cos²(2π/7)), 1/(4cos²(π/7))`. These
   enclosures replace Rebák's Lemmas 3.2–3.8 at this point.
6. `u⁷ = s₁²/s₂` (and cyclically), using `p = 1`. Taking 7th roots gives the three cosine terms.
-/
import RamanujanTau.Septic.Son
import RamanujanTau.Septic.Bounds
import RamanujanTau.Septic.Cubic
import RamanujanTau.Septic.Transform

set_option autoImplicit false

namespace RamanujanTau.Septic

open Real

/-! ### Step 6: seventh roots -/

lemma eq_rpow_two_sevenths {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) (h : u ^ 7 = y ^ 2) :
    u = y ^ (2 / 7 : ℝ) := by
  have h1 : (u ^ 7) ^ ((7 : ℕ)⁻¹ : ℝ) = u := Real.pow_rpow_inv_natCast hu (by norm_num)
  rw [← h1, h, ← Real.rpow_natCast_mul hy]
  norm_num

/-! ### Steps 3–6: the real algebra -/

/-- Pure algebra at the special point, given `p = 1` (`8bcd = a³`): from (A), (B), `R = 7` and three crude
inequalities, `u, v, w` are the three cosine terms. -/
theorem septic_algebra_of_p {a b c d P : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : P ^ 4 = a ^ 4 + 24 * a * b * c * d + 8 * (b ^ 3 * c + c ^ 3 * d + d ^ 3 * b))
    (hB : a * (b ^ 2 * c ^ 3 + c ^ 2 * d ^ 3 + d ^ 2 * b ^ 3) = a ^ 3 * b * c * d + 2 * (b * c * d) ^ 2)
    (hp : 8 * b * c * d = a ^ 3)
    (hR : P ^ 4 = 7 * a ^ 4)
    (h2 : 16 * c ^ 3 * d < a ^ 4) (h3 : 16 * d ^ 3 * b < a ^ 4)
    (h23 : d ^ 2 * b < c ^ 3) :
    2 * b / a = (cos (2 * π / 7) / (2 * cos (3 * π / 7) ^ 2)) ^ (2 / 7 : ℝ) ∧
    2 * c / a = (cos (π / 7) / (2 * cos (2 * π / 7) ^ 2)) ^ (2 / 7 : ℝ) ∧
    2 * d / a = (cos (3 * π / 7) / (2 * cos (π / 7) ^ 2)) ^ (2 / 7 : ℝ) := by
  -- step 4: Vieta
  have ha4 : 0 < a ^ 4 := by positivity
  set s1 := 16 * b ^ 3 * c / a ^ 4 with hs1
  set s2 := 16 * c ^ 3 * d / a ^ 4 with hs2
  set s3 := 16 * d ^ 3 * b / a ^ 4 with hs3
  have E1 : 16 * (b ^ 3 * c + c ^ 3 * d + d ^ 3 * b) = 6 * a ^ 4 := by
    linear_combination (-2) * hA + 2 * hR - 6 * a * hp
  have E2 : 256 * (b ^ 3 * c * (c ^ 3 * d) + c ^ 3 * d * (d ^ 3 * b) + d ^ 3 * b * (b ^ 3 * c))
      = 5 * a ^ 8 := by
    have E2a : a * (256 * (b ^ 3 * c * (c ^ 3 * d) + c ^ 3 * d * (d ^ 3 * b) + d ^ 3 * b * (b ^ 3 * c)))
        = a * (5 * a ^ 8) := by
      linear_combination (256 * b * c * d) * hB
        + (5 * a ^ 6 + 40 * (b * c * d) * a ^ 3 + 64 * (b * c * d) ^ 2) * hp
    exact mul_left_cancel₀ ha.ne' E2a
  have E3 : 4096 * (b ^ 3 * c) * (c ^ 3 * d) * (d ^ 3 * b) = a ^ 12 := by
    have : (8 * b * c * d) ^ 4 = (a ^ 3) ^ 4 := by rw [hp]
    linear_combination this
  have hvieta : ∀ ξ : ℝ, (ξ - s1) * (ξ - s2) * (ξ - s3) = rcub ξ := by
    intro ξ
    have e1 : s1 + s2 + s3 = 6 := by
      rw [hs1, hs2, hs3]; field_simp; linear_combination E1
    have e2 : s1 * s2 + s2 * s3 + s3 * s1 = 5 := by
      rw [hs1, hs2, hs3]; field_simp; linear_combination E2
    have e3 : s1 * s2 * s3 = 1 := by
      rw [hs1, hs2, hs3]; field_simp; linear_combination E3
    unfold rcub
    linear_combination (-ξ ^ 2) * e1 + ξ * e2 - e3
  -- step 5: ordering and identification
  have hs1g : 1 < s1 := by rw [hs1, lt_div_iff₀ ha4]; linarith
  have hs2l : s2 < 1 := by rw [hs2, div_lt_iff₀ ha4]; linarith
  have hs3l : s3 < 1 := by rw [hs3, div_lt_iff₀ ha4]; linarith
  have hs23 : s3 < s2 := by
    rw [hs2, hs3]; apply div_lt_div_of_pos_right _ ha4
    nlinarith [mul_pos hd (mul_pos hd hd)]
  have root_cases : ∀ ξ, rcub ξ = 0 → ξ = s1 ∨ ξ = s2 ∨ ξ = s3 := by
    intro ξ hξ
    rw [← hvieta ξ] at hξ
    rcases mul_eq_zero.mp hξ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  have hA1 : rootA = s1 := by
    rcases root_cases _ rootA_root with h | h | h
    · exact h
    · exact absurd h (by linarith [rootA_gt_one])
    · exact absurd h (by linarith [rootA_gt_one])
  have hB2 : rootB = s2 ∧ rootC = s3 := by
    have hBn1 : rootB ≠ s1 := by linarith [rootB_lt_one]
    have hCn1 : rootC ≠ s1 := by linarith [rootB_lt_one, rootC_lt_rootB]
    rcases root_cases _ rootB_root with h | h | h
    · exact absurd h hBn1
    · refine ⟨h, ?_⟩
      rcases root_cases _ rootC_root with h' | h' | h'
      · exact absurd h' hCn1
      · exact absurd (h'.trans h.symm) (ne_of_lt rootC_lt_rootB)
      · exact h'
    · rcases root_cases _ rootC_root with h' | h' | h'
      · exact absurd h' hCn1
      · exact absurd (by linarith [rootC_lt_rootB] : s2 < s3) (not_lt.mpr hs23.le)
      · exact absurd (h'.trans h.symm) (ne_of_lt rootC_lt_rootB)
  obtain ⟨hB2, hC3⟩ := hB2
  -- step 6
  have c1 := c1_pos; have c2 := c2_pos; have c3 := c3_pos
  simp only [one_mul] at c1
  have hrA : rootA = 1 / (4 * cos (3 * π / 7) ^ 2) := rfl
  have hrB : rootB = 1 / (4 * cos (2 * π / 7) ^ 2) := rfl
  have hrC : rootC = 1 / (4 * cos (π / 7) ^ 2) := by rw [rootC, one_mul]
  have ha7 : a ^ 7 = 8 * b * c * d * a ^ 4 := by rw [hp]; ring
  refine ⟨?_, ?_, ?_⟩
  · apply eq_rpow_two_sevenths (by positivity) (by positivity)
    have key : (2 * b / a) ^ 7 = s1 ^ 2 / s2 := by
      calc (2 * b / a) ^ 7 = 128 * b ^ 7 / a ^ 7 := by ring
        _ = 128 * b ^ 7 / (8 * b * c * d * a ^ 4) := by rw [ha7]
        _ = s1 ^ 2 / s2 := by rw [hs1, hs2]; field_simp; ring
    rw [key, ← hA1, ← hB2, hrA, hrB]; field_simp; ring
  · apply eq_rpow_two_sevenths (by positivity) (by positivity)
    have key : (2 * c / a) ^ 7 = s2 ^ 2 / s3 := by
      calc (2 * c / a) ^ 7 = 128 * c ^ 7 / a ^ 7 := by ring
        _ = 128 * c ^ 7 / (8 * b * c * d * a ^ 4) := by rw [ha7]
        _ = s2 ^ 2 / s3 := by rw [hs2, hs3]; field_simp; ring
    rw [key, ← hB2, ← hC3, hrB, hrC]; field_simp; ring
  · apply eq_rpow_two_sevenths (by positivity) (by positivity)
    have key : (2 * d / a) ^ 7 = s3 ^ 2 / s1 := by
      calc (2 * d / a) ^ 7 = 128 * d ^ 7 / a ^ 7 := by ring
        _ = 128 * d ^ 7 / (8 * b * c * d * a ^ 4) := by rw [ha7]
        _ = s3 ^ 2 / s1 := by rw [hs3, hs1]; field_simp; ring
    rw [key, ← hC3, ← hA1, hrC, hrA]; field_simp; ring

/-- Pure algebra at the special point: from (A), (B), (iii), `R = 7` and three crude inequalities,
`u, v, w` are the three cosine terms. Entry 1.1(iii) at `R = 7` gives `p = 1`. -/
theorem septic_algebra {a b c d P : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : P ^ 4 = a ^ 4 + 24 * a * b * c * d + 8 * (b ^ 3 * c + c ^ 3 * d + d ^ 3 * b))
    (hB : a * (b ^ 2 * c ^ 3 + c ^ 2 * d ^ 3 + d ^ 2 * b ^ 3) = a ^ 3 * b * c * d + 2 * (b * c * d) ^ 2)
    (hIII : a * P ^ 8 + (a ^ 3 - 8 * b * c * d) ^ 3 = (2 * a ^ 5 + 40 * a ^ 2 * b * c * d) * P ^ 4)
    (hR : P ^ 4 = 7 * a ^ 4)
    (h2 : 16 * c ^ 3 * d < a ^ 4) (h3 : 16 * d ^ 3 * b < a ^ 4)
    (h23 : d ^ 2 * b < c ^ 3) :
    2 * b / a = (cos (2 * π / 7) / (2 * cos (3 * π / 7) ^ 2)) ^ (2 / 7 : ℝ) ∧
    2 * c / a = (cos (π / 7) / (2 * cos (2 * π / 7) ^ 2)) ^ (2 / 7 : ℝ) ∧
    2 * d / a = (cos (3 * π / 7) / (2 * cos (π / 7) ^ 2)) ^ (2 / 7 : ℝ) := by
  have hP8 : P ^ 8 = 49 * a ^ 8 := by
    rw [show P ^ 8 = (P ^ 4) ^ 2 by ring, hR]; ring
  have hm : (a ^ 3 - 8 * b * c * d) * ((a ^ 3 - 8 * b * c * d) ^ 2 + 35 * a ^ 6) = 0 := by
    linear_combination hIII - a * hP8 + (2 * a ^ 5 + 40 * a ^ 2 * b * c * d) * hR
  have hp : 8 * b * c * d = a ^ 3 := by
    have hpos : 0 < (a ^ 3 - 8 * b * c * d) ^ 2 + 35 * a ^ 6 := by positivity
    have := (mul_eq_zero.mp hm).resolve_right hpos.ne'
    linarith
  exact septic_algebra_of_p ha hb hc hd hA hB hp hR h2 h3 h23

/-! ### Steps 1–2: transfer to the point `x₀` -/

section transfer

lemma hx0' : 0 ≤ x0 := x0_pos.le

/-- the subring of power series convergent at `x₀` -/
local notation "S0" => convSub x0 hx0'

lemma ev0 (F : PowerSeries ℤ) (h : AbsConv x0 F) : evHom x0 hx0' ⟨F, h⟩ = evR x0 F := rfl

lemma evT0 : evR x0 (T 0) = aR := evR_T hx0' x0_lt_one (r := ((0 : ℕ) : ℤ)) (by norm_num) (by norm_num)
lemma evT1 : evR x0 (T 1) = bR := evR_T hx0' x0_lt_one (r := ((1 : ℕ) : ℤ)) (by norm_num) (by norm_num)
lemma evT2 : evR x0 (T 2) = cR := evR_T hx0' x0_lt_one (r := ((2 : ℕ) : ℤ)) (by norm_num) (by norm_num)
lemma evT3 : evR x0 (T 3) = dR := evR_T hx0' x0_lt_one (r := ((3 : ℕ) : ℤ)) (by norm_num) (by norm_num)

/-- the five elements of `S0` -/
noncomputable def eA : S0 := ⟨T 0, T0_mem hx0' x0_lt_one⟩
noncomputable def eB : S0 := ⟨T 1, T1_mem hx0' x0_lt_one⟩
noncomputable def eC : S0 := ⟨T 2, T2_mem hx0' x0_lt_one⟩
noncomputable def eD : S0 := ⟨T 3, T3_mem hx0' x0_lt_one⟩
noncomputable def eP : S0 := ⟨ramF 7 7, ramF_mem hx0' x0_lt_one 7 7⟩
noncomputable def ePhi : S0 := ⟨phi, ramF_mem hx0' x0_lt_one 1 1⟩

lemma evA : evHom x0 hx0' eA = aR := evT0
lemma evB : evHom x0 hx0' eB = bR := evT1
lemma evC : evHom x0 hx0' eC = cR := evT2
lemma evD : evHom x0 hx0' eD = dR := evT3
lemma evP : evHom x0 hx0' eP = phiR (x0 ^ 7) := evR_ramF_mm hx0' x0_lt_one (by norm_num)
lemma evPhi : evHom x0 hx0' ePhi = phiR x0 := by
  have := evR_ramF_mm hx0' x0_lt_one (m := 1) le_rfl
  rw [pow_one] at this; exact this

lemma real_dissection : phiR x0 = aR + 2 * bR + 2 * cR + 2 * dR := by
  have h : ePhi = eA + 2 * eB + 2 * eC + 2 * eD := Subtype.ext (by
    simp only [ePhi, eA, eB, eC, eD, Subring.coe_add, Subring.coe_mul]
    rw [phi_T]; rfl)
  have := congrArg (evHom x0 hx0') h
  simp only [map_add, map_mul, map_ofNat, evA, evB, evC, evD, evPhi] at this
  exact this

lemma real_quaternion :
    phiR (x0 ^ 7) ^ 4 = aR ^ 4 + 24 * aR * bR * cR * dR
      + 8 * (bR ^ 3 * cR + cR ^ 3 * dR + dR ^ 3 * bR) := by
  have h : eP ^ 4 = eA ^ 4 + 24 * eA * eB * eC * eD + 8 * (eB ^ 3 * eC + eC ^ 3 * eD + eD ^ 3 * eB) :=
    Subtype.ext (by
      simp only [eP, eA, eB, eC, eD, Subring.coe_add, Subring.coe_mul, Subring.coe_pow]
      rw [quaternion_identity_T]; rfl)
  have := congrArg (evHom x0 hx0') h
  simp only [map_add, map_mul, map_pow, map_ofNat, evA, evB, evC, evD, evP] at this
  exact this

lemma real_sextic (h : SonSextic) :
    aR * (bR ^ 2 * cR ^ 3 + cR ^ 2 * dR ^ 3 + dR ^ 2 * bR ^ 3)
      = aR ^ 3 * bR * cR * dR + 2 * (bR * cR * dR) ^ 2 := by
  have h' : eA * (eB ^ 2 * eC ^ 3 + eC ^ 2 * eD ^ 3 + eD ^ 2 * eB ^ 3)
      = eA ^ 3 * eB * eC * eD + 2 * (eB * eC * eD) ^ 2 :=
    Subtype.ext (by
      simp only [eA, eB, eC, eD, Subring.coe_add, Subring.coe_mul, Subring.coe_pow]
      rw [sonSextic_T h]; rfl)
  have := congrArg (evHom x0 hx0') h'
  simp only [map_add, map_mul, map_pow, map_ofNat, evA, evB, evC, evD] at this
  exact this

lemma real_entryIII (h : SonEntryIII) :
    aR * phiR (x0 ^ 7) ^ 8 + (aR ^ 3 - 8 * bR * cR * dR) ^ 3
      = (2 * aR ^ 5 + 40 * aR ^ 2 * bR * cR * dR) * phiR (x0 ^ 7) ^ 4 := by
  have h' : eA * eP ^ 8 + (eA ^ 3 - 8 * eB * eC * eD) ^ 3
      = (2 * eA ^ 5 + 40 * eA ^ 2 * eB * eC * eD) * eP ^ 4 :=
    Subtype.ext (by
      simp only [eA, eB, eC, eD, eP, Subring.coe_add, Subring.coe_mul, Subring.coe_pow,
        AddSubgroupClass.coe_sub]
      exact sonEntryIII_T h)
  have := congrArg (evHom x0 hx0') h'
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, evA, evB, evC, evD, evP] at this
  exact this

end transfer

/-! ### Step 1: Lemma 2.1 at `n = 7` and `n = 343` -/

lemma sqrt343 : √(343 : ℝ) = 7 * √7 := by
  rw [show (343 : ℝ) = 7 ^ 2 * 7 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma x0_pow7 : x0 ^ 7 = Real.exp (-π / √7) := by
  rw [x0, ← Real.exp_nat_mul]; congr 1
  have : (0 : ℝ) < √7 := by positivity
  field_simp; push_cast; ring

lemma x0_pow49 : x0 ^ 49 = Real.exp (-π * √7) := by
  rw [x0, ← Real.exp_nat_mul]; congr 1
  have h7 : (0 : ℝ) < √7 := by positivity
  have hs : √7 * √7 = 7 := Real.mul_self_sqrt (by norm_num)
  field_simp; push_cast; linear_combination 7 * hs

lemma aR_eq : aR = phiR (Real.exp (-π * √7)) := by
  rw [← evT0, T0_eq, evR_ramF_mm hx0' x0_lt_one (by norm_num), x0_pow49]

/-- `R = φ⁴(x₀⁷)/φ⁴(x₀⁴⁹) = 7` (Lemma 2.1 at `n = 7`). -/
lemma R_eq_seven : phiR (x0 ^ 7) ^ 4 = 7 * aR ^ 4 := by
  rw [x0_pow7, rebak_lemma_2_1 (by norm_num : (0 : ℝ) < 7), aR_eq, mul_pow,
    ← Real.rpow_natCast ((7 : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Lemma 2.1 at `n = 343`: `φ(x₀) = 7^{3/4} φ(e^{−7π√7})`. -/
lemma phi_x0 : phiR x0 = (7 : ℝ) ^ (3 / 4 : ℝ) * phiR (Real.exp (-7 * π * √7)) := by
  have h := rebak_lemma_2_1 (by norm_num : (0 : ℝ) < 343)
  rw [sqrt343] at h
  rw [x0, h, show (-π * (7 * √7)) = -7 * π * √7 by ring,
    show (343 : ℝ) = 7 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-! ### The page-206 evaluation from `SepticSonCore` -/

/-- **Rebák's Theorem 4.1 (Ramanujan's Lost Notebook, p. 206), conditional on `SepticSonCore`**
(Son's sextic relation and Entry 1.1(iii) as `ℤ⟦q⟧` identities). -/
theorem page206_of_sonCore (h : SepticSonCore) : Page206Evaluation := by
  have ha := aR_pos; have hb := bR_pos; have hc := cR_pos; have hd := dR_ge
  obtain ⟨hu, hv, hw⟩ := septic_algebra ha hb hc hd real_quaternion (real_sextic h.1)
    (real_entryIII h.2) R_eq_seven ineq_s2 ineq_s3 ineq_s23
  have key : phiR (Real.exp (-7 * π * √7)) * (7 : ℝ) ^ (3 / 4 : ℝ)
      = aR * (1 + 2 * bR / aR + 2 * cR / aR + 2 * dR / aR) := by
    rw [mul_comm, ← phi_x0, real_dissection]; field_simp
  have h7 : (0 : ℝ) < (7 : ℝ) ^ (3 / 4 : ℝ) := by positivity
  unfold Page206Evaluation
  rw [← aR_eq, Real.rpow_neg (by norm_num), ← hu, ← hv, ← hw]
  have e := key
  field_simp at e ⊢
  linear_combination e

end RamanujanTau.Septic
