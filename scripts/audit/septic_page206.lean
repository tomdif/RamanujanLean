/-
Audit for the page-206 chain (Rebák, Theorem 4.1); see docs/SEPTIC_PAGE206.md.

Every theorem listed below must depend only on [propext, Classical.choice, Quot.sound].

Headline: `page206_unconditional : Page206Evaluation`, with no gap. `SepticSonCore` (Son's (iii) and the
sextic relation as ℤ⟦q⟧ identities) is still stated, but only the conditional route `page206_of_sonCore` uses it.
-/
import RamanujanTau.Septic.Page206Final

set_option autoImplicit false

open PowerSeries RamanujanTau.Septic Real

/-- **Headline: Rebák's Theorem 4.1 (Lost Notebook p. 206), unconditionally.** -/
example : Page206Evaluation := page206_unconditional

/-- The earlier conditional route (kept): from Son's (iii) + sextic relation. -/
example : SepticSonCore → Page206Evaluation := page206_of_sonCore

/-- 8-dimensional lattice identities `φ(q⁷)⁸ = P_{W}(a,b,c,d)`. -/
example : ramF 7 7 ^ 8 = O1poly := octo1_identity
example : ramF 7 7 ^ 8 = O2poly := octo2_identity

/-- (a) Rebák's Lemma 2.1. -/
example {n : ℝ} (hn : 0 < n) :
    phiR (Real.exp (-π / √n)) = n ^ (1 / 4 : ℝ) * phiR (Real.exp (-π * √n)) :=
  rebak_lemma_2_1 hn

/-- Quaternion identity = Entry 1.1(iv)/(v), first symmetric function:
`φ(q⁷)⁴ = φ(q⁴⁹)⁴ + 24 φ(q⁴⁹) B C D + 8(B³C + C³D + D³B)`. -/
example :
    ramF 7 7 ^ 4 = ramF 49 49 ^ 4
      + 24 * ramF 49 49 * (X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91)
      + 8 * ((X * ramF 35 63) ^ 3 * (X ^ 4 * ramF 21 77) + (X ^ 4 * ramF 21 77) ^ 3 * (X ^ 9 * ramF 7 91)
        + (X ^ 9 * ramF 7 91) ^ 3 * (X * ramF 35 63)) :=
  quaternion_identity

/-- (b) real transfer: evaluation is a ring hom on absolutely convergent series, and
`φ(q^m)` evaluates to `phiR (x^m)`. -/
example (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) (hm : 1 ≤ m) :
    evR x (ramF m m) = phiR (x ^ m) := evR_ramF_mm hx0 hx1 hm

/-- Real form at `x₀ = e^{−π/(7√7)}` of Entry 1.1(i) (with Lemma 2.1 at n = 343). -/
example : phiR x0 = (7 : ℝ) ^ (3 / 4 : ℝ) * phiR (Real.exp (-7 * π * √7)) := phi_x0
example : phiR x0 = aR + 2 * bR + 2 * cR + 2 * dR := real_dissection
/-- `R = 7` at the point. -/
example : phiR (x0 ^ 7) ^ 4 = 7 * aR ^ 4 := R_eq_seven

/-- (d) the roots of `ξ³ − 6ξ² + 5ξ − 1`. -/
example : rcub (1 / (4 * cos (3 * π / 7) ^ 2)) = 0 := rootA_root

#print axioms page206_unconditional
#print axioms page206_of_sonCore
#print axioms octo1_identity
#print axioms octo2_identity
#print axioms cert_f5
#print axioms cert_Bp
#print axioms real_octo1
#print axioms real_octo2
#print axioms septic_algebra_of_p
#print axioms rebak_lemma_2_1
#print axioms phiR_transform
#print axioms quaternion_identity
#print axioms quaternion_identity_T
#print axioms cnt_mul
#print axioms hasSum_fibre
#print axioms evR_mul
#print axioms evR_ramF_mm
#print axioms evR_T
#print axioms real_dissection
#print axioms real_quaternion
#print axioms R_eq_seven
#print axioms phi_x0
#print axioms ineq_s1
#print axioms ineq_s2
#print axioms ineq_s3
#print axioms ineq_s23
#print axioms U6_cos
#print axioms rootA_root
#print axioms rootB_root
#print axioms rootC_root
#print axioms septic_algebra

-- the named gap (statement only)
#check (SepticSonCore : Prop)
#check (SonSextic : Prop)
#check (SonEntryIII : Prop)
