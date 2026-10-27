/-
# Atkin–O'Brien 13^k: the 21 relations at the eta point of `ℤ⟦q⟧`

The theta point is the image of `ηPt = (η₁, …, η₆, q)` under `ιN`, with the first six entries scaled by
`B = ιN (q¹³;q¹³)_∞`. Each `W_i` is homogeneous of degree 4 in those entries, so `W_i(Jpt) = B⁴·ιN(W_i(ηPt))`.
-/
import RamanujanTau.Atkin13Cert.Rel

set_option autoImplicit false

namespace Atkin13
open PowerSeries ALz ALz13 MTC SPoly7
open Atkin11 (PS h1' ιN1_inv X_ι)

/-- the eta point `(η₁, …, η₆, q)`. -/
noncomputable def ηPt : List PS := [ηP 1, ηP 2, ηP 3, ηP 4, ηP 5, ηP 6, X]

/-- degree in the first six variables. -/
def deg6 (m : Mono) : ℕ := ((dec m).take 6).sum

def homog (k : ℕ) (p : Poly) : Bool := p.all fun t => deg6 t.1 == k

section Scale
variable {R : Type*} [CommRing R]

lemma evalM_scale (a1 a2 a3 a4 a5 a6 a7 B : R) (m : Mono) :
    evalM [B * a1, B * a2, B * a3, B * a4, B * a5, B * a6, a7] m = B ^ deg6 m * evalM [a1, a2, a3, a4, a5, a6, a7] m := by
  simp only [evalM, deg6, dec, evalL, List.take, List.sum_cons, List.sum_nil, mul_pow, pow_add]
  ring

lemma evalP_scale (a1 a2 a3 a4 a5 a6 a7 B : R) (k : ℕ) (p : Poly) (h : homog k p = true) :
    evalP [B * a1, B * a2, B * a3, B * a4, B * a5, B * a6, a7] p = B ^ k * evalP [a1, a2, a3, a4, a5, a6, a7] p := by
  induction p with
  | nil => simp [evalP]
  | cons t p ih =>
    simp only [homog, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [evalP_cons, evalP_cons, ih h.2, evalM_scale, h.1]
    ring

end Scale

lemma Jt1_ι (a : ℕ) (h0 : 1 ≤ a) (h1 : a < 13) :
    Jt h13 hd1 (a : ℤ) = ιN h1' (ηP a) * ιN h1' (RankProof.Pinf 13 13) := by
  have h := θ_eq_ιN_prod (d := 1) (a := 13) (b := a) h1' h0 h1 (by norm_num)
  rw [θ_congrN (show 1 * 13 = 13 by norm_num) _ h13] at h
  rw [ALz13.Jt, ← map_mul, ηP, show ((1 : ℕ) : ℤ) * (a : ℤ) = ((1 * a : ℕ) : ℤ) by push_cast; ring, h]

lemma Jpt_eq : Jpt = [ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 1), ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 2),
    ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 3), ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 4),
    ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 5), ιN h1' (RankProof.Pinf 13 13) * ιN h1' (ηP 6), ιN h1' X] := by
  have hQ : Qt hd1 = ιN h1' X := by rw [X_ι]; rfl
  have j1 := Jt1_ι 1 le_rfl (by norm_num)
  have j2 := Jt1_ι 2 (by norm_num) (by norm_num)
  have j3 := Jt1_ι 3 (by norm_num) (by norm_num)
  have j4 := Jt1_ι 4 (by norm_num) (by norm_num)
  have j5 := Jt1_ι 5 (by norm_num) (by norm_num)
  have j6 := Jt1_ι 6 (by norm_num) (by norm_num)
  push_cast at j1 j2 j3 j4 j5 j6
  simp only [Jpt, j1, j2, j3, j4, j5, j6, hQ, mul_comm]

/-- **transport**: a degree-4 homogeneous relation at the theta point holds at the eta point. -/
lemma pull4 (p : Poly) (hh : homog 4 p = true) (h : evalP Jpt p = 0) : evalP ηPt p = 0 := by
  have hB : ιN h1' (RankProof.Pinf 13 13) ≠ 0 :=
    ((RankProof.isUnit_Pinf 13 13 (by norm_num) (by norm_num)).map _).ne_zero
  rw [Jpt_eq, evalP_scale _ _ _ _ _ _ _ _ 4 p hh] at h
  have h2 : evalP (ηPt.map (ιN h1')) p = 0 := by
    have := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hB)
    simpa [ηPt] using this
  rw [← evalP_map] at h2
  exact (map_eq_zero_iff _ (MTC.ιN_injective h1')).mp h2

lemma Wall_homog : Wall.all (homog 4) = true := by decide +kernel

lemma W1_zero : evalP ηPt W1 = 0 := pull4 _ (by decide +kernel) W1_zero_L
lemma W2_zero : evalP ηPt W2 = 0 := pull4 _ (by decide +kernel) W2_zero_L
lemma W3_zero : evalP ηPt W3 = 0 := pull4 _ (by decide +kernel) W3_zero_L
lemma W4_zero : evalP ηPt W4 = 0 := pull4 _ (by decide +kernel) W4_zero_L
lemma W5_zero : evalP ηPt W5 = 0 := pull4 _ (by decide +kernel) W5_zero_L
lemma W6_zero : evalP ηPt W6 = 0 := pull4 _ (by decide +kernel) W6_zero_L
lemma W7_zero : evalP ηPt W7 = 0 := pull4 _ (by decide +kernel) W7_zero_L
lemma W8_zero : evalP ηPt W8 = 0 := pull4 _ (by decide +kernel) W8_zero_L
lemma W9_zero : evalP ηPt W9 = 0 := pull4 _ (by decide +kernel) W9_zero_L
lemma W10_zero : evalP ηPt W10 = 0 := pull4 _ (by decide +kernel) W10_zero_L
lemma W11_zero : evalP ηPt W11 = 0 := pull4 _ (by decide +kernel) W11_zero_L
lemma W12_zero : evalP ηPt W12 = 0 := pull4 _ (by decide +kernel) W12_zero_L
lemma W13_zero : evalP ηPt W13 = 0 := pull4 _ (by decide +kernel) W13_zero_L
lemma W14_zero : evalP ηPt W14 = 0 := pull4 _ (by decide +kernel) W14_zero_L
lemma W15_zero : evalP ηPt W15 = 0 := pull4 _ (by decide +kernel) W15_zero_L
lemma W16_zero : evalP ηPt W16 = 0 := pull4 _ (by decide +kernel) W16_zero_L
lemma W17_zero : evalP ηPt W17 = 0 := pull4 _ (by decide +kernel) W17_zero_L
lemma W18_zero : evalP ηPt W18 = 0 := pull4 _ (by decide +kernel) W18_zero_L
lemma W19_zero : evalP ηPt W19 = 0 := pull4 _ (by decide +kernel) W19_zero_L
lemma W20_zero : evalP ηPt W20 = 0 := pull4 _ (by decide +kernel) W20_zero_L
lemma W21_zero : evalP ηPt W21 = 0 := pull4 _ (by decide +kernel) W21_zero_L

lemma W_zero_mem : ∀ w ∈ Wall, evalP ηPt w = 0 := by
  intro w hw
  simp only [Wall, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact W1_zero
  · exact W2_zero
  · exact W3_zero
  · exact W4_zero
  · exact W5_zero
  · exact W6_zero
  · exact W7_zero
  · exact W8_zero
  · exact W9_zero
  · exact W10_zero
  · exact W11_zero
  · exact W12_zero
  · exact W13_zero
  · exact W14_zero
  · exact W15_zero
  · exact W16_zero
  · exact W17_zero
  · exact W18_zero
  · exact W19_zero
  · exact W20_zero
  · exact W21_zero

lemma W_zero_getD (i : ℕ) : evalP ηPt (Wall.getD i []) = 0 := by
  rcases Nat.lt_or_ge i Wall.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact W_zero_mem _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; simp [evalP]

end Atkin13
