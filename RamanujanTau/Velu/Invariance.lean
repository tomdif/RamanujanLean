import RamanujanTau.Velu.Main

/-!
# Vélu: the sum formulas and `G`-invariance

For `P ∈ E(K) ∖ G`:
* `X(P) = Σ_{V∈G} x(P + V) - Σ_{V∈G} x(V)` (`X_eq_sum`),
* `Y(P) = Σ_{V∈G} y(P + V)` (`Y_eq_sum`),
(with the convention `x(0) = y(0) = 0`), hence `X(P + R) = X(P)` and `Y(P + R) = Y(P)` for
`R ∈ G` (`X_add_mem`, `Y_add_mem`).
-/

namespace Velu

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K]

/-- `t/(x₀ - x_Q) + u/(x₀ - x_Q)² = x(P+Q) + x(P-Q) - 2x_Q` (no condition on `y₀`). -/
theorem jet0_alg (A B x0 y0 xq yq : K) (h0 : y0 ^ 2 = x0 ^ 3 + A * x0 + B)
    (hq : yq ^ 2 = xq ^ 3 + A * xq + B) (hx : x0 ≠ xq) :
    (6 * xq ^ 2 + 2 * A) / (x0 - xq) + 4 * yq ^ 2 / (x0 - xq) ^ 2 =
      (((y0 - yq) / (x0 - xq)) ^ 2 - x0 - xq) + (((y0 + yq) / (x0 - xq)) ^ 2 - x0 - xq) -
        2 * xq := by
  have hd : x0 - xq ≠ 0 := sub_ne_zero.2 hx
  have hB : B = y0 ^ 2 - x0 ^ 3 - A * x0 := by linear_combination -h0
  subst hB
  have hA : A = (y0 ^ 2 - yq ^ 2 - x0 ^ 3 + xq ^ 3) / (x0 - xq) := by
    field_simp; linear_combination hq
  subst hA
  field_simp
  ring

variable [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

lemma phi_eq_point {P Q : (short A B).Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : xc P ≠ xc Q) :
    tQ Q / (xc P - xc Q) + uQ Q / (xc P - xc Q) ^ 2 =
      xc (P + Q) + xc (P + -Q) - 2 * xc Q := by
  have hQ' : -Q ≠ 0 := neg_ne_zero.2 hQ
  have hx' : xc P ≠ xc (-Q) := by rwa [xc_neg]
  rw [(add_coords_of_xc_ne hP hQ hx).1, (add_coords_of_xc_ne hP hQ' hx').1]
  simp only [xc_neg, yc_neg, sub_neg_eq_add, tQ, uQ]
  exact jet0_alg A B _ _ _ _ (equation_xc_yc hP) (equation_xc_yc hQ) hx

/-- **Vélu's `X` as a sum over the kernel**: `X(P) = Σ_{V∈G} x(P+V) - Σ_{V∈G} x(V)`. -/
theorem X_eq_sum {P : (short A B).Point} (hP0 : P ≠ 0) (hP : P ∉ κ.G) :
    κ.X (xc P) = ∑ V ∈ κ.G, xc (P + V) - ∑ V ∈ κ.G, xc V := by
  rw [κ.sum_G (fun V => xc (P + V)), κ.sum_G xc, X,
    Finset.sum_congr rfl fun Q hQ => phi_eq_point hP0 (κ.ne_zero_of_mem_S hQ)
      (κ.xc_ne_of_not_mem_G hP0 hP hQ)]
  simp only [add_zero, xc_zero, zero_add, xc_neg]
  rw [Finset.sum_sub_distrib]
  have : ∑ Q ∈ κ.S, 2 * xc Q = ∑ Q ∈ κ.S, (xc Q + xc Q) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

lemma sum_G_neg {M : Type*} [AddCommMonoid M] (g : (short A B).Point → M) :
    ∑ V ∈ κ.G, g (-V) = ∑ V ∈ κ.G, g V := by
  refine Finset.sum_nbij' (fun V => -V) (fun V => -V) ?_ ?_ ?_ ?_ ?_
  · intro V hV; exact κ.neg_mem _ hV
  · intro V hV; exact κ.neg_mem _ hV
  · intro V _; simp
  · intro V _; simp
  · intro V _; rfl

/-- **Vélu's `Y` as a sum over the kernel**: `Y(P) = Σ_{V∈G} y(P+V)`. -/
theorem Y_eq_sum (h2 : (2 : K) ≠ 0) {P : (short A B).Point} (hP0 : P ≠ 0) (hP : P ∉ κ.G) :
    κ.Y (xc P) (yc P) = ∑ V ∈ κ.G, yc (P + V) := by
  by_cases hy : yc P = 0
  · -- `P` is `2`-torsion: both sides vanish
    rw [Y_eq, hy, zero_mul]
    have hPn : -P = P := by
      obtain ⟨h, eP⟩ := eq_some_of_ne_zero hP0
      rw [eP, Affine.Point.neg_some]
      congr 1
      simp [Affine.negY, hy]
    have hs := κ.sum_G_neg (fun V => yc (P + V))
    have : ∀ V, yc (P + -V) = -yc (P + V) := by
      intro V
      rw [← yc_neg, neg_add, hPn]
    simp only [this, Finset.sum_neg_distrib] at hs
    have h2s : 2 * ∑ V ∈ κ.G, yc (P + V) = 0 := by linear_combination -hs
    exact ((mul_eq_zero.1 h2s).resolve_left h2).symm
  · rw [κ.sum_G (fun V => yc (P + V)), Y, add_zero]
    have hjet : ∀ Q ∈ κ.S, uQ Q * (2 * yc P) / (xc P - xc Q) ^ 3 +
        tQ Q * yc P / (xc P - xc Q) ^ 2 = -(yc (P + Q) + yc (P + -Q)) := by
      intro Q hQ
      have h := jet_point hP0 (κ.ne_zero_of_mem_S hQ) (κ.xc_ne_of_not_mem_G hP0 hP hQ) hy h2 1
        (by norm_num)
      simp only [cj, one_ne_zero, if_false, sub_zero, jet_one_eq] at h
      have hab : yc (P + Q) + yc (P + -Q) = yc P * -(tQ Q * (xc P - xc Q)⁻¹ ^ 2 +
          2 * uQ Q * (xc P - xc Q)⁻¹ ^ 3) := by
        rw [h]; field_simp
      rw [hab, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]; ring
    rw [Finset.sum_congr rfl hjet, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- `G`-invariance of `X`. -/
theorem X_add_mem {P R : (short A B).Point} (hP0 : P ≠ 0) (hP : P ∉ κ.G) (hR : R ∈ κ.G) :
    κ.X (xc (P + R)) = κ.X (xc P) := by
  have hPR : P + R ∉ κ.G := fun h => hP (by
    simpa using κ.add_mem _ h _ (κ.neg_mem _ hR))
  have hPR0 : P + R ≠ 0 := fun h => hPR (h ▸ κ.zero_mem)
  rw [κ.X_eq_sum hPR0 hPR, κ.X_eq_sum hP0 hP]
  congr 1
  rw [← κ.sum_G_translate (fun V => xc (P + V)) hR]
  simp only [add_assoc]

/-- `G`-invariance of `Y`. -/
theorem Y_add_mem (h2 : (2 : K) ≠ 0) {P R : (short A B).Point} (hP0 : P ≠ 0) (hP : P ∉ κ.G)
    (hR : R ∈ κ.G) : κ.Y (xc (P + R)) (yc (P + R)) = κ.Y (xc P) (yc P) := by
  have hPR : P + R ∉ κ.G := fun h => hP (by
    simpa using κ.add_mem _ h _ (κ.neg_mem _ hR))
  have hPR0 : P + R ≠ 0 := fun h => hPR (h ▸ κ.zero_mem)
  rw [κ.Y_eq_sum h2 hPR0 hPR, κ.Y_eq_sum h2 hP0 hP]
  rw [← κ.sum_G_translate (fun V => yc (P + V)) hR]
  simp only [add_assoc]

end Kernel

end Velu
