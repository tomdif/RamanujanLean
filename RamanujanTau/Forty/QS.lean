/-
# Sums of binary quadratic forms over `ℤ²` as values (Cao's Type III gluing)

`qf_two` (Lattice.lean) compares two *product* expansions of one form. Cao's proofs of Entries 3.18 and 3.19(ii)
also need sums of forms that are not products, related by non-orthogonal changes of variables and parity splits
("1-dimensional ECS"). This file makes `Σ_{x∈ℤ²} F(x)` a value:

* `Summ F`: `F` is the function of some summable family; `QS F` is then its sum (`hs`), and `0` otherwise.
* `QS_cover`: for any exact cover `B` with `F(B w + i r) = a i · G i w`, `QS F = Σ_{i∈I} a i · QS (G i)`.
* `qmono_cmap`: on the coset `i`, `qmono` of a form is a monomial times `qmono` of the transformed form
  (`B`-conjugate quadratic part, affine-in-`i` linear part, transformed sign character).
* `qmono_summ`: every positive definite `qmono` is summable, through the generic orthogonal cover
  `(1 −Bq; 0 A)`.
* `QS_sub` (any cover) and `QS_orth` (orthogonal cover: theta products, as in `qf_two`).
-/
import RamanujanTau.Forty.Lattice

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset

/-- `F` is the coefficient function of a summable family. -/
def Summ (F : ℤ × ℤ → L) : Prop := ∃ P : SummableFamily ℤ ℂ (ℤ × ℤ), ∀ p, P p = F p

/-- `Σ_{x∈ℤ²} F(x)` (and `0` if `F` is not summable). -/
noncomputable def QS (F : ℤ × ℤ → L) : L := by
  classical exact if h : Summ F then hs (Classical.choose h) else 0

lemma QS_of (P : SummableFamily ℤ ℂ (ℤ × ℤ)) {F : ℤ × ℤ → L} (hP : ∀ p, P p = F p) : QS F = hs P := by
  classical
  have h : Summ F := ⟨P, hP⟩
  rw [QS, dif_pos h]
  congr 1
  exact SummableFamily.ext fun p => by rw [(Classical.choose_spec h) p, hP p]

/-- **gluing along an exact cover**: `Σ F = Σ_{i∈I} a i Σ G i` when `F(B w + i r) = a i G i w`. -/
theorem QS_cover (B : ECS) (F : ℤ × ℤ → L) (a : ℤ → L) (G : ℤ → ℤ × ℤ → L)
    (hG : ∀ i ∈ B.I, Summ (G i)) (hF : ∀ i ∈ B.I, ∀ w, F (B.cmap i w) = a i * G i w) :
    Summ F ∧ QS F = ∑ i ∈ B.I, a i * QS (G i) := by
  classical
  let E : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ) := fun i => if h : Summ (G i) then Classical.choose h else 0
  have hE : ∀ i ∈ B.I, ∀ w, E i w = G i w := fun i hi w => by
    simp only [E, dif_pos (hG i hi)]; exact Classical.choose_spec (hG i hi) w
  have hF' : ∀ i ∈ B.I, ∀ w, F (B.cmap i w) = a i * E i w := fun i hi w => by rw [hE i hi w]; exact hF i hi w
  have hP := splitFam_apply B a E F hF'
  refine ⟨⟨_, hP⟩, ?_⟩
  rw [QS_of _ hP, hs_splitFam]
  exact sum_congr rfl fun i hi => by rw [QS_of (E i) (hE i hi)]

/-! ## change of variables in `qmono` -/

section Sub
variable (A Bq C d e δ1 δ2 : ℤ) (B : ECS)

/-- the transformed quadratic coefficients `BᵀQB`. -/
def sA : ℤ := A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2
def sB : ℤ := A * B.b11 * B.b12 + Bq * (B.b11 * B.b22 + B.b12 * B.b21) + C * B.b21 * B.b22
def sC : ℤ := A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2
/-- the transformed linear coefficients on the coset `i`. -/
def sd (i : ℤ) : ℤ := 2 * A * B.b11 * (B.r1 * i) + 2 * Bq * (B.b11 * (B.r2 * i) + B.b21 * (B.r1 * i))
  + 2 * C * B.b21 * (B.r2 * i) + d * B.b11 + e * B.b21
def se (i : ℤ) : ℤ := 2 * A * B.b12 * (B.r1 * i) + 2 * Bq * (B.b12 * (B.r2 * i) + B.b22 * (B.r1 * i))
  + 2 * C * B.b22 * (B.r2 * i) + d * B.b12 + e * B.b22

theorem qmono_cmap (i : ℤ) (w : ℤ × ℤ) :
    qmono A Bq C d e δ1 δ2 (B.cmap i w) =
      mono (qf0 A Bq C d e B i) ((-1) ^ (δ1 * (B.r1 * i) + δ2 * (B.r2 * i))) *
        qmono (sA A Bq C B) (sB A Bq C B) (sC A Bq C B) (sd A Bq C d e B i) (se A Bq C d e B i)
          (δ1 * B.b11 + δ2 * B.b21) (δ1 * B.b12 + δ2 * B.b22) w := by
  obtain ⟨u, v⟩ := w
  simp only [qmono, ECS.cmap, mono_mul]
  refine mono_ext_lat ?_ ?_
  · simp only [qf0, sA, sB, sC, sd, se]; ring
  · have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
    rw [← zpow_add₀ hm]
    congr 1
    ring

/-- `QS` of a form along any exact cover. -/
theorem QS_sub
    (hS : ∀ i ∈ B.I, Summ (qmono (sA A Bq C B) (sB A Bq C B) (sC A Bq C B) (sd A Bq C d e B i) (se A Bq C d e B i)
      (δ1 * B.b11 + δ2 * B.b21) (δ1 * B.b12 + δ2 * B.b22))) :
    QS (qmono A Bq C d e δ1 δ2) = ∑ i ∈ B.I, mono (qf0 A Bq C d e B i) ((-1) ^ (δ1 * (B.r1 * i) + δ2 * (B.r2 * i))) *
      QS (qmono (sA A Bq C B) (sB A Bq C B) (sC A Bq C B) (sd A Bq C d e B i) (se A Bq C d e B i)
        (δ1 * B.b11 + δ2 * B.b21) (δ1 * B.b12 + δ2 * B.b22)) :=
  (QS_cover B _ _ _ hS fun i _ w => qmono_cmap A Bq C d e δ1 δ2 B i w).2

/-- `QS` of a form along an orthogonal cover: theta products (the two sides of `qf_two`). -/
theorem QS_orth {M1 M2 : ℕ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (horth : A * B.b11 * B.b12 + Bq * (B.b11 * B.b22 + B.b12 * B.b21) + C * B.b21 * B.b22 = 0)
    (hM1e : (M1 : ℤ) = 2 * (A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2))
    (hM2e : (M2 : ℤ) = 2 * (A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2)) :
    Summ (qmono A Bq C d e δ1 δ2) ∧
    QS (qmono A Bq C d e δ1 δ2) = ∑ i ∈ B.I, mono (qf0 A Bq C d e B i) ((-1) ^ (δ1 * (B.r1 * i) + δ2 * (B.r2 * i))) *
        (θ hM1 (qf1 A Bq C d e B i) (-((-1) ^ (δ1 * B.b11 + δ2 * B.b21))) *
          θ hM2 (qf2 A Bq C d e B i) (-((-1) ^ (δ1 * B.b12 + δ2 * B.b22)))) := by
  have h := QS_cover B (qmono A Bq C d e δ1 δ2) _
    (fun i => ⇑((thF hM1 (qf1 A Bq C d e B i) (-((-1) ^ (δ1 * B.b11 + δ2 * B.b21)))).mul
      (thF hM2 (qf2 A Bq C d e B i) (-((-1) ^ (δ1 * B.b12 + δ2 * B.b22))))))
    (fun i _ => ⟨_, fun _ => rfl⟩) (fun i _ w => qf_term A Bq C d e δ1 δ2 B hM1 hM2 horth hM1e hM2e i w)
  refine ⟨h.1, h.2.trans (sum_congr rfl fun i _ => ?_)⟩
  rw [QS_of _ (fun _ => rfl), θ_mul_hs]

end Sub

/-! ## every positive definite form is summable -/

/-- the orthogonal cover `B = (1 −Bq; 0 A)`, shifts `i (0,1)`, `0 ≤ i < A`. -/
noncomputable def orthECS (A Bq : ℤ) (hA : 0 < A) : ECS where
  b11 := 1
  b12 := -Bq
  b21 := 0
  b22 := A
  r1 := 0
  r2 := 1
  I := Finset.Ico 0 A
  det_ne := by simp; omega
  cover := fun m n => ⟨n % A, by
      rw [Finset.mem_Ico]; exact ⟨Int.emod_nonneg n hA.ne', Int.emod_lt_of_pos n hA⟩,
    m + Bq * (n / A), n / A, by ring, by have := Int.mul_ediv_add_emod n A; linarith⟩
  uniq := by
    intro i hi j hj u v u' v' _ h2
    rw [Finset.mem_Ico] at hi hj
    have e1 : (i + A * v) % A = i := by rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hi.1 hi.2
    have e2 : (j + A * v') % A = j := by rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hj.1 hj.2
    have h3 : i + A * v = j + A * v' := by linarith
    rw [← e1, ← e2, h3]

theorem qmono_summ (A Bq C d e δ1 δ2 : ℤ) (hA : 0 < A) (hD : 0 < A * C - Bq ^ 2) : Summ (qmono A Bq C d e δ1 δ2) := by
  have h1 : 1 ≤ (2 * A).toNat := by omega
  have hpos : 0 < A * (A * C - Bq ^ 2) := mul_pos hA hD
  have h2 : 1 ≤ (2 * (A * (A * C - Bq ^ 2))).toNat := by omega
  refine (QS_orth A Bq C d e δ1 δ2 (orthECS A Bq hA) h1 h2 ?_ ?_ ?_).1
  · simp only [orthECS]; ring
  · simp only [orthECS]; rw [Int.toNat_of_nonneg (by omega)]; ring
  · simp only [orthECS]; rw [Int.toNat_of_nonneg (by omega)]; ring

end Forty

namespace Forty
open ALz HahnSeries

/-- only the parity of the sign character matters. -/
lemma qmono_par (A Bq C d e δ1 δ2 δ1' δ2' : ℤ) (h1 : (δ1 - δ1') % 2 = 0) (h2 : (δ2 - δ2') % 2 = 0) :
    qmono A Bq C d e δ1 δ2 = qmono A Bq C d e δ1' δ2' := by
  funext p
  simp only [qmono]
  congr 1
  obtain ⟨k1, hk1⟩ := Int.dvd_of_emod_eq_zero h1
  obtain ⟨k2, hk2⟩ := Int.dvd_of_emod_eq_zero h2
  have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
  rw [show δ1 * p.1 + δ2 * p.2 = (δ1' * p.1 + δ2' * p.2) + 2 * (k1 * p.1 + k2 * p.2) by
    linear_combination p.1 * hk1 + p.2 * hk2, zpow_add₀ hm, zpow_mul]
  norm_num

end Forty
