/-
# Matrix exact covering systems and products of theta functions

The engine behind the "Type I / Type II" proofs of Ramanujan's forty identities (Z. Cao, *Quadratic forms,
exact covering systems, and product identities for theta functions*, arXiv:2503.11445, Thm 3.1):

* `ECS` — an integer matrix `B = (b₁₁ b₁₂; b₂₁ b₂₂)` with `det B ≠ 0` and a finite set `I` of shifts such that
  `ℤ² = ⨆_{i ∈ I} (B ℤ² + (i, 0))` (exact cover; `cover` + `uniq`).
* `hs_split` — if a summable family `P` over `ℤ²` satisfies `P (B w + (i,0)) = a i · E i w`, then
  `Σ P = Σ_{i ∈ I} a i · Σ E i`.
* `θθ_lattice` — the case `P = θ_{N₁}(e₁,c₁) ⊗ θ_{N₂}(e₂,c₂)` with `N₁ b₁₁ b₁₂ + N₂ b₂₁ b₂₂ = 0`:
  `θ_{N₁}(e₁,c₁) θ_{N₂}(e₂,c₂) = Σ_{i∈I} c₁ⁱ(−1)ⁱ t^{N₁C(i,2)+e₁i} θ_{M₁}(f₁ᵢ, d₁) θ_{M₂}(f₂ᵢ, d₂)`,
  `M₁ = N₁b₁₁² + N₂b₂₁²`, `M₂ = N₁b₁₂² + N₂b₂₂²`.

Here `θ_N(e, c) = Σ_k (−1)^k c^k t^{N C(k,2) + e k}` (`ALz.θ`), i.e. Ramanujan's `f(−c tᵉ, −c⁻¹ t^{N−e})`.
-/
import RamanujanTau.ALBase

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset

/-- a matrix exact covering system of `ℤ²` by the cosets `B ℤ² + (i, 0)`, `i ∈ I`. -/
structure ECS where
  b11 : ℤ
  b12 : ℤ
  b21 : ℤ
  b22 : ℤ
  /-- the shift direction `(r₁, r₂)`: cosets are `B ℤ² + i (r₁, r₂)`. -/
  r1 : ℤ
  r2 : ℤ
  I : Finset ℤ
  det_ne : b11 * b22 - b12 * b21 ≠ 0
  cover : ∀ m n : ℤ, ∃ i ∈ I, ∃ u v : ℤ, m = b11 * u + b12 * v + r1 * i ∧ n = b21 * u + b22 * v + r2 * i
  uniq : ∀ i ∈ I, ∀ j ∈ I, ∀ u v u' v' : ℤ,
    b11 * u + b12 * v + r1 * i = b11 * u' + b12 * v' + r1 * j →
      b21 * u + b22 * v + r2 * i = b21 * u' + b22 * v' + r2 * j → i = j

namespace ECS
variable (B : ECS)

/-- the coset map `(u, v) ↦ B (u, v) + i (r₁, r₂)`. -/
def cmap (i : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (B.b11 * p.1 + B.b12 * p.2 + B.r1 * i, B.b21 * p.1 + B.b22 * p.2 + B.r2 * i)

lemma cmap_inj (i : ℤ) : Function.Injective (B.cmap i) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [cmap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hd := B.det_ne
  have e1 : (B.b11 * B.b22 - B.b12 * B.b21) * (u - u') = 0 := by linear_combination B.b22 * h1 - B.b12 * h2
  have e2 : (B.b11 * B.b22 - B.b12 * B.b21) * (v - v') = 0 := by linear_combination B.b11 * h2 - B.b21 * h1
  rcases mul_eq_zero.mp e1 with h | h
  · exact absurd h hd
  rcases mul_eq_zero.mp e2 with h' | h'
  · exact absurd h' hd
  rw [Prod.mk.injEq]; omega

/-- the coset embedding. -/
def emb (i : ℤ) : ℤ × ℤ ↪ ℤ × ℤ := ⟨B.cmap i, B.cmap_inj i⟩

lemma emb_apply (i : ℤ) (p : ℤ × ℤ) : B.emb i p = B.cmap i p := rfl

end ECS

section Split
variable (B : ECS)

lemma fam_sum_apply {ι : Type*} (s : Finset ι) (f : ι → SummableFamily ℤ ℂ (ℤ × ℤ)) (p : ℤ × ℤ) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SummableFamily.zero_apply]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, SummableFamily.add_apply, ih]

/-- the split family `Σ_{i∈I} a i • (E i ∘ coset⁻¹)`. -/
noncomputable def splitFam (a : ℤ → L) (E : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ)) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ∑ i ∈ B.I, a i • (E i).embDomain (B.emb i)

theorem hs_splitFam (a : ℤ → L) (E : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ)) :
    hs (splitFam B a E) = ∑ i ∈ B.I, a i * hs (E i) := by
  unfold splitFam
  induction B.I using Finset.induction_on with
  | empty => simp [hs, SummableFamily.hsum_zero]
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj, ← ih, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_add,
      SummableFamily.hsum_smul, SummableFamily.hsum_embDomain]

/-- evaluation of the split family through a formula `F`. -/
theorem splitFam_apply (a : ℤ → L) (E : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ)) (F : ℤ × ℤ → L)
    (hF : ∀ i ∈ B.I, ∀ w, F (B.cmap i w) = a i * E i w) (p : ℤ × ℤ) : splitFam B a E p = F p := by
  obtain ⟨i, hi, u, v, hm, hn⟩ := B.cover p.1 p.2
  have hp : p = B.emb i (u, v) := by
    rw [ECS.emb_apply, ECS.cmap]; ext <;> simp [hm, hn]
  rw [splitFam, fam_sum_apply, hp, sum_eq_single i]
  · rw [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, SummableFamily.embDomain_image,
      ECS.emb_apply, hF i hi]
  · intro j hj hji
    rw [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, SummableFamily.embDomain_notin_range,
      mul_zero]
    rintro ⟨⟨u', v'⟩, h⟩
    simp only [ECS.emb_apply, ECS.cmap, Prod.mk.injEq] at h
    exact hji (B.uniq j hj i hi u' v' u v h.1 h.2)
  · intro h; exact absurd hi h

/-- **the split**: a family given by `F` on every coset sums to `Σ a i · Σ E i`. -/
theorem hs_split (P : SummableFamily ℤ ℂ (ℤ × ℤ)) (a : ℤ → L) (E : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ))
    (hP : ∀ i ∈ B.I, ∀ w, P (B.cmap i w) = a i * E i w) : hs P = ∑ i ∈ B.I, a i * hs (E i) := by
  rw [← hs_splitFam B a E]
  congr 1
  ext p : 1
  rw [splitFam_apply B a E P hP]

/-- two exact covers of the same formula give the same sum (Cao's "Type II"). -/
theorem split_two (B' : ECS) (F : ℤ × ℤ → L) (a a' : ℤ → L) (E E' : ℤ → SummableFamily ℤ ℂ (ℤ × ℤ))
    (hF : ∀ i ∈ B.I, ∀ w, F (B.cmap i w) = a i * E i w) (hF' : ∀ i ∈ B'.I, ∀ w, F (B'.cmap i w) = a' i * E' i w) :
    ∑ i ∈ B.I, a i * hs (E i) = ∑ i ∈ B'.I, a' i * hs (E' i) := by
  rw [← hs_splitFam B a E, ← hs_split B' (splitFam B a E) a' E' fun i hi w => by
    rw [splitFam_apply B a E F hF, hF' i hi w]]

end Split

/-! ## Products of two thetas -/

section ThetaProd

lemma mono_ext_lat {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C = C') : (mono E C : L) = mono E' C' := by
  rw [hE, hC]

lemma θ_mul_hs {N1 N2 : ℕ} (h1 : 1 ≤ N1) (h2 : 1 ≤ N2) (e1 e2 : ℤ) (w1 w2 : ℂ) :
    θ h1 e1 w1 * θ h2 e2 w2 = hs ((thF h1 e1 w1).mul (thF h2 e2 w2)) := by
  unfold θ; rw [hs, hs, hs, SummableFamily.hsum_mul]

lemma neg_zpow_mul_self (K : ℂ) (u : ℤ) : ((-1 : ℂ)) ^ u * (-K) ^ u = K ^ u := by
  rw [neg_eq_neg_one_mul K, mul_zpow, ← mul_assoc, ← mul_zpow]; norm_num

/-- the theta coefficient identity behind `θθ_lattice`. -/
lemma lattice_coeff {w1 w2 : ℂ} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (b11 b12 b21 b22 i u v : ℤ) :
    thC w1 (b11 * u + b12 * v + i) * thC w2 (b21 * u + b22 * v) =
      ((-1) ^ i * w1 ^ i) * (thC (-((-1) ^ (b11 + b21) * w1 ^ b11 * w2 ^ b21)) u *
        thC (-((-1) ^ (b12 + b22) * w1 ^ b12 * w2 ^ b22)) v) := by
  have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
  unfold thC
  rw [neg_zpow_mul_self, neg_zpow_mul_self]
  simp only [mul_zpow, zpow_add₀ hm, zpow_add₀ hw1, zpow_add₀ hw2, ← zpow_mul]
  ring_nf

/-- **products of two thetas over a matrix exact cover** (Cao, Thm 3.1). -/
theorem θθ_lattice {N1 N2 M1 M2 : ℕ} (h1 : 1 ≤ N1) (h2 : 1 ≤ N2) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (e1 e2 : ℤ) {w1 w2 : ℂ} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (B : ECS)
    (hr1 : B.r1 = 1) (hr2 : B.r2 = 0) (horth : (N1 : ℤ) * B.b11 * B.b12 + N2 * B.b21 * B.b22 = 0)
    (hM1e : (M1 : ℤ) = N1 * B.b11 ^ 2 + N2 * B.b21 ^ 2) (hM2e : (M2 : ℤ) = N1 * B.b12 ^ 2 + N2 * B.b22 ^ 2) :
    θ h1 e1 w1 * θ h2 e2 w2 =
      ∑ i ∈ B.I, mono (N1 * c2 i + e1 * i) ((-1) ^ i * w1 ^ i) *
        (θ hM1 (N1 * c2 B.b11 + N2 * c2 B.b21 + N1 * B.b11 * i + e1 * B.b11 + e2 * B.b21)
            (-((-1) ^ (B.b11 + B.b21) * w1 ^ B.b11 * w2 ^ B.b21)) *
          θ hM2 (N1 * c2 B.b12 + N2 * c2 B.b22 + N1 * B.b12 * i + e1 * B.b12 + e2 * B.b22)
            (-((-1) ^ (B.b12 + B.b22) * w1 ^ B.b12 * w2 ^ B.b22))) := by
  rw [θ_mul_hs]
  simp_rw [θ_mul_hs]
  refine hs_split B _ _ _ fun i _ w => ?_
  obtain ⟨u, v⟩ := w
  simp only [ECS.cmap, SummableFamily.mul_toFun, thF, monoFam_apply, mono_mul, hr1, hr2, one_mul, zero_mul,
    add_zero]
  refine mono_ext_lat ?_ (lattice_coeff hw1 hw2 _ _ _ _ _ _ _)
  simp only [thE]
  have hx1 := two_c2 (B.b11 * u + B.b12 * v + i)
  have hx2 := two_c2 (B.b21 * u + B.b22 * v)
  have hi := two_c2 i
  have hu := two_c2 u
  have hv := two_c2 v
  have h11 := two_c2 B.b11
  have h12 := two_c2 B.b12
  have h21 := two_c2 B.b21
  have h22 := two_c2 B.b22
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  linear_combination (N1 : ℤ) * hx1 + (N2 : ℤ) * hx2 - (N1 : ℤ) * hi - (M1 : ℤ) * hu - (M2 : ℤ) * hv
    - u * (N1 : ℤ) * h11 - u * (N2 : ℤ) * h21 - v * (N1 : ℤ) * h12 - v * (N2 : ℤ) * h22
    + 2 * u * v * horth - (u * u - u) * hM1e - (v * v - v) * hM2e

end ThetaProd

/-! ## Binary quadratic forms (Cao's "Type II")

`qmono (A, Bq, C, d, e, δ₁, δ₂) (x₁, x₂) = (−1)^{δ₁x₁+δ₂x₂} t^{A x₁² + 2Bq x₁x₂ + C x₂² + d x₁ + e x₂}`.
On a coset `x = B (u,v) + i (r₁,r₂)` with `B` orthogonal for the form, it factors as a product of two theta terms. -/

section QF

/-- the terms of `Σ_{x ∈ ℤ²} (−1)^{δ·x} t^{Q(x)}`. -/
noncomputable def qmono (A Bq C d e δ1 δ2 : ℤ) (p : ℤ × ℤ) : L :=
  mono (A * p.1 ^ 2 + 2 * Bq * p.1 * p.2 + C * p.2 ^ 2 + d * p.1 + e * p.2) ((-1) ^ (δ1 * p.1 + δ2 * p.2))

variable (A Bq C d e δ1 δ2 : ℤ) (B : ECS)

/-- the `u`-exponent shift on the coset `i`. -/
def qf1 (i : ℤ) : ℤ := (A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2) +
  (2 * A * B.b11 * (B.r1 * i) + 2 * Bq * (B.b11 * (B.r2 * i) + B.b21 * (B.r1 * i)) + 2 * C * B.b21 * (B.r2 * i)
    + d * B.b11 + e * B.b21)

/-- the `v`-exponent shift on the coset `i`. -/
def qf2 (i : ℤ) : ℤ := (A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2) +
  (2 * A * B.b12 * (B.r1 * i) + 2 * Bq * (B.b12 * (B.r2 * i) + B.b22 * (B.r1 * i)) + 2 * C * B.b22 * (B.r2 * i)
    + d * B.b12 + e * B.b22)

/-- the constant term on the coset `i`. -/
def qf0 (i : ℤ) : ℤ := A * (B.r1 * i) ^ 2 + 2 * Bq * (B.r1 * i) * (B.r2 * i) + C * (B.r2 * i) ^ 2
  + d * (B.r1 * i) + e * (B.r2 * i)

lemma neg_one_zpow_add_one (k u : ℤ) : ((-1 : ℂ)) ^ (k * u) = (-1) ^ u * (-((-1) ^ k)) ^ u := by
  rw [neg_eq_neg_one_mul ((-1 : ℂ) ^ k), mul_zpow, ← mul_assoc, ← mul_zpow]
  norm_num
  rw [← zpow_mul, mul_comm]

theorem qf_term {M1 M2 : ℕ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (horth : A * B.b11 * B.b12 + Bq * (B.b11 * B.b22 + B.b12 * B.b21) + C * B.b21 * B.b22 = 0)
    (hM1e : (M1 : ℤ) = 2 * (A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2))
    (hM2e : (M2 : ℤ) = 2 * (A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2)) (i : ℤ) (w : ℤ × ℤ) :
    qmono A Bq C d e δ1 δ2 (B.cmap i w) =
      mono (qf0 A Bq C d e B i) ((-1) ^ (δ1 * (B.r1 * i) + δ2 * (B.r2 * i))) *
        ((thF hM1 (qf1 A Bq C d e B i) (-((-1) ^ (δ1 * B.b11 + δ2 * B.b21)))).mul
          (thF hM2 (qf2 A Bq C d e B i) (-((-1) ^ (δ1 * B.b12 + δ2 * B.b22))))) w := by
  obtain ⟨u, v⟩ := w
  simp only [qmono, ECS.cmap, SummableFamily.mul_toFun, thF, monoFam_apply, mono_mul, thE, thC]
  refine mono_ext_lat ?_ ?_
  · have hu := two_c2 u
    have hv := two_c2 v
    simp only [qf0, qf1, qf2]
    linear_combination (-(c2 u)) * hM1e + (-(c2 v)) * hM2e + (2 * u * v) * horth
      - (A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2) * hu
      - (A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2) * hv
  · have hm : ((-1 : ℂ)) ≠ 0 := by norm_num
    rw [← neg_one_zpow_add_one, ← neg_one_zpow_add_one, ← zpow_add₀ hm, ← zpow_add₀ hm]
    congr 1
    ring

/-- **two exact covers of one binary quadratic form** (Cao's Type II): both sides equal
`Σ_{x∈ℤ²} (−1)^{δ·x} t^{Q(x)}`. -/
theorem qf_two (B' : ECS) {M1 M2 M1' M2' : ℕ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM1' : 1 ≤ M1') (hM2' : 1 ≤ M2')
    (horth : A * B.b11 * B.b12 + Bq * (B.b11 * B.b22 + B.b12 * B.b21) + C * B.b21 * B.b22 = 0)
    (hM1e : (M1 : ℤ) = 2 * (A * B.b11 ^ 2 + 2 * Bq * B.b11 * B.b21 + C * B.b21 ^ 2))
    (hM2e : (M2 : ℤ) = 2 * (A * B.b12 ^ 2 + 2 * Bq * B.b12 * B.b22 + C * B.b22 ^ 2))
    (horth' : A * B'.b11 * B'.b12 + Bq * (B'.b11 * B'.b22 + B'.b12 * B'.b21) + C * B'.b21 * B'.b22 = 0)
    (hM1e' : (M1' : ℤ) = 2 * (A * B'.b11 ^ 2 + 2 * Bq * B'.b11 * B'.b21 + C * B'.b21 ^ 2))
    (hM2e' : (M2' : ℤ) = 2 * (A * B'.b12 ^ 2 + 2 * Bq * B'.b12 * B'.b22 + C * B'.b22 ^ 2)) :
    ∑ i ∈ B.I, mono (qf0 A Bq C d e B i) ((-1) ^ (δ1 * (B.r1 * i) + δ2 * (B.r2 * i))) *
        (θ hM1 (qf1 A Bq C d e B i) (-((-1) ^ (δ1 * B.b11 + δ2 * B.b21))) *
          θ hM2 (qf2 A Bq C d e B i) (-((-1) ^ (δ1 * B.b12 + δ2 * B.b22)))) =
      ∑ i ∈ B'.I, mono (qf0 A Bq C d e B' i) ((-1) ^ (δ1 * (B'.r1 * i) + δ2 * (B'.r2 * i))) *
        (θ hM1' (qf1 A Bq C d e B' i) (-((-1) ^ (δ1 * B'.b11 + δ2 * B'.b21))) *
          θ hM2' (qf2 A Bq C d e B' i) (-((-1) ^ (δ1 * B'.b12 + δ2 * B'.b22)))) := by
  simp_rw [θ_mul_hs]
  exact split_two B B' (qmono A Bq C d e δ1 δ2) _ _ _ _
    (fun i _ w => qf_term A Bq C d e δ1 δ2 B hM1 hM2 horth hM1e hM2e i w)
    (fun i _ w => qf_term A Bq C d e δ1 δ2 B' hM1' hM2' horth' hM1e' hM2e' i w)

end QF

end Forty
