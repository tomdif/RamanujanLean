/-
# Göllnitz–Gordon, part 3: the inner identity for `a = q²`, `ρ = −q` (base `q²`)

  `Σ_{i=0}^{N} (−q;q²)_{r+i} q^{2ri+i²+2i} / ((q²;q²)_{N−i} (q²;q²)_i (q⁴;q²)_{2r+i})
      = (−q;q²)_r (−q³;q²)_{r+N} / ((−q³;q²)_r (q²;q²)_N (q⁴;q²)_{2r+N})`,

by the WZ certificate `R = q²x(y−1)(q²yz²−1)/((q²x−y)(q³xz+1))` (`x = q^{2N}`, `y = q^{2i}`, `z = q^{2r}`).
-/
import RamanujanTau.GollnitzGordonWZ

set_option autoImplicit false

namespace GG
open PowerSeries Finset FourSquares

/-- `(q⁴;q²)_n`. -/
noncomputable def Q2 (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range n, (1 - X ^ (2 * i + 4))
/-- `(−q³;q²)_n`. -/
noncomputable def M3 (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range n, (1 + X ^ (2 * i + 3))

lemma Q2_succ (n : ℕ) : Q2 (n + 1) = Q2 n * (1 - X ^ (2 * n + 4)) := by rw [Q2, Q2, prod_range_succ]
lemma M3_succ (n : ℕ) : M3 (n + 1) = M3 n * (1 + X ^ (2 * n + 3)) := by rw [M3, M3, prod_range_succ]
lemma Q2_zero : Q2 0 = 1 := by simp [Q2]
lemma M3_zero : M3 0 = 1 := by simp [M3]
lemma isUnit_Q2 (n : ℕ) : IsUnit (Q2 n) := isUnit_of_cc (by rw [Q2, map_prod]; exact prod_eq_one fun i _ => by simp)
lemma isUnit_M3 (n : ℕ) : IsUnit (M3 n) := isUnit_of_cc (by rw [M3, map_prod]; exact prod_eq_one fun i _ => by simp)

macro "unit_gg2" : tactic =>
  `(tactic| repeat' (first | exact isUnit_Qf _ | exact isUnit_Mq _ | exact isUnit_Q2 _ | exact isUnit_M3 _ | exact isUnit_one_add (by omega) | exact isUnit_one_sub (by omega) | apply IsUnit.mul | apply IsUnit.pow))

noncomputable def Fh (r N i : ℕ) : PowerSeries ℤ :=
  Mq (r + i) * X ^ (2 * r * i + i ^ 2 + 2 * i) * Ring.inverse (Qf (N - i) * Qf i * Q2 (2 * r + i))
    * (Qf N * Q2 (2 * r + N)) * M3 r * Ring.inverse (Mq r * M3 (r + N))

noncomputable def Gh (r N : ℕ) : ℕ → PowerSeries ℤ
  | 0 => 0
  | i + 1 => -X ^ (2 * (N - i)) * Ring.inverse (1 + X ^ (2 * (r + N) + 3)) * Mq (r + i + 1)
      * X ^ (2 * r * (i + 1) + (i + 1) ^ 2 + 2 * (i + 1)) * Ring.inverse (Qf (N - i) * Qf i * Q2 (2 * r + i))
      * (Qf N * Q2 (2 * r + N)) * M3 r * Ring.inverse (Mq r * M3 (r + N))

lemma core2_zero {K : Type*} [Field K] (x c u p1 p2 p3 m m3 mN : K) (hx : x ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0)
    (hp3 : p3 ≠ 0) (hm : m ≠ 0) (hmN : mN ≠ 0) (h1 : 1 - u ^ 2 * x ^ 2 ≠ 0) (h2 : 1 - c ^ 4 * u ^ 2 * x ^ 4 ≠ 0)
    (h3 : 1 + c ^ 2 * u ^ 2 * x ^ 3 ≠ 0) :
    m * (p1 * (1 - u ^ 2 * x ^ 2) * p3)⁻¹ * (p1 * (1 - u ^ 2 * x ^ 2) * (p2 * (1 - c ^ 4 * u ^ 2 * x ^ 4))) * m3
        * (m * (mN * (1 + c ^ 2 * u ^ 2 * x ^ 3)))⁻¹ - m * (p1 * p3)⁻¹ * (p1 * p2) * m3 * (m * mN)⁻¹
      = -u ^ 2 * (1 + c ^ 2 * u ^ 2 * x ^ 3)⁻¹ * (m * (1 + c ^ 2 * x)) * (c ^ 2 * x ^ 3) * (p1 * p3)⁻¹
        * (p1 * p2) * m3 * (m * mN)⁻¹ := by
  generalize hB : c ^ 4 * u ^ 2 * x ^ 4 = B at *
  generalize hC : c ^ 2 * u ^ 2 * x ^ 3 = C at *
  generalize hA : u ^ 2 * x ^ 2 = A at *
  field_simp
  subst hA hB hC
  ring

lemma wz2_zero (r N : ℕ) : Fh r (N + 1) 0 - Fh r N 0 = Gh r N 1 := by
  apply φ_inj
  have hx : φ (X : PowerSeries ℤ) ≠ 0 := fun h => X_ne_zero (φ_inj (h.trans (map_zero φ).symm))
  have h1 := φ_ne (isUnit_one_sub (m := 2 * N + 2) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + N) + 4) (by omega))
  have h3 := φ_ne (isUnit_one_add (m := 2 * (r + N) + 3) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2 h3
  have hc := core2_zero (φ X) (φ X ^ r) (φ X ^ N) (φ (Qf N)) (φ (Q2 (2 * r + N))) (φ (Q2 (2 * r)))
    (φ (Mq r)) (φ (M3 r)) (φ (M3 (r + N))) hx (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Q2 _)) (φ_ne (isUnit_Q2 _))
    (φ_ne (isUnit_Mq _)) (φ_ne (isUnit_M3 _)) (by convert h1 using 2; ring) (by convert h2 using 2; ring)
    (by convert h3 using 2; ring)
  simp only [Fh, Gh, Nat.sub_zero, add_zero, mul_zero, pow_zero, mul_one, Qf_zero,
    show r + (N + 1) = r + N + 1 by ring, show 2 * r + (N + 1) = 2 * r + N + 1 by ring, Qf_succ, Q2_succ, M3_succ,
    Mq_succ]
  simp (disch := unit_gg2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  linear_combination hc


lemma core2_succ {K : Type*} [Field K] (x c b a P pd pi pri pN prN mri m m3 mN : K) (hx : x ≠ 0)
    (hpd : pd ≠ 0) (hpi : pi ≠ 0) (hpri : pri ≠ 0) (hpN : pN ≠ 0) (hprN : prN ≠ 0) (hm : m ≠ 0) (hmN : mN ≠ 0)
    (h1 : 1 - a ^ 2 * x ^ 2 ≠ 0) (h2 : 1 - b ^ 2 * x ^ 2 ≠ 0) (h3 : 1 - c ^ 4 * b ^ 2 * x ^ 4 ≠ 0)
    (h4 : 1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 5 ≠ 0) :
    mri * (1 + c ^ 2 * b ^ 2 * x) * (P * c ^ 2 * b ^ 2 * x ^ 3)
        * (pd * (1 - a ^ 2 * x ^ 2) * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 4)))⁻¹
        * (pN * (1 - b ^ 2 * a ^ 2 * x ^ 4) * (prN * (1 - c ^ 4 * b ^ 2 * a ^ 2 * x ^ 6))) * m3
        * (m * (mN * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 5)))⁻¹
      - mri * (1 + c ^ 2 * b ^ 2 * x) * (P * c ^ 2 * b ^ 2 * x ^ 3)
        * (pd * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 4)))⁻¹ * (pN * prN) * m3 * (m * mN)⁻¹
    = -a ^ 2 * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 5)⁻¹ * (mri * (1 + c ^ 2 * b ^ 2 * x) * (1 + c ^ 2 * b ^ 2 * x ^ 3))
        * (P * c ^ 4 * b ^ 4 * x ^ 8) * (pd * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 4)))⁻¹
        * (pN * prN) * m3 * (m * mN)⁻¹
      - -(a ^ 2 * x ^ 2) * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 5)⁻¹ * (mri * (1 + c ^ 2 * b ^ 2 * x))
        * (P * c ^ 2 * b ^ 2 * x ^ 3) * (pd * (1 - a ^ 2 * x ^ 2) * pi * pri)⁻¹ * (pN * prN) * m3 * (m * mN)⁻¹ := by
  generalize hD : c ^ 2 * b ^ 2 * a ^ 2 * x ^ 5 = D at *
  generalize hE : c ^ 4 * b ^ 2 * x ^ 4 = E at *
  generalize hA : a ^ 2 * x ^ 2 = A at *
  generalize hB : b ^ 2 * x ^ 2 = B at *
  field_simp
  subst hA hB hD hE
  ring

lemma wz2_succ (r i d : ℕ) :
    Fh r (i + 1 + d + 1) (i + 1) - Fh r (i + 1 + d) (i + 1) = Gh r (i + 1 + d) (i + 1 + 1) - Gh r (i + 1 + d) (i + 1) := by
  apply φ_inj
  have hx : φ (X : PowerSeries ℤ) ≠ 0 := fun h => X_ne_zero (φ_inj (h.trans (map_zero φ).symm))
  have h1 := φ_ne (isUnit_one_sub (m := 2 * d + 2) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := 2 * i + 2) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + i) + 4) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := 2 * (r + (i + 1 + d)) + 3) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2 h3 h4
  have hc := core2_succ (φ X) (φ X ^ r) (φ X ^ i) (φ X ^ d) (φ X ^ (2 * r * i + i ^ 2 + 2 * i))
    (φ (Qf d)) (φ (Qf i)) (φ (Q2 (2 * r + i))) (φ (Qf (i + 1 + d))) (φ (Q2 (2 * r + (i + 1 + d))))
    (φ (Mq (r + i))) (φ (Mq r)) (φ (M3 r)) (φ (M3 (r + (i + 1 + d)))) hx (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _))
    (φ_ne (isUnit_Q2 _)) (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Q2 _)) (φ_ne (isUnit_Mq _)) (φ_ne (isUnit_M3 _))
    (by convert h1 using 2; ring) (by convert h2 using 2; ring) (by convert h3 using 2; ring)
    (by convert h4 using 2; ring)
  simp only [Fh, Gh, show i + 1 + d + 1 - (i + 1) = d + 1 by omega, show i + 1 + d - (i + 1) = d by omega,
    show i + 1 + d - i = d + 1 by omega, show r + (i + 1 + d + 1) = r + (i + 1 + d) + 1 by ring,
    show 2 * r + (i + 1 + d + 1) = 2 * r + (i + 1 + d) + 1 by ring,
    show r + (i + 1) = r + i + 1 by ring, show 2 * r + (i + 1) = 2 * r + i + 1 by ring, Qf_succ, Q2_succ, Mq_succ,
    M3_succ]
  simp (disch := unit_gg2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  linear_combination hc

lemma wz2_end (r N : ℕ) : Fh r (N + 1) (N + 1) = -Gh r N (N + 1) := by
  apply φ_inj
  simp only [Fh, Gh, Nat.sub_self, Qf_zero, pow_zero, show r + (N + 1) = r + N + 1 by ring,
    show 2 * r + (N + 1) = 2 * r + N + 1 by ring, Mq_succ, Qf_succ, Q2_succ, M3_succ, mul_zero, one_mul]
  simp (disch := unit_gg2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  have h4 := φ_ne (isUnit_one_add (m := 2 * (r + N) + 3) (by omega))
  have hq1 := φ_ne (isUnit_Qf N)
  have hq2 := φ_ne (isUnit_Q2 (2 * r + N))
  have hm := φ_ne (isUnit_Mq (r + N))
  have hm0 := φ_ne (isUnit_Mq r)
  have hm3 := φ_ne (isUnit_M3 (r + N))
  have hs1 := φ_ne (isUnit_one_sub (m := 2 * N + 2) (by omega))
  have hs2 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + N) + 4) (by omega))
  have hs3 := φ_ne (isUnit_one_add (m := 2 * (r + N) + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h4 hs1 hs2 hs3
  generalize φ (Qf N) = p1 at *
  generalize φ (Q2 (2 * r + N)) = p2 at *
  generalize φ (Mq (r + N)) = mm at *
  generalize φ (Mq r) = m0 at *
  generalize φ (M3 (r + N)) = m3 at *
  generalize φ X ^ (2 * r * (N + 1) + (N + 1) ^ 2 + 2 * (N + 1)) = T at *
  generalize φ X ^ (2 * (r + N) + 3) = w at *
  generalize φ X ^ (2 * (r + N) + 1) = v at *
  generalize φ X ^ (2 * N + 2) = s1 at *
  generalize φ X ^ (2 * (2 * r + N) + 4) = s2 at *
  field_simp

theorem Sh_eq_one (r N : ℕ) : ∑ i ∈ range (N + 1), Fh r N i = 1 := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Fh, Nat.sub_zero, Qf_zero, mul_zero, add_zero]
    have h1 := Ring.mul_inverse_cancel _ (isUnit_Q2 (2 * r))
    have h2 := Ring.mul_inverse_cancel _ ((isUnit_Mq r).mul (isUnit_M3 r))
    simp only [one_mul, mul_one, pow_zero]
    linear_combination (Mq r * M3 r * Ring.inverse (Mq r * M3 r)) * h1 + h2
  | succ N ih =>
    rw [sum_range_succ, wz2_end]
    have hT : ∀ i ∈ range (N + 1), Fh r (N + 1) i = Fh r N i + (Gh r N (i + 1) - Gh r N i) := by
      intro i hi
      rw [mem_range] at hi
      rcases i with _ | i
      · have := wz2_zero r N
        rw [show Gh r N 0 = 0 from rfl]
        linear_combination this
      · obtain ⟨d, rfl⟩ : ∃ d, N = i + 1 + d := ⟨N - (i + 1), by omega⟩
        have := wz2_succ r i d; linear_combination this
    rw [sum_congr rfl hT, sum_add_distrib, ih, sum_range_sub (fun i => Gh r N i), Gh]
    ring

/-- **the inner identity for `a = q²`**. -/
theorem inner_gg2 (r N : ℕ) :
    ∑ i ∈ range (N + 1), Mq (r + i) * X ^ (2 * r * i + i ^ 2 + 2 * i) * Ring.inverse (Qf (N - i) * Qf i * Q2 (2 * r + i))
      = Mq r * M3 (r + N) * Ring.inverse (M3 r * (Qf N * Q2 (2 * r + N))) := by
  have h := Sh_eq_one r N
  simp only [Fh] at h
  rw [← sum_mul, ← sum_mul, ← sum_mul] at h
  set S := ∑ i ∈ range (N + 1), Mq (r + i) * X ^ (2 * r * i + i ^ 2 + 2 * i) * Ring.inverse (Qf (N - i) * Qf i * Q2 (2 * r + i))
  have hK : Qf N * Q2 (2 * r + N) * M3 r * Ring.inverse (Mq r * M3 (r + N))
      * (Mq r * M3 (r + N) * Ring.inverse (M3 r * (Qf N * Q2 (2 * r + N)))) = 1 := by
    have h1 := Ring.mul_inverse_cancel _ ((isUnit_M3 r).mul ((isUnit_Qf N).mul (isUnit_Q2 (2 * r + N))))
    have h2 := Ring.inverse_mul_cancel _ ((isUnit_Mq r).mul (isUnit_M3 (r + N)))
    linear_combination (Ring.inverse (Mq r * M3 (r + N)) * (Mq r * M3 (r + N))) * h1 + h2
  calc S = S * (Qf N * Q2 (2 * r + N) * M3 r * Ring.inverse (Mq r * M3 (r + N))
        * (Mq r * M3 (r + N) * Ring.inverse (M3 r * (Qf N * Q2 (2 * r + N))))) := by rw [hK, mul_one]
    _ = (S * (Qf N * Q2 (2 * r + N)) * M3 r * Ring.inverse (Mq r * M3 (r + N)))
        * (Mq r * M3 (r + N) * Ring.inverse (M3 r * (Qf N * Q2 (2 * r + N)))) := by ring
    _ = _ := by rw [h, one_mul]

end GG
