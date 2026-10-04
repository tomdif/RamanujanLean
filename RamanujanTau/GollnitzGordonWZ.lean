/-
# Göllnitz–Gordon, part 1: the inner identity of the `ρ = −q` Bailey step (base `q²`)

  `Σ_{i=0}^{N} (−q;q²)_{r+i} q^{2ri+i²} / ((q²;q²)_{N−i} (q²;q²)_i (q²;q²)_{2r+i}) = (−q;q²)_{r+N} / ((q²;q²)_N (q²;q²)_{2r+N})`,

proved by a WZ certificate (found with sympy): with `F` the summand divided by the right side,
`F(N+1,i) − F(N,i) = G(N,i+1) − G(N,i)`, `G(N,0) = 0`, `F(N+1,N+1) = −G(N,N+1)`, where
`G(N,i+1) = −q^{2(N−i)}/(1+q^{2(r+N)+1}) · (−q;q²)_{r+i+1} q^{2r(i+1)+(i+1)²}/((q²)_{N−i}(q²)_i(q²)_{2r+i}) · (…)⁻¹`.
-/
import RamanujanTau.FourSquaresWZ

set_option autoImplicit false

namespace GG
open PowerSeries Finset FourSquares

/-- `(q²;q²)_n`. -/
noncomputable def Qf (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range n, (1 - X ^ (2 * i + 2))
/-- `(−q;q²)_n`. -/
noncomputable def Mq (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range n, (1 + X ^ (2 * i + 1))

lemma Qf_succ (n : ℕ) : Qf (n + 1) = Qf n * (1 - X ^ (2 * n + 2)) := by rw [Qf, Qf, prod_range_succ]
lemma Mq_succ (n : ℕ) : Mq (n + 1) = Mq n * (1 + X ^ (2 * n + 1)) := by rw [Mq, Mq, prod_range_succ]
lemma Qf_zero : Qf 0 = 1 := by simp [Qf]
lemma Mq_zero : Mq 0 = 1 := by simp [Mq]

lemma isUnit_Qf (n : ℕ) : IsUnit (Qf n) := isUnit_of_cc (by rw [Qf, map_prod]; exact prod_eq_one fun i _ => by simp)
lemma isUnit_Mq (n : ℕ) : IsUnit (Mq n) := isUnit_of_cc (by rw [Mq, map_prod]; exact prod_eq_one fun i _ => by simp)

macro "unit_gg" : tactic =>
  `(tactic| repeat' (first | exact isUnit_Qf _ | exact isUnit_Mq _ | exact isUnit_one_add (by omega) | exact isUnit_one_sub (by omega) | apply IsUnit.mul | apply IsUnit.pow))

/-- the normalized summand. -/
noncomputable def Fg (r N i : ℕ) : PowerSeries ℤ :=
  Mq (r + i) * X ^ (2 * r * i + i ^ 2) * Ring.inverse (Qf (N - i) * Qf i * Qf (2 * r + i))
    * (Qf N * Qf (2 * r + N)) * Ring.inverse (Mq (r + N))

/-- the WZ certificate. -/
noncomputable def Gg (r N : ℕ) : ℕ → PowerSeries ℤ
  | 0 => 0
  | i + 1 => -X ^ (2 * (N - i)) * Ring.inverse (1 + X ^ (2 * (r + N) + 1)) * Mq (r + i + 1)
      * X ^ (2 * r * (i + 1) + (i + 1) ^ 2) * Ring.inverse (Qf (N - i) * Qf i * Qf (2 * r + i))
      * (Qf N * Qf (2 * r + N)) * Ring.inverse (Mq (r + N))

lemma core_zero {K : Type*} [Field K] (x c u p1 p2 p3 m1 m2 : K) (hx : x ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0)
    (hp3 : p3 ≠ 0) (hm1 : m1 ≠ 0) (h1 : 1 - u ^ 2 * x ^ 2 ≠ 0) (h2 : 1 - c ^ 4 * u ^ 2 * x ^ 2 ≠ 0)
    (h3 : 1 + c ^ 2 * u ^ 2 * x ≠ 0) :
    m2 * (p1 * (1 - u ^ 2 * x ^ 2) * p3)⁻¹ * (p1 * (1 - u ^ 2 * x ^ 2) * (p2 * (1 - c ^ 4 * u ^ 2 * x ^ 2)))
        * (m1 * (1 + c ^ 2 * u ^ 2 * x))⁻¹ - m2 * (p1 * p3)⁻¹ * (p1 * p2) * m1⁻¹
      = -u ^ 2 * (1 + c ^ 2 * u ^ 2 * x)⁻¹ * (m2 * (1 + c ^ 2 * x)) * (c ^ 2 * x) * (p1 * p3)⁻¹ * (p1 * p2) * m1⁻¹ := by
  generalize hB : c ^ 4 * u ^ 2 * x ^ 2 = B at *
  generalize hC : c ^ 2 * u ^ 2 * x = C at *
  generalize hA : u ^ 2 * x ^ 2 = A at *
  field_simp
  subst hA hB hC
  ring

/-- WZ step at `i = 0`. -/
lemma wz_zero (r N : ℕ) : Fg r (N + 1) 0 - Fg r N 0 = Gg r N 1 := by
  apply φ_inj
  have hx : φ (X : PowerSeries ℤ) ≠ 0 := fun h => X_ne_zero (φ_inj (h.trans (map_zero φ).symm))
  have h1 := φ_ne (isUnit_one_sub (m := 2 * N + 2) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + N) + 2) (by omega))
  have h3 := φ_ne (isUnit_one_add (m := 2 * (r + N) + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2 h3
  have hc := core_zero (φ X) (φ X ^ r) (φ X ^ N) (φ (Qf N)) (φ (Qf (2 * r + N))) (φ (Qf (2 * r)))
    (φ (Mq (r + N))) (φ (Mq r)) hx (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _))
    (φ_ne (isUnit_Mq _)) (by convert h1 using 2; ring) (by convert h2 using 2; ring) (by convert h3 using 2; ring)
  simp only [Fg, Gg, Nat.sub_zero, add_zero, mul_zero, pow_zero, mul_one, Qf_zero,
    show r + (N + 1) = r + N + 1 by ring, show 2 * r + (N + 1) = 2 * r + N + 1 by ring, Qf_succ, Mq_succ]
  simp (disch := unit_gg) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  linear_combination hc


lemma core_succ {K : Type*} [Field K] (x c b a P pd pi pri pN prN mri mrN : K) (hx : x ≠ 0)
    (hpd : pd ≠ 0) (hpi : pi ≠ 0) (hpri : pri ≠ 0) (hpN : pN ≠ 0) (hprN : prN ≠ 0) (hmri : mri ≠ 0) (hmrN : mrN ≠ 0)
    (h1 : 1 - a ^ 2 * x ^ 2 ≠ 0) (h2 : 1 - b ^ 2 * x ^ 2 ≠ 0) (h3 : 1 - c ^ 4 * b ^ 2 * x ^ 2 ≠ 0)
    (h4 : 1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 3 ≠ 0) (h5 : 1 + c ^ 2 * b ^ 2 * x ≠ 0) :
    mri * (1 + c ^ 2 * b ^ 2 * x) * (P * c ^ 2 * b ^ 2 * x)
        * (pd * (1 - a ^ 2 * x ^ 2) * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 2)))⁻¹
        * (pN * (1 - b ^ 2 * a ^ 2 * x ^ 4) * (prN * (1 - c ^ 4 * b ^ 2 * a ^ 2 * x ^ 4)))
        * (mrN * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 3))⁻¹
      - mri * (1 + c ^ 2 * b ^ 2 * x) * (P * c ^ 2 * b ^ 2 * x)
        * (pd * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 2)))⁻¹ * (pN * prN) * mrN⁻¹
    = -a ^ 2 * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 3)⁻¹ * (mri * (1 + c ^ 2 * b ^ 2 * x) * (1 + c ^ 2 * b ^ 2 * x ^ 3))
        * (P * c ^ 4 * b ^ 4 * x ^ 4) * (pd * (pi * (1 - b ^ 2 * x ^ 2)) * (pri * (1 - c ^ 4 * b ^ 2 * x ^ 2)))⁻¹
        * (pN * prN) * mrN⁻¹
      - -(a ^ 2 * x ^ 2) * (1 + c ^ 2 * b ^ 2 * a ^ 2 * x ^ 3)⁻¹ * (mri * (1 + c ^ 2 * b ^ 2 * x))
        * (P * c ^ 2 * b ^ 2 * x) * (pd * (1 - a ^ 2 * x ^ 2) * pi * pri)⁻¹ * (pN * prN) * mrN⁻¹ := by
  generalize hD : c ^ 2 * b ^ 2 * a ^ 2 * x ^ 3 = D at *
  generalize hE : c ^ 4 * b ^ 2 * x ^ 2 = E at *
  generalize hF : c ^ 2 * b ^ 2 * x = F at *
  generalize hA : a ^ 2 * x ^ 2 = A at *
  generalize hB : b ^ 2 * x ^ 2 = B at *
  field_simp
  subst hA hB hD hE hF
  ring

/-- WZ step at `i = i' + 1` (with `N = i' + 1 + d`). -/
lemma wz_succ (r i d : ℕ) :
    Fg r (i + 1 + d + 1) (i + 1) - Fg r (i + 1 + d) (i + 1) = Gg r (i + 1 + d) (i + 1 + 1) - Gg r (i + 1 + d) (i + 1) := by
  apply φ_inj
  have hx : φ (X : PowerSeries ℤ) ≠ 0 := fun h => X_ne_zero (φ_inj (h.trans (map_zero φ).symm))
  have h1 := φ_ne (isUnit_one_sub (m := 2 * d + 2) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := 2 * i + 2) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + i) + 2) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := 2 * (r + (i + 1 + d)) + 1) (by omega))
  have h5 := φ_ne (isUnit_one_add (m := 2 * (r + i) + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2 h3 h4 h5
  have hc := core_succ (φ X) (φ X ^ r) (φ X ^ i) (φ X ^ d) (φ X ^ (2 * r * i + i ^ 2))
    (φ (Qf d)) (φ (Qf i)) (φ (Qf (2 * r + i))) (φ (Qf (i + 1 + d))) (φ (Qf (2 * r + (i + 1 + d))))
    (φ (Mq (r + i))) (φ (Mq (r + (i + 1 + d)))) hx (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _))
    (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Qf _)) (φ_ne (isUnit_Mq _)) (φ_ne (isUnit_Mq _))
    (by convert h1 using 2; ring) (by convert h2 using 2; ring) (by convert h3 using 2; ring)
    (by convert h4 using 2; ring) (by convert h5 using 2; ring)
  simp only [Fg, Gg, show i + 1 + d + 1 - (i + 1) = d + 1 by omega, show i + 1 + d - (i + 1) = d by omega,
    show i + 1 + d - i = d + 1 by omega, show r + (i + 1 + d + 1) = r + (i + 1 + d) + 1 by ring,
    show 2 * r + (i + 1 + d + 1) = 2 * r + (i + 1 + d) + 1 by ring, show r + (i + 1) + 1 = r + (i + 1) + 1 from rfl,
    show r + (i + 1) = r + i + 1 by ring, show 2 * r + (i + 1) = 2 * r + i + 1 by ring, Qf_succ, Mq_succ]
  simp (disch := unit_gg) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  linear_combination hc

/-- boundary: `F(N+1,N+1) = −G(N,N+1)`. -/
lemma wz_end (r N : ℕ) : Fg r (N + 1) (N + 1) = -Gg r N (N + 1) := by
  apply φ_inj
  have h4 := φ_ne (isUnit_one_add (m := 2 * (r + N) + 1) (by omega))
  simp only [Fg, Gg, Nat.sub_self, Qf_zero, pow_zero, show r + (N + 1) = r + N + 1 by ring,
    show 2 * r + (N + 1) = 2 * r + N + 1 by ring, Mq_succ, Qf_succ, mul_zero, one_mul]
  simp (disch := unit_gg) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  have hq1 := φ_ne (isUnit_Qf N)
  have hq2 := φ_ne (isUnit_Qf (2 * r + N))
  have hm := φ_ne (isUnit_Mq (r + N))
  have hs1 := φ_ne (isUnit_one_sub (m := 2 * N + 2) (by omega))
  have hs2 := φ_ne (isUnit_one_sub (m := 2 * (2 * r + N) + 2) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h4 hs1 hs2
  generalize φ (Qf N) = p1 at *
  generalize φ (Qf (2 * r + N)) = p2 at *
  generalize φ (Mq (r + N)) = m at *
  generalize φ X ^ (2 * r * (N + 1) + (N + 1) ^ 2) = T at *
  generalize φ X ^ (2 * (r + N) + 1) = w at *
  generalize φ X ^ (2 * N + 2) = s1 at *
  generalize φ X ^ (2 * (2 * r + N) + 2) = s2 at *
  field_simp

/-- the normalized sum is `1`. -/
theorem Sg_eq_one (r N : ℕ) : ∑ i ∈ range (N + 1), Fg r N i = 1 := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Fg, Nat.sub_zero, Qf_zero, pow_zero, mul_zero, add_zero]
    have h1 := Ring.mul_inverse_cancel _ (isUnit_Qf (2 * r))
    have h2 := Ring.mul_inverse_cancel _ (isUnit_Mq r)
    simp only [one_mul, mul_one]
    linear_combination (Mq r * Ring.inverse (Mq r)) * h1 + h2
  | succ N ih =>
    rw [sum_range_succ, wz_end]
    have hT : ∀ i ∈ range (N + 1), Fg r (N + 1) i = Fg r N i + (Gg r N (i + 1) - Gg r N i) := by
      intro i hi
      rw [mem_range] at hi
      rcases i with _ | i
      · have := wz_zero r N
        rw [show Gg r N 0 = 0 from rfl]
        linear_combination this
      · obtain ⟨d, rfl⟩ : ∃ d, N = i + 1 + d := ⟨N - (i + 1), by omega⟩
        have := wz_succ r i d; linear_combination this
    rw [sum_congr rfl hT, sum_add_distrib, ih, sum_range_sub (fun i => Gg r N i), Gg]
    ring

/-- **the inner identity**. -/
theorem inner_gg (r N : ℕ) :
    ∑ i ∈ range (N + 1), Mq (r + i) * X ^ (2 * r * i + i ^ 2) * Ring.inverse (Qf (N - i) * Qf i * Qf (2 * r + i))
      = Mq (r + N) * Ring.inverse (Qf N * Qf (2 * r + N)) := by
  have h := Sg_eq_one r N
  simp only [Fg] at h
  rw [← sum_mul, ← sum_mul] at h
  have hK : Qf N * Qf (2 * r + N) * Ring.inverse (Mq (r + N)) * (Mq (r + N) * Ring.inverse (Qf N * Qf (2 * r + N))) = 1 := by
    have h1 := Ring.mul_inverse_cancel _ ((isUnit_Qf N).mul (isUnit_Qf (2 * r + N)))
    have h2 := Ring.inverse_mul_cancel _ (isUnit_Mq (r + N))
    linear_combination (Ring.inverse (Mq (r + N)) * Mq (r + N)) * h1 + h2
  set S := ∑ i ∈ range (N + 1), Mq (r + i) * X ^ (2 * r * i + i ^ 2) * Ring.inverse (Qf (N - i) * Qf i * Qf (2 * r + i))
  calc S = S * (Qf N * Qf (2 * r + N) * Ring.inverse (Mq (r + N)) * (Mq (r + N) * Ring.inverse (Qf N * Qf (2 * r + N)))) := by
        rw [hK, mul_one]
    _ = (S * (Qf N * Qf (2 * r + N)) * Ring.inverse (Mq (r + N))) * (Mq (r + N) * Ring.inverse (Qf N * Qf (2 * r + N))) := by ring
    _ = Mq (r + N) * Ring.inverse (Qf N * Qf (2 * r + N)) := by rw [h, one_mul]

end GG
