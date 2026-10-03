/-
# The Appell–Lerch form of the rank generating function

`R(z;q) = Σ q^{n²}/((zq)_n(q/z)_n) = (1/(q)_∞)·Σ_r q^{r²} α_r`, with the Bailey pair (relative to `a = 1`)
  `β_n = 1/((zq)_n(q/z)_n)`,  `α_0 = 1`,
  `α_r = (−1)^r q^{r(r+1)/2}(1+q^r)(1−z)(1−z⁻¹)/((1−zq^r)(1−q^r/z))`,
i.e. `R(z;q) = (1/(q)_∞)(1 + Σ_{r≥1} (−1)^r q^{r(3r+1)/2}(1+q^r)(1−z)(1−z⁻¹)/((1−zq^r)(1−q^r/z)))`.
The finite pair is proved in any field by the telescoping certificate
  `G(n,s) = (−1)^{s+1} q^{n+1+C(s,2)}(1−z)(1−z⁻¹)·W_n/((1−q^{n+1})(q)_{n+1−s}(q)_{n+s})`.
-/
import RamanujanTau.RankBailey
import RamanujanTau.RankHR1

set_option autoImplicit false

namespace RankProof
open Finset

section ALFinite
variable {K : Type*} [Field K] (q z : K)

/-- `W_n = (zq)_n(q/z)_n`. -/
def Wn (n : ℕ) : K := ∏ i ∈ range n, ((1 - z * q ^ (i + 1)) * (1 - z⁻¹ * q ^ (i + 1)))

lemma Wn_succ (n : ℕ) : Wn q z (n + 1) = Wn q z n * ((1 - z * q ^ (n + 1)) * (1 - z⁻¹ * q ^ (n + 1))) := by
  rw [Wn, prod_range_succ]; rfl

/-- the `α` of the pair. -/
def alL (r : ℕ) : K :=
  if r = 0 then 1
  else (-1) ^ r * q ^ ((r + 1).choose 2) * (1 + q ^ r) * ((1 - z) * (1 - z⁻¹))
    / ((1 - z * q ^ r) * (1 - z⁻¹ * q ^ r))

/-- normalized terms `F(n,r) = α_r W_n/((q)_{n−r}(q)_{n+r})`. -/
def Fr (n r : ℕ) : K := alL q z r * Wn q z n / (P q (n - r) * P q (n + r))

/-- the certificate. -/
def Gc (n s : ℕ) : K :=
  if s = 0 then 0
  else (-1) ^ (s + 1) * q ^ (n + 1 + s.choose 2) * ((1 - z) * (1 - z⁻¹)) * Wn q z n
    / ((1 - q ^ (n + 1)) * P q (n + 1 - s) * P q (n + s))

end ALFinite

section ALLocal
variable {K : Type*} [Field K] {q z : K}

lemma al_mid (A B e sg p pp W : K) (hp : p ≠ 0) (hpp : pp ≠ 0) (hz : z ≠ 0)
    (h1 : 1 - A * q ≠ 0) (h2 : 1 - A * B * B * q ≠ 0) (h3 : 1 - A * B * q ≠ 0)
    (h4 : 1 - z * B ≠ 0) (h5 : z - B ≠ 0) :
    sg * e * B * (1 + B) * ((1 - z) * (1 - z⁻¹)) / ((1 - z * B) * (1 - z⁻¹ * B))
        * (W * ((1 - z * (A * B * q)) * (1 - z⁻¹ * (A * B * q)))) / (p * (1 - A * q) * (pp * (1 - A * B * B * q)))
      - sg * e * B * (1 + B) * ((1 - z) * (1 - z⁻¹)) / ((1 - z * B) * (1 - z⁻¹ * B)) * W / (p * pp)
      = sg * (A * B * q) * (e * B) * ((1 - z) * (1 - z⁻¹)) * W / ((1 - A * B * q) * p * (pp * (1 - A * B * B * q)))
        - -sg * (A * B * q) * e * ((1 - z) * (1 - z⁻¹)) * W / ((1 - A * B * q) * (p * (1 - A * q)) * pp) := by
  have hinv : ∀ t : K, 1 - z⁻¹ * t = (z - t) / z := fun t => by field_simp
  have h4' : 1 - B * z ≠ 0 := by rwa [mul_comm]
  have h2' : 1 - B ^ 2 * A * q ≠ 0 := by rwa [show B ^ 2 * A * q = A * B * B * q by ring]
  have h3' : 1 - B * A * q ≠ 0 := by rwa [show B * A * q = A * B * q by ring]
  have h5' : z - B ≠ 0 := h5
  simp only [hinv]
  field_simp
  ring

lemma al_bot (Q c p W : K) (hp : p ≠ 0) (hQ : 1 - Q ≠ 0) (hz : z ≠ 0) (hc : c = (1 - z) * (1 - z⁻¹)) :
    W * ((1 - z * Q) * (1 - z⁻¹ * Q)) / (p * (1 - Q) * (p * (1 - Q))) - W / (p * p)
      = Q * c * W / ((1 - Q) * p * (p * (1 - Q))) := by
  subst hc
  have hinv : ∀ t : K, 1 - z⁻¹ * t = (z - t) / z := fun t => by field_simp
  simp only [hinv]
  field_simp
  ring

lemma al_top (Q e sg c p W u v : K) (hp : p ≠ 0) (hQ : 1 - Q ≠ 0) (hQ' : 1 + Q ≠ 0)
    (h4 : u ≠ 0) (h5 : v ≠ 0) :
    -sg * (e * Q) * (1 + Q) * c / (u * v)
        * (W * (u * v)) / (1 * (p * ((1 - Q) * (1 + Q))))
      = -(sg * (Q * e) * c * W / ((1 - Q) * 1 * p)) := by
  field_simp

end ALLocal

section ALAssembly
variable {K : Type*} [Field K] {q z : K} (hq : ∀ i : ℕ, 1 - q ^ (i + 1) ≠ 0) (hz : z ≠ 0)
  (hzq : ∀ i : ℕ, 1 - z * q ^ (i + 1) ≠ 0) (hzq' : ∀ i : ℕ, z - q ^ (i + 1) ≠ 0)
include hq hz hzq hzq'

omit hq hz hzq hzq' in
lemma choose2_succ (r : ℕ) : (r + 1).choose 2 = r.choose 2 + r := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

omit hq hzq in
lemma hzq_inv (i : ℕ) : 1 - z⁻¹ * q ^ (i + 1) ≠ 0 := by
  intro h; apply hzq' i
  have : z - q ^ (i + 1) = z * (1 - z⁻¹ * q ^ (i + 1)) := by field_simp
  rw [this, h, mul_zero]

lemma al_mid_step (d r : ℕ) (hr : 1 ≤ r) :
    Fr q z (d + r + 1) r - Fr q z (d + r) r = Gc q z (d + r) (r + 1) - Gc q z (d + r) r := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  have hr0 : t + 1 ≠ 0 := by omega
  unfold Fr Gc alL
  rw [choose2_succ (t + 1),
    show d + (t + 1) + 1 - (t + 1) = d + 1 by omega, show d + (t + 1) - (t + 1) = d by omega,
    show d + (t + 1) + 1 - (t + 1 + 1) = d by omega,
    show d + (t + 1) + 1 + (t + 1) = d + (t + 1) + (t + 1) + 1 by omega,
    show d + (t + 1) + (t + 1 + 1) = d + (t + 1) + (t + 1) + 1 by omega,
    P_succ q d, P_succ q (d + (t + 1) + (t + 1)), Wn_succ]
  have key := al_mid (q := q) (z := z) (q ^ d) (q ^ (t + 1)) (q ^ (t + 1).choose 2) ((-1) ^ (t + 1))
    (P q d) (P q (d + (t + 1) + (t + 1))) (Wn q z (d + (t + 1))) (P_ne hq _) (P_ne hq _) hz
    (by convert hq d using 2; ring) (by convert hq (d + (t + 1) + (t + 1)) using 2; ring)
    (by convert hq (d + (t + 1)) using 2; ring) (hzq t) (hzq' t)
  have e1 : q ^ (d + (t + 1) + 1) = q ^ d * q ^ (t + 1) * q := by ring
  have e2 : q ^ (d + 1) = q ^ d * q := by ring
  have e3 : q ^ (d + (t + 1) + (t + 1) + 1) = q ^ d * q ^ (t + 1) * q ^ (t + 1) * q := by ring
  rw [e1, e2, e3]
  simp only [hr0, show t + 1 + 1 ≠ 0 by omega, if_false]
  generalize 1 - q ^ d * q = D1 at key ⊢
  generalize 1 - q ^ d * q ^ (t + 1) * q = D2 at key ⊢
  generalize 1 - q ^ d * q ^ (t + 1) * q ^ (t + 1) * q = D3 at key ⊢
  generalize 1 - z * q ^ (t + 1) = D4 at key ⊢
  generalize 1 - z⁻¹ * q ^ (t + 1) = D5 at key ⊢
  linear_combination key

omit hzq hzq' in
lemma al_bot_step (n : ℕ) : Fr q z (n + 1) 0 - Fr q z n 0 = Gc q z n 1 - Gc q z n 0 := by
  unfold Fr Gc alL
  simp only [if_true, one_ne_zero, if_false, Nat.sub_zero, add_zero]
  rw [show n + 1 - 1 = n by omega, P_succ q n, Wn_succ]
  have key := al_bot (z := z) (q ^ (n + 1)) ((1 - z) * (1 - z⁻¹)) (P q n) (Wn q z n) (P_ne hq _) (hq n) hz rfl
  rw [show Nat.choose 1 2 = 0 by rfl, add_zero]
  generalize 1 - q ^ (n + 1) = D1 at key ⊢
  generalize 1 - z * q ^ (n + 1) = D4 at key ⊢
  generalize 1 - z⁻¹ * q ^ (n + 1) = D5 at key ⊢
  linear_combination key

lemma al_top_step (n : ℕ) : Fr q z (n + 1) (n + 1) = -Gc q z n (n + 1) := by
  unfold Fr Gc alL
  simp only [show n + 1 ≠ 0 by omega, if_false, Nat.sub_self]
  rw [choose2_succ (n + 1), show n + 1 + (n + 1) = 2 * n + 1 + 1 by omega,
    show n + (n + 1) = 2 * n + 1 by omega, P_succ q (2 * n + 1), Wn_succ,
    show P q 0 = 1 by simp [P]]
  have hsq : (1 : K) - q ^ (2 * n + 1 + 1) = (1 - q ^ (n + 1)) * (1 + q ^ (n + 1)) := by ring
  have hQ' : (1 : K) + q ^ (n + 1) ≠ 0 := by
    intro h; apply hq (2 * n + 1); rw [hsq, h, mul_zero]
  have key := al_top (q ^ (n + 1)) (q ^ (n + 1).choose 2) ((-1) ^ n) ((1 - z) * (1 - z⁻¹))
    (P q (2 * n + 1)) (Wn q z n) (1 - z * q ^ (n + 1)) (1 - z⁻¹ * q ^ (n + 1)) (P_ne hq _) (hq n) hQ'
    (hzq n) (hzq_inv hz hzq' n)
  rw [hsq]
  generalize 1 - q ^ (n + 1) = D1 at key ⊢
  generalize 1 + q ^ (n + 1) = D2 at key ⊢
  generalize 1 - z * q ^ (n + 1) = D4 at key ⊢
  generalize 1 - z⁻¹ * q ^ (n + 1) = D5 at key ⊢
  linear_combination key

lemma al_step (n r : ℕ) (hr : r ≤ n) :
    Fr q z (n + 1) r - Fr q z n r = Gc q z n (r + 1) - Gc q z n r := by
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · exact al_bot_step hq hz n
  · obtain ⟨d, rfl⟩ : ∃ d, n = d + r := ⟨n - r, by omega⟩
    exact al_mid_step hq hz hzq hzq' d r hpos

/-- the finite Bailey pair: `Σ_{r≤n} α_r/((q)_{n−r}(q)_{n+r}) = 1/((zq)_n(q/z)_n)`, normalized. -/
theorem al_pair (n : ℕ) : ∑ r ∈ range (n + 1), Fr q z n r = 1 := by
  induction n with
  | zero => simp [Fr, alL, Wn, P]
  | succ n ih =>
    have hD : ∑ r ∈ range (n + 1), (Fr q z (n + 1) r - Fr q z n r) = Gc q z n (n + 1) := by
      rw [sum_congr rfl fun r hr => al_step hq hz hzq hzq' n r (by have := mem_range.mp hr; omega),
        sum_range_sub (fun s => Gc q z n s)]
      simp [Gc]
    rw [sum_range_succ, al_top_step hq hz hzq hzq' n, ← ih]
    rw [sum_sub_distrib] at hD
    linear_combination hD

end ALAssembly

/-! ## Transfer to `ℂ⟦X⟧` and the limit -/

section ALSeries
open PowerSeries MockTheta5.Bailey MockTheta5.JTP CrankProof
local notation "ψ" => MockTheta5.JTP.ψC

abbrev KC := FractionRing (PowerSeries ℂ)
noncomputable abbrev φC : PowerSeries ℂ →+* KC := algebraMap (PowerSeries ℂ) KC

lemma φC_inj : Function.Injective φC := IsFractionRing.injective _ _

lemma φC_inverse {u : PowerSeries ℂ} (hu : IsUnit u) : φC (Ring.inverse u) = (φC u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one])

lemma φC_ne {f : PowerSeries ℂ} (h : constantCoeff f ≠ 0) : φC f ≠ 0 := by
  intro h'; apply h; rw [← map_zero φC] at h'; rw [φC_inj h', map_zero]

/-- the `α` of the pair, as a power series. -/
noncomputable def αser (z : ℂ) (r : ℕ) : PowerSeries ℂ :=
  if r = 0 then 1
  else C ((-1) ^ r * ((1 - z) * (1 - z⁻¹))) * X ^ ((r + 1).choose 2) * (1 + X ^ r)
    * Ring.inverse ((1 - C z * X ^ r) * (1 - C z⁻¹ * X ^ r))

lemma φC_Cinv (z : ℂ) : φC (C z⁻¹) = (φC (C z))⁻¹ := map_inv₀ (φC.comp C) z

lemma φC_αser (z : ℂ) (r : ℕ) : φC (αser z r) = alL (φC X) (φC (C z)) r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [αser, alL]
  have hr0 : r ≠ 0 := by omega
  have hu : IsUnit ((1 - C z * X ^ r) * (1 - C z⁻¹ * X ^ r) : PowerSeries ℂ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [zero_pow hr0]
  simp only [αser, alL, if_neg hr0]
  rw [map_mul, φC_inverse hu]
  simp only [map_mul, map_sub, map_add, map_one, map_pow, map_neg, φC_Cinv]
  rw [div_eq_mul_inv]
  ring

lemma φC_qfac (m : ℕ) : φC (ψ (qfac m)) = P (φC X) m := by
  rw [qfac, map_prod, map_prod, P]
  exact prod_congr rfl fun i _ => by simp [map_sub, map_pow]

lemma φC_poch (z : ℂ) (n : ℕ) :
    φC (poch z 1 n) * φC (poch z⁻¹ 1 n) = Wn (φC X) (φC (C z)) n := by
  rw [poch, poch, map_prod, map_prod, ← prod_mul_distrib, Wn]
  refine prod_congr rfl fun i _ => ?_
  simp only [map_sub, map_one, map_mul, map_pow, φC_Cinv, add_comm 1 i]

lemma hqC : ∀ i : ℕ, 1 - (φC X) ^ (i + 1) ≠ 0 := fun i => by
  have := φC_ne (f := 1 - X ^ (i + 1)) (by simp)
  simpa [map_sub, map_pow] using this

lemma hwC {z : ℂ} (hz : z ≠ 0) : φC (C z) ≠ 0 := φC_ne (by simpa using hz)

lemma hwqC (z : ℂ) : ∀ i : ℕ, 1 - φC (C z) * (φC X) ^ (i + 1) ≠ 0 := fun i => by
  have := φC_ne (f := 1 - C z * X ^ (i + 1)) (by simp)
  simpa [map_sub, map_pow, map_mul] using this

lemma hwqC' {z : ℂ} (hz : z ≠ 0) : ∀ i : ℕ, φC (C z) - (φC X) ^ (i + 1) ≠ 0 := fun i => by
  have := φC_ne (f := C z - X ^ (i + 1)) (by simpa using hz)
  simpa [map_sub, map_pow] using this

/-- **the finite Bailey pair in `ℂ⟦X⟧`**:
`Σ_{r≤n} α_r/((q)_{n−r}(q)_{n+r}) = 1/((zq)_n(q/z)_n)`. -/
theorem al_pair_series {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    ∑ r ∈ range (n + 1), αser z r * ψ (Ring.inverse (qfac (n - r))) * ψ (Ring.inverse (qfac (n + r)))
      = Ring.inverse (poch z 1 n) * Ring.inverse (poch z⁻¹ 1 n) := by
  apply φC_inj
  have h := al_pair hqC (hwC hz) (hwqC z) (hwqC' hz) n
  have hW : Wn (φC X) (φC (C z)) n ≠ 0 := by
    rw [Wn, prod_ne_zero_iff]; intro i _
    exact mul_ne_zero (hwqC z i) (hzq_inv (hwC hz) (hwqC' hz) i)
  have hψ : ∀ m, φC (ψ (Ring.inverse (qfac m))) = (P (φC X) m)⁻¹ := fun m => by
    rw [map_inverse ψ (isUnit_qfac m), φC_inverse ((isUnit_qfac m).map ψ), φC_qfac]
  rw [map_mul, φC_inverse (isUnit_poch z le_rfl n), φC_inverse (isUnit_poch z⁻¹ le_rfl n), ← mul_inv,
    φC_poch, map_sum, ← mul_one (Wn (φC X) (φC (C z)) n)⁻¹, ← h, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, hψ, hψ, φC_αser, Fr]
  have h1 := P_ne hqC (n - r)
  have h2 := P_ne hqC (n + r)
  field_simp

/-- `Σ_r q^{r²} α_r`, coefficientwise. -/
noncomputable def ALser (z : ℂ) : PowerSeries ℂ :=
  mk fun c => coeff c (∑ r ∈ range (c + 1), X ^ (r ^ 2) * αser z r)

lemma ALser_dvd (z : ℂ) (c : ℕ) :
    (X : PowerSeries ℂ) ^ (c + 1) ∣ ALser z - ∑ r ∈ range (c + 1), X ^ (r ^ 2) * αser z r := by
  rw [X_pow_dvd_iff]; intro i hi
  rw [map_sub, ALser, coeff_mk, sub_eq_zero, map_sum, map_sum]
  refine sum_subset (range_subset_range.mpr (by omega)) fun r _ hr => ?_
  simp only [mem_range, not_lt] at hr
  exact coeffC_Xpow_zero (by nlinarith) _

noncomputable def Hterm (z : ℂ) (c r m : ℕ) : ℂ := coeff c (X ^ (r ^ 2) * αser z r * ψ (rectTerm (2 * r) m))

/-- **the Appell–Lerch form of the rank generating function**:
`R(z;q) = Σ_n q^{n²}/((zq)_n(q/z)_n) = (1/(q;q)_∞)·Σ_{r≥0} q^{r²} α_r`, i.e.
`(q)_∞ R(z;q) = 1 + Σ_{r≥1} (−1)^r q^{r(3r+1)/2}(1+q^r)(1−z)(1−z⁻¹)/((1−zq^r)(1−q^r/z))`. -/
theorem rank_AL {z : ℂ} (hz : z ≠ 0) : Dser z z⁻¹ = ψ (Ring.inverse qfacInf) * ALser z := by
  ext c
  let f := Hterm z c
  have hR : coeff c (ψ (Ring.inverse qfacInf) * ALser z) = ∑ r ∈ range (c + 1), ∑ m ∈ range (c + 1), f r m := by
    rw [coeffC_congr (ALser_dvd z c), mul_sum, map_sum]
    refine sum_congr rfl fun r _ => ?_
    have hd := ψ_dvd (rect_dvd (2 * r) c)
    rw [map_sub] at hd
    rw [← durfee_rect_base (2 * r), mul_comm, coeffC_congr hd, rectPartial, map_sum, mul_sum, map_sum]
    exact sum_congr rfl fun m _ => rfl
  have hL : coeff c (Dser z z⁻¹) = ∑ j ∈ range (c + 1), ∑ r ∈ range (j + 1), f r (j - r) := by
    rw [Dser, coeff_mk, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [show C ((z * z⁻¹) ^ j) * X ^ (j ^ 2) * Ring.inverse (poch z 1 j) * Ring.inverse (poch z⁻¹ 1 j)
        = X ^ (j ^ 2) * (Ring.inverse (poch z 1 j) * Ring.inverse (poch z⁻¹ 1 j)) by
        rw [mul_inv_cancel₀ hz, one_pow, map_one]; ring,
      ← al_pair_series hz j, mul_sum, map_sum]
    refine sum_congr rfl fun r hr => ?_
    obtain ⟨m, rfl⟩ : ∃ m, j = r + m := ⟨j - r, by have := mem_range.mp hr; omega⟩
    show _ = Hterm z c r (r + m - r)
    rw [Hterm, show r + m - r = m by omega, rectTerm, RingHom.map_mul ψ, RingHom.map_mul ψ, RingHom.map_pow ψ, PowerSeries.map_X,
      show r + m + r = 2 * r + m by ring, show (r + m) ^ 2 = r ^ 2 + (m ^ 2 + 2 * r * m) by ring, pow_add]
    ring_nf
  rw [hL, hR, sum_range_diag_flip]
  refine sum_congr rfl fun r hr => ?_
  refine sum_subset (range_subset_range.mpr (by omega)) fun m _ hm => ?_
  simp only [mem_range, not_lt] at hm
  show Hterm z c r m = 0
  rw [Hterm, rectTerm, RingHom.map_mul ψ, RingHom.map_mul ψ, RingHom.map_pow ψ, PowerSeries.map_X,
    show X ^ (r ^ 2) * αser z r * (X ^ (m ^ 2 + 2 * r * m) * ψ (Ring.inverse (qfac m))
      * ψ (Ring.inverse (qfac (2 * r + m))))
      = X ^ (r ^ 2 + (m ^ 2 + 2 * r * m))
        * (αser z r * ψ (Ring.inverse (qfac m)) * ψ (Ring.inverse (qfac (2 * r + m)))) by ring]
  have hr' := mem_range.mp hr
  have h1 : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
  have h2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
  have h3 : c + 1 ≤ r + m := by omega
  exact coeffC_Xpow_zero (by nlinarith [Nat.zero_le (2 * r * m)]) _

end ALSeries

end RankProof
