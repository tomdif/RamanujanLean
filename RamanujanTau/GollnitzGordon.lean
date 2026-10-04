/-
# The first Göllnitz–Gordon identity

  `Σ_{n≥0} q^{n²} (−q;q²)_n / (q²;q²)_n = 1/((q;q⁸)_∞ (q⁴;q⁸)_∞ (q⁷;q⁸)_∞)`.

The proof inserts the parameter `ρ = −q` into Bailey's lemma in base `q²`. For a Bailey pair `(α,β)` in base `q²`:

* **chain step** (`isBaileyPair2_rho`): `(q^{n²}αₙ, (1/(−q;q²)_n) Σ_{j≤n} (−q;q²)_j q^{j²}/(q²;q²)_{n−j} β_j)` is again a
  Bailey pair. The inner sum is `inner_gg`, proved by WZ.
* **transform** (`bailey_transform_rho`): letting `n → ∞`,
  `Σ (−q;q²)_n q^{n²} βₙ = (−q;q²)_∞/(q²;q²)_∞ · Σ q^{n²} αₙ`.

Applied to the Rogers–Ramanujan pair in base `q²`, the right side is `(−q;q²)_∞ J_{8,3}/(q²;q²)_∞`.
-/
import RamanujanTau.GollnitzGordonWZ
import RamanujanTau.RogersRamanujan
import RamanujanTau.FourSquaresLimit

set_option autoImplicit false

namespace GG
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP MockTheta5.JTP.RR
open RankProof (Ea Ea_X Ea_Pinf Pinf Pfin Pfin_succ X_pow_dvd_Pinf_sub X_pow_dvd_Pfin_sub Pinf_ext Pinf_one_one
  thetaS thA thB thetaTr thetaTr_eq thetaS_dvd jtp_ab)

/-- a Bailey pair relative to `a = 1` in base `q²`. -/
def IsBaileyPair2 (α β : ℕ → PowerSeries ℤ) : Prop :=
  ∀ n, β n = ∑ r ∈ range (n + 1), α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Qf (n + r))

lemma map_inverse' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {u : R} (hu : IsUnit u) :
    f (Ring.inverse u) = Ring.inverse (f u) := by
  have h1 : f u * f (Ring.inverse u) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]
  calc f (Ring.inverse u) = (Ring.inverse (f u) * f u) * f (Ring.inverse u) := by
        rw [Ring.inverse_mul_cancel _ (hu.map f), one_mul]
    _ = Ring.inverse (f u) * (f u * f (Ring.inverse u)) := by ring
    _ = Ring.inverse (f u) := by rw [h1, mul_one]

lemma Ea2_qfac (n : ℕ) : Ea 2 two_ne_zero (qfac n) = Qf n := by
  rw [qfac, Qf, map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, Ea_X, ← pow_mul]; ring_nf

/-- the Rogers–Ramanujan pair in base `q²`. -/
theorem isBaileyPair2_C : IsBaileyPair2 (fun r => Ea 2 two_ne_zero (alphaC r)) (fun n => Ring.inverse (Qf n)) := by
  intro n
  have h := congrArg (Ea 2 two_ne_zero) (isBaileyPair_C n)
  simp only at h
  rw [map_inverse' _ (isUnit_qfac n), Ea2_qfac, map_sum] at h
  show Ring.inverse (Qf n) = _
  rw [h]
  refine sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_inverse' _ (isUnit_qfac _), map_inverse' _ (isUnit_qfac _), Ea2_qfac, Ea2_qfac]

/-! ## the `ρ = −q` chain step -/

noncomputable def rhoBeta (β : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  Ring.inverse (Mq n) * ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j

lemma inv_mul3 (a b c : PowerSeries ℤ) (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    Ring.inverse (a * b * c) = Ring.inverse a * Ring.inverse b * Ring.inverse c := by
  rw [Ring.mul_inverse_rev' (Commute.all _ _), Ring.mul_inverse_rev' (Commute.all _ _)]; ring

theorem isBaileyPair2_rho {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPair2 α β) :
    IsBaileyPair2 (fun n => X ^ (n ^ 2) * α n) (rhoBeta β) := by
  unfold IsBaileyPair2 at h
  intro n
  show rhoBeta β n = _
  rw [rhoBeta]
  set T : ℕ → ℕ → PowerSeries ℤ := fun j r =>
    Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * (α r * Ring.inverse (Qf (j - r)) * Ring.inverse (Qf (j + r)))
    with hT
  have hswap : ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j
      = ∑ r ∈ range (n + 1), α r * X ^ (r ^ 2) * (Mq n * Ring.inverse (Qf (n - r) * Qf (n + r))) := by
    calc ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j
        = ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1), T j r := by simp_rw [h, mul_sum, hT]
      _ = ∑ r ∈ Ico 0 (n + 1), ∑ j ∈ Ico r (n + 1), T j r := by
          rw [range_eq_Ico]; simp_rw [range_eq_Ico]
          exact (sum_Ico_Ico_comm 0 (n + 1) (fun r j => T j r)).symm
      _ = ∑ r ∈ range (n + 1), ∑ i ∈ range (n + 1 - r), T (r + i) r := by
          rw [← range_eq_Ico]; exact sum_congr rfl fun r _ => sum_Ico_eq_sum_range _ _ _
      _ = _ := by
          refine sum_congr rfl fun r hr => ?_
          rw [mem_range] at hr
          have hin := inner_gg r (n - r)
          rw [show n - r + 1 = n + 1 - r by omega, show r + (n - r) = n by omega,
            show 2 * r + (n - r) = n + r by omega] at hin
          rw [← hin, mul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [mem_range] at hi
          simp only [hT]
          rw [show n - (r + i) = n - r - i by omega, show r + i - r = i by omega, show r + i + r = 2 * r + i by ring,
            inv_mul3 _ _ _ (isUnit_Qf _) (isUnit_Qf _) (isUnit_Qf _),
            show (r + i) ^ 2 = r ^ 2 + (2 * r * i + i ^ 2) by ring, pow_add]
          ring
  rw [hswap, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  have h1 := Ring.inverse_mul_cancel _ (isUnit_Mq n)
  rw [Ring.mul_inverse_rev' (Commute.all _ _)]
  linear_combination (X ^ (r ^ 2) * α r * Ring.inverse (Qf (n + r)) * Ring.inverse (Qf (n - r))) * h1


/-! ## the limit `n → ∞` -/

open FourSquares (π π_eq_iff π_inverse π_X_pow)

/-- `(q²;q²)_∞`. -/
noncomputable def Qinf2 : PowerSeries ℤ := Ea 2 two_ne_zero qfacInf
/-- `(−q;q²)_∞`. -/
noncomputable def Minf : PowerSeries ℤ := mk fun k => coeff k (Mq (k + 1))

lemma X_pow_dvd_Mq_sub (N : ℕ) : ∀ M, N ≤ M → (X : PowerSeries ℤ) ^ (N + 1) ∣ Mq M - Mq N := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Mq_succ, show Mq M * (1 + X ^ (2 * M + 1)) - Mq N = (Mq M - Mq N) + Mq M * X ^ (2 * M + 1) by ring]
    exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _)

lemma π_Mq {N n : ℕ} (h : N ≤ n) : π N (Mq n) = π N Minf := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, Minf, coeff_mk, sub_eq_zero, RR.coeff_eq_of_dvd (X_pow_dvd_Mq_sub k n (by omega)) (Nat.lt_succ_self k),
    RR.coeff_eq_of_dvd (X_pow_dvd_Mq_sub k (k + 1) (by omega)) (Nat.lt_succ_self k)]

lemma π_Qf {N n : ℕ} (h : N ≤ n) : π N (Qf n) = π N Qinf2 := by
  rw [π_eq_iff, ← Ea2_qfac, Qinf2, ← map_sub]
  have hd : (X : PowerSeries ℤ) ^ n ∣ qfac n - qfacInf := by
    rw [PowerSeries.X_pow_dvd_iff]; intro j hj
    rw [map_sub, coeff_qfacInf (show j + 1 ≤ n by omega), sub_self]
  obtain ⟨g, hg⟩ := hd
  rw [hg, map_mul, map_pow, Ea_X, ← pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _

lemma isUnit_Qinf2 : IsUnit Qinf2 := isUnit_qfacInf.map _

lemma isUnit_Minf : IsUnit Minf := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, Minf, coeff_mk]
  simp [Mq]

lemma π_sum_split {m n : ℕ} (hmn : m ≤ n) (f g : ℕ → PowerSeries ℤ)
    (c : PowerSeries ℤ ⧸ Ideal.span {(X : PowerSeries ℤ) ^ (m + 1)})
    (h1 : ∀ j, j ≤ m → π (m + 1) (f j) = π (m + 1) (X ^ (j ^ 2) * g j) * c)
    (h2 : ∀ j, m < j → π (m + 1) (f j) = 0) :
    π (m + 1) (∑ j ∈ range (n + 1), f j) = π (m + 1) (tsumQsq g) * c := by
  rw [map_sum, show n + 1 = (m + 1) + (n - m) by omega, sum_range_add,
    sum_eq_zero (s := range (n - m)) (fun i _ => h2 _ (by omega)), add_zero,
    sum_congr rfl (fun j hj => h1 j (by rw [mem_range] at hj; omega)), ← sum_mul, ← map_sum]
  congr 1
  exact (π_eq_iff.mpr (RR.tsumQsq_dvd g m)).symm

lemma π_Xsq_zero {m j : ℕ} (h : m < j) : π (m + 1) (X ^ (j ^ 2) : PowerSeries ℤ) = 0 :=
  π_X_pow (by nlinarith)

/-- **the `ρ = −q` Bailey transform** in base `q²`:
`Σ (−q;q²)_n q^{n²} βₙ = (−q;q²)_∞/(q²;q²)_∞ · Σ q^{n²} αₙ`. -/
theorem bailey_transform_rho {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPair2 α β) :
    tsumQsq (fun n => Mq n * β n) = Minf * Ring.inverse Qinf2 * tsumQsq α := by
  refine eq_of_dvd_all fun m => ?_
  rw [← π_eq_iff]
  set n := 2 * m + 2 with hn
  have hc := isBaileyPair2_rho h n
  rw [rhoBeta] at hc
  have hc' : ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j
      = Mq n * ∑ r ∈ range (n + 1), X ^ (r ^ 2) * α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Qf (n + r)) := by
    rw [← hc, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_Mq n), one_mul]
  have hP := congrArg (π (m + 1)) hc'
  set I := Ring.inverse (π (m + 1) Qinf2) with hI
  have hQ : ∀ k, m + 1 ≤ k → π (m + 1) (Ring.inverse (Qf k)) = I := fun k hk => by
    rw [π_inverse (isUnit_Qf k), π_Qf hk]
  have hL := π_sum_split (m := m) (n := n) (by omega)
    (fun j => Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j) (fun j => Mq j * β j) I
    (fun j hj => by
      show π (m + 1) (Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j) = _
      rw [show Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j
          = X ^ (j ^ 2) * (Mq j * β j) * Ring.inverse (Qf (n - j)) by ring, map_mul, hQ _ (by omega)])
    (fun j hj => by
      show π (m + 1) (Mq j * X ^ (j ^ 2) * Ring.inverse (Qf (n - j)) * β j) = 0
      rw [map_mul, map_mul, map_mul, π_Xsq_zero hj, mul_zero, zero_mul, zero_mul])
  have hR := π_sum_split (m := m) (n := n) (by omega)
    (fun r => X ^ (r ^ 2) * α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Qf (n + r))) α (I * I)
    (fun j hj => by
      show π (m + 1) (X ^ (j ^ 2) * α j * Ring.inverse (Qf (n - j)) * Ring.inverse (Qf (n + j))) = _
      rw [map_mul, map_mul, hQ _ (by omega), hQ _ (by omega)]; ring)
    (fun j hj => by
      show π (m + 1) (X ^ (j ^ 2) * α j * Ring.inverse (Qf (n - j)) * Ring.inverse (Qf (n + j))) = 0
      rw [map_mul, map_mul, map_mul, π_Xsq_zero hj, zero_mul, zero_mul, zero_mul])
  rw [hL, map_mul, π_Mq (show m + 1 ≤ n by omega), hR] at hP
  have hu : I * π (m + 1) Qinf2 = 1 := Ring.inverse_mul_cancel _ (isUnit_Qinf2.map _)
  rw [map_mul, map_mul, π_inverse isUnit_Qinf2]
  linear_combination π (m + 1) Qinf2 * hP
    - (π (m + 1) (tsumQsq fun n => Mq n * β n) - π (m + 1) Minf * π (m + 1) (tsumQsq α) * I) * hu


/-! ## GG1 -/

lemma term_gg (r : ℕ) :
    X ^ (r ^ 2) * Ea 2 two_ne_zero (alphaC r) = thA 8 3 r + (if r = 0 then 0 else thB 8 3 (r - 1)) := by
  rcases r with _ | r
  · simp [alphaC, RankProof.thA]
  · rw [alphaC, if_neg (by omega), if_neg (by omega), RankProof.thA, RankProof.thB, Nat.add_sub_cancel, Apent_eq]
    simp only [map_mul, map_pow, map_neg, map_one, map_add, Ea_X]
    have h2 := two_choose (r + 1)
    have e1 : (r + 1) ^ 2 + 2 * (3 * (r + 1).choose 2 + (r + 1)) = 8 * (r + 1).choose 2 + 3 * (r + 1) := by
      rw [← h2]; ring
    have e2 : (r + 1) ^ 2 + (2 * (3 * (r + 1).choose 2 + (r + 1)) + 2 * (r + 1))
        = 8 * (r + 1).choose 2 + (8 - 3) * (r + 1) := by rw [← h2]; ring
    rw [← e1, ← e2]
    simp only [← pow_mul, pow_add, map_mul, map_neg, map_pow, map_one]
    ring

lemma sum_term_gg (N : ℕ) :
    ∑ n ∈ range (N + 1), X ^ (n ^ 2) * Ea 2 two_ne_zero (alphaC n)
      = ∑ d ∈ range (N + 1), thA 8 3 d + ∑ d ∈ range N, thB 8 3 d := by
  induction N with
  | zero => simp [term_gg]
  | succ N ih =>
    rw [sum_range_succ, ih, term_gg, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA _ _) (N + 1),
      sum_range_succ (thB _ _) N]
    ring

theorem alpha_gg_theta : tsumQsq (fun r => Ea 2 two_ne_zero (alphaC r)) = thetaS 8 3 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := RR.tsumQsq_dvd (fun r => Ea 2 two_ne_zero (alphaC r)) N
  have h2 := thetaS_dvd 8 3 (by norm_num) (by norm_num) N
  rw [sum_term_gg] at h1
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB 8 3 N := thB_deg 8 3 N (by norm_num)
  rw [thetaTr_eq, sum_range_succ (thB _ _)] at h2
  have := dvd_sub (dvd_sub h1 h2) h3
  rw [show tsumQsq (fun r => Ea 2 two_ne_zero (alphaC r)) - (∑ d ∈ range (N + 1), thA 8 3 d + ∑ d ∈ range N, thB 8 3 d)
      - (thetaS 8 3 - (∑ d ∈ range (N + 1), thA 8 3 d + (∑ d ∈ range N, thB 8 3 d + thB 8 3 N))) - thB 8 3 N
      = tsumQsq (fun r => Ea 2 two_ne_zero (alphaC r)) - thetaS 8 3 by ring] at this
  exact this

/-- `(q^b;q^a)_∞ = (q^b;q^{2a})_∞ (q^{a+b};q^{2a})_∞`. -/
lemma Pfin_split_two (b a : ℕ) : ∀ N, Pfin b a (2 * N) = Pfin b (2 * a) N * Pfin (b + a) (2 * a) N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Pfin_succ, Pfin_succ, Pfin_split_two b a N, Pfin_succ, Pfin_succ]
    ring_nf

lemma Pinf_split_two {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) : Pinf b a = Pinf b (2 * a) * Pinf (b + a) (2 * a) := by
  symm
  refine Pinf_ext hb ha fun N => ?_
  rw [← π_eq_iff, map_mul, (π_eq_iff.mpr (X_pow_dvd_Pinf_sub b (2 * a) hb (by omega) N)),
    (π_eq_iff.mpr (X_pow_dvd_Pinf_sub (b + a) (2 * a) (by omega) (by omega) N)), ← map_mul, ← Pfin_split_two, π_eq_iff]
  exact X_pow_dvd_Pfin_sub b a N hb ha (2 * N) (by omega)

lemma Qinf2_eq : Qinf2 = Pinf 2 2 := by
  rw [Qinf2, ← Pinf_one_one, Ea_Pinf 2 1 1 two_ne_zero le_rfl le_rfl]

lemma Mq_Pfin (N : ℕ) : Mq N * Pfin 1 2 N = Pfin 2 4 N := by
  induction N with
  | zero => simp [Mq, Pfin]
  | succ N ih => rw [Mq_succ, Pfin_succ, Pfin_succ, ← ih]; ring_nf

lemma Minf_mul : Minf * Pinf 1 2 = Pinf 2 4 := by
  refine Pinf_ext (by norm_num) (by norm_num) fun N => ?_
  rw [← π_eq_iff, map_mul, ← π_Mq (show N + 1 ≤ N + 1 from le_rfl),
    (π_eq_iff.mpr (X_pow_dvd_Pinf_sub 1 2 le_rfl (by norm_num) N)),
    (π_eq_iff.mpr (X_pow_dvd_Mq_sub N (N + 1) (by omega))), ← map_mul, Mq_Pfin]

/-- **The first Göllnitz–Gordon identity**:
`Σ_{n≥0} q^{n²}(−q;q²)_n/(q²;q²)_n = 1/((q;q⁸)_∞(q⁴;q⁸)_∞(q⁷;q⁸)_∞)`. -/
theorem gollnitz_gordon_1 :
    tsumQsq (fun n => Mq n * Ring.inverse (Qf n)) * (Pinf 1 8 * Pinf 4 8 * Pinf 7 8) = 1 := by
  rw [bailey_transform_rho isBaileyPair2_C, alpha_gg_theta, ← jtp_ab 8 3 (by norm_num) (by norm_num), Qinf2_eq]
  have h22 : Pinf 2 2 = Pinf 2 4 * (Pinf 4 8 * Pinf 8 8) := by
    rw [Pinf_split_two (b := 2) (a := 2) (by norm_num) (by norm_num), Pinf_split_two (b := 4) (a := 4) (by norm_num) (by norm_num)]
  have h12 : Pinf 1 2 = (Pinf 1 8 * Pinf 5 8) * (Pinf 3 8 * Pinf 7 8) := by
    rw [Pinf_split_two (b := 1) (a := 2) (by norm_num) (by norm_num), Pinf_split_two (b := 1) (a := 4) (by norm_num) (by norm_num),
      Pinf_split_two (b := 3) (a := 4) (by norm_num) (by norm_num)]
  have hM := Minf_mul
  rw [h12] at hM
  rw [h22]
  norm_num
  have hu : IsUnit (Pinf 2 4 * (Pinf 4 8 * Pinf 8 8)) := by
    rw [← h22, ← Qinf2_eq]; exact isUnit_Qinf2
  have hinv := Ring.mul_inverse_cancel _ hu
  linear_combination (Ring.inverse (Pinf 2 4 * (Pinf 4 8 * Pinf 8 8)) * Pinf 4 8 * Pinf 8 8) * hM
    + hinv

end GG
