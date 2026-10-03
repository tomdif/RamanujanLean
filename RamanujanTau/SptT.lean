/-
# The spt identity, step 1: `R(z) = C(z) · Σ (z)_n(z⁻¹)_n qⁿ/(q)_n` (finite form)

With `W_n = (zq)_n(q/z)_n`, `α_r` the Appell–Lerch weights of `RankAL` and `F(n,r) = q^{r²}α_r W_n/((q)_{n−r}(q)_{n+r})`:
  `Σ_{r≤n} F(n,r) = Σ_{j≤n} (z)_j(z⁻¹)_j q^j/(q)_j`.
Both sides satisfy `S(n+2) − S(n+1) = ρ_n (S(n+1) − S(n))`, `ρ_n = (1−zq^{n+1})(1−q^{n+1}/z)q/(1−q^{n+2})`;
for the left side this is creative telescoping with the certificate
  `G(n,s) = (−1)^{s+1} q^{2n+3+C(s+1,2)+(s−1)²}(1−z)(1−z⁻¹)W_{n+1}/((1−q^{n+2})(q)_{n+2−s}(q)_{n+1+s})`.
-/
import RamanujanTau.RankAL

set_option autoImplicit false

namespace RankProof
open Finset

section SptFinite
variable {K : Type*} [Field K] (q z : K)

/-- `F(n,r) = q^{r²} α_r W_n/((q)_{n−r}(q)_{n+r})`. -/
def Fs (n r : ℕ) : K := q ^ (r ^ 2) * Fr q z n r

/-- the certificate. -/
def Gs (n s : ℕ) : K :=
  if s = 0 ∨ n + 2 < s then 0
  else (-1) ^ (s + 1) * q ^ (2 * n + 3 + (s + 1).choose 2 + (s - 1) ^ 2) * ((1 - z) * (1 - z⁻¹)) * Wn q z (n + 1)
    / ((1 - q ^ (n + 2)) * P q (n + 2 - s) * P q (n + 1 + s))

/-- `(w;q)_j`. -/
def zp (w : K) (j : ℕ) : K := ∏ i ∈ range j, (1 - w * q ^ i)

/-- `t_j = (z)_j(z⁻¹)_j q^j/(q)_j`. -/
def tz (j : ℕ) : K := zp q z j * zp q z⁻¹ j * q ^ j / P q j

/-- the ratio `t_{n+2}/t_{n+1}`. -/
def rho (n : ℕ) : K := (1 - z * q ^ (n + 1)) * (1 - z⁻¹ * q ^ (n + 1)) * q / (1 - q ^ (n + 2))

def SF (n : ℕ) : K := ∑ r ∈ range (n + 1), Fs q z n r

def TS (n : ℕ) : K := ∑ j ∈ range (n + 1), tz q z j

end SptFinite

section SptSteps
variable {K : Type*} [Field K] {q z : K} (hq : ∀ i : ℕ, 1 - q ^ (i + 1) ≠ 0) (hz : z ≠ 0)
  (hzq : ∀ i : ℕ, 1 - z * q ^ (i + 1) ≠ 0) (hzq' : ∀ i : ℕ, z - q ^ (i + 1) ≠ 0)
include hq

lemma tz_succ_succ (n : ℕ) : tz q z (n + 2) = rho q z n * tz q z (n + 1) := by
  unfold tz rho zp
  rw [prod_range_succ _ (n + 1), prod_range_succ _ (n + 1), P_succ q (n + 1)]
  have h1 := hq (n + 1)
  have h2 := P_ne hq (n + 1)
  field_simp
  ring

omit hq in
lemma hzq_inv' (hz : z ≠ 0) (hzq' : ∀ i : ℕ, z - q ^ (i + 1) ≠ 0) (i : ℕ) : 1 - z⁻¹ * q ^ (i + 1) ≠ 0 := by
  intro h; apply hzq' i
  have : z - q ^ (i + 1) = z * (1 - z⁻¹ * q ^ (i + 1)) := by field_simp
  rw [this, h, mul_zero]

omit hq in
lemma Gs_of (n s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ n + 2) :
    Gs q z n s = (-1) ^ (s + 1) * q ^ (2 * n + 3 + (s + 1).choose 2 + (s - 1) ^ 2) * ((1 - z) * (1 - z⁻¹))
      * Wn q z (n + 1) / ((1 - q ^ (n + 2)) * P q (n + 2 - s) * P q (n + 1 + s)) := by
  unfold Gs; rw [if_neg (by omega)]

omit hq in
lemma Fs_of (n r : ℕ) (h1 : 1 ≤ r) :
    Fs q z n r = q ^ (r ^ 2) * ((-1) ^ r * q ^ ((r + 1).choose 2) * (1 + q ^ r) * ((1 - z) * (1 - z⁻¹))
      / ((1 - z * q ^ r) * (1 - z⁻¹ * q ^ r)) * Wn q z n / (P q (n - r) * P q (n + r))) := by
  unfold Fs Fr alL; rw [if_neg (by omega)]

include hz hzq hzq' in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma sp_mid (d t : ℕ) :
    Fs q z (d + t + 3) (t + 1) - (1 + rho q z (d + t + 1)) * Fs q z (d + t + 2) (t + 1)
      + rho q z (d + t + 1) * Fs q z (d + t + 1) (t + 1)
      = Gs q z (d + t + 1) (t + 2) - Gs q z (d + t + 1) (t + 1) := by
  rw [Fs_of _ _ (by omega), Fs_of _ _ (by omega), Fs_of _ _ (by omega), Gs_of _ _ (by omega) (by omega),
    Gs_of _ _ (by omega) (by omega)]
  unfold rho
  have hc1 : (t + 1 + 1).choose 2 = (t + 1).choose 2 + (t + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hc2 : (t + 2 + 1).choose 2 = (t + 1).choose 2 + (t + 1) + (t + 2) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, show t + 2 = t + 1 + 1 by rfl, hc1]; ring
  rw [hc1, hc2]
  simp only [show d + t + 3 - (t + 1) = d + 2 by omega, show d + t + 2 - (t + 1) = d + 1 by omega,
    show d + t + 1 - (t + 1) = d by omega, show d + t + 1 + 2 - (t + 2) = d + 1 by omega,
    show d + t + 1 + 2 - (t + 1) = d + 2 by omega, show t + 2 - 1 = t + 1 by omega, show t + 1 - 1 = t by omega,
    show d + t + 3 + (t + 1) = d + 2 * t + 4 by omega, show d + t + 2 + (t + 1) = d + 2 * t + 3 by omega,
    show d + t + 1 + (t + 1) = d + 2 * t + 2 by omega, show d + t + 1 + 1 + (t + 2) = d + 2 * t + 4 by omega,
    show d + t + 1 + 1 + (t + 1) = d + 2 * t + 3 by omega, show d + t + 3 = d + t + 1 + 1 + 1 by omega,
    show d + t + 2 = d + t + 1 + 1 by omega, show t + 2 + 1 = t + 1 + 1 + 1 by omega,
    show t + 1 + 1 = t + 2 by omega]
  simp only [P_succ, Wn_succ]
  have e0 := hq d
  have e1 := hq (d + 1)
  have e2 := hq (d + 2 * t + 1)
  have e3 := hq (d + 2 * t + 2)
  have e4 := hq (d + 2 * t + 3)
  have e8 := hq (d + 2 * t)
  have e5 := hq (d + t + 1 + 1)
  have e6 := hzq t
  have e9 := hzq' t
  have p1 := P_ne hq d
  have p2 := P_ne hq (d + 2 * t)
  have hinv : ∀ x : K, 1 - z⁻¹ * x = (z - x) / z := fun x => by field_simp
  simp only [hinv]
  rw [show (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 by ring]
  clear hq hzq hzq'
  simp only [mul_add, add_mul, pow_add, pow_mul', pow_one, one_mul, mul_one] at *
  generalize P q d = A at *
  generalize P q (d + 2 * t) = B at *
  generalize Wn q z (d + t) = W at *
  generalize (t + 1).choose 2 = c at *
  generalize q ^ c = Cq at *
  generalize q ^ (t ^ 2) = E at *
  generalize q ^ d = D at *
  generalize q ^ t = T at *
  generalize ((-1 : K) ^ t) = sg at *
  have hz1 : (1 : K) - z⁻¹ = (z - 1) / z := by field_simp
  rw [hz1]
  generalize hu1 : (1 - D * q) = u1 at *
  generalize hu2 : (1 - D * q * q) = u2 at *
  generalize hu3 : (1 - D * T * q * q * q) = u3 at *
  generalize hu4 : (1 - D * T ^ 2 * q) = u4 at *
  generalize hu5 : (1 - D * T ^ 2 * q * q) = u5 at *
  generalize hu6 : (1 - D * T ^ 2 * q ^ 2 * q) = u6 at *
  generalize hu7 : (1 - D * T ^ 2 * q ^ 3 * q) = u7 at *
  generalize hu8 : (1 - z * (T * q)) = u8 at *
  generalize hu9 : (z - T * q) = u9 at *
  field_simp
  subst hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9
  ring

include hz hzq hzq' in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma sp_bot (n : ℕ) :
    Fs q z (n + 2) 0 - (1 + rho q z n) * Fs q z (n + 1) 0 + rho q z n * Fs q z n 0 = Gs q z n 1 - Gs q z n 0 := by
  rw [Gs_of _ _ (by omega) (by omega)]
  unfold Fs Fr alL rho Gs
  simp only [if_true, show (0 = 0 ∨ n + 2 < 0) by omega, Nat.sub_zero, add_zero, pow_zero, one_mul,
    show (0 : ℕ) ^ 2 = 0 by rfl, show n + 2 - 1 = n + 1 by omega, show (1 : ℕ) - 1 = 0 by rfl,
    show n + 1 + 1 = n + 2 by omega]
  simp only [show n + 2 = n + 1 + 1 by omega, P_succ, Wn_succ]
  have e0 := hq n
  have e1 := hq (n + 1)
  have e6 := hzq n
  have e9 := hzq' n
  have e10 := hzq (n + 1)
  have p1 := P_ne hq n
  have hinv : ∀ x : K, 1 - z⁻¹ * x = (z - x) / z := fun x => by field_simp
  simp only [hinv]
  clear hq hzq hzq'
  simp only [mul_add, add_mul, pow_add, pow_mul', pow_one, one_mul, mul_one] at *
  generalize P q n = A at *
  generalize Wn q z n = W at *
  generalize q ^ n = M at *
  simp only [true_or, if_true, show (1 + 1).choose 2 = 1 by rfl, pow_one, sub_zero]
  have hz1 : (1 : K) - z⁻¹ = (z - 1) / z := by field_simp
  rw [hz1]
  generalize hu1 : (1 - M * q) = u1 at *
  generalize hu2 : (1 - M * q * q) = u2 at *
  field_simp
  subst hu1 hu2
  ring

include hz hzq hzq' in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma sp_n1 (n : ℕ) :
    Fs q z (n + 2) (n + 1) - (1 + rho q z n) * Fs q z (n + 1) (n + 1) = Gs q z n (n + 2) - Gs q z n (n + 1) := by
  rw [Fs_of _ _ (by omega), Fs_of _ _ (by omega), Gs_of _ _ (by omega) (by omega), Gs_of _ _ (by omega) (by omega)]
  unfold rho
  have hc1 : (n + 1 + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hc2 : (n + 2 + 1).choose 2 = (n + 1).choose 2 + (n + 1) + (n + 2) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, show n + 2 = n + 1 + 1 by rfl, hc1]; ring
  rw [hc1, hc2]
  simp only [show n + 2 - (n + 1) = 1 by omega, show n + 1 - (n + 1) = 0 by omega, show n + 2 - (n + 2) = 0 by omega,
    show n + 2 + (n + 1) = 2 * n + 2 + 1 by omega, show n + 1 + (n + 1) = 2 * n + 2 by omega,
    show n + 1 + (n + 2) = 2 * n + 2 + 1 by omega, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
    show n + 2 = n + 1 + 1 by omega]
  simp only [P_succ, Wn_succ, show P q 0 = 1 by simp [P]]
  have e0 := hq (2 * n + 1)
  have e1 := hq (2 * n + 2)
  have e2 := hq 0
  have e5 := hq (n + 1)
  have e6 := hzq n
  have e9 := hzq' n
  have p2 := P_ne hq (2 * n)
  have e3 := hq (2 * n)
  have hinv : ∀ x : K, 1 - z⁻¹ * x = (z - x) / z := fun x => by field_simp
  simp only [hinv]
  clear hq hzq hzq'
  rw [show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring]
  simp only [mul_add, add_mul, pow_add, pow_mul', pow_one, one_mul, mul_one, zero_add] at *
  generalize P q (2 * n) = B at *
  generalize Wn q z n = W at *
  generalize (n + 1).choose 2 = c at *
  generalize q ^ c = Cq at *
  generalize q ^ (n ^ 2) = E at *
  generalize q ^ n = M at *
  generalize ((-1 : K) ^ n) = sg at *
  have hz1 : (1 : K) - z⁻¹ = (z - 1) / z := by field_simp
  rw [hz1]
  generalize hu1 : (1 - q) = u1 at *
  generalize hu2 : (1 - M ^ 2 * q) = u2 at *
  generalize hu3 : (1 - M ^ 2 * q * q) = u3 at *
  generalize hu4 : (1 - M ^ 2 * q ^ 2 * q) = u4 at *
  generalize hu5 : (1 - z * (M * q)) = u5 at *
  generalize hu6 : (z - M * q) = u6 at *
  generalize hu7 : (1 - M * q * q) = u7 at *
  field_simp
  subst hu1 hu2 hu3 hu4 hu5 hu6 hu7
  ring

include hz hzq hzq' in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma sp_top (n : ℕ) : Fs q z (n + 2) (n + 2) = -Gs q z n (n + 2) := by
  rw [Fs_of _ _ (by omega), Gs_of _ _ (by omega) (by omega)]
  have hc1 : (n + 1 + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hc2 : (n + 2 + 1).choose 2 = (n + 1).choose 2 + (n + 1) + (n + 2) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, show n + 2 = n + 1 + 1 by rfl, hc1]; ring
  rw [hc2]
  simp only [show n + 2 - (n + 2) = 0 by omega, show n + 2 + (n + 2) = 2 * n + 3 + 1 by omega,
    show n + 1 + (n + 2) = 2 * n + 3 by omega, show n + 2 - 1 = n + 1 by omega, show n + 2 = n + 1 + 1 by omega]
  simp only [P_succ, Wn_succ, show P q 0 = 1 by simp [P]]
  have e1 := hq (2 * n + 3)
  have e5 := hq (n + 1)
  have e6 := hzq (n + 1)
  have e9 := hzq' (n + 1)
  have p2 := P_ne hq (2 * n + 3)
  have e2 := hq (2 * n)
  have e3 := hq (2 * n + 1)
  have e4 := hq (2 * n + 2)
  have p3 := P_ne hq (2 * n)
  have hinv : ∀ x : K, 1 - z⁻¹ * x = (z - x) / z := fun x => by field_simp
  simp only [hinv]
  clear hq hzq hzq'
  rw [show (n + 1 + 1) ^ 2 = n ^ 2 + 4 * n + 4 by ring, show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring]
  simp only [mul_add, add_mul, pow_add, pow_mul', pow_one, one_mul, mul_one, zero_add] at *
  generalize P q (2 * n) = B at *
  generalize Wn q z n = W at *
  generalize (n + 1).choose 2 = c at *
  generalize q ^ c = Cq at *
  generalize q ^ (n ^ 2) = E at *
  generalize q ^ n = M at *
  generalize ((-1 : K) ^ n) = sg at *
  have hz1 : (1 : K) - z⁻¹ = (z - 1) / z := by field_simp
  rw [hz1]
  generalize hu2 : (1 - M ^ 2 * q) = u2 at *
  generalize hu3 : (1 - M ^ 2 * q * q) = u3 at *
  generalize hu4 : (1 - M ^ 2 * q ^ 2 * q) = u4 at *
  generalize hu8 : (1 - M ^ 2 * q ^ 3 * q) = u8 at *
  generalize hu5 : (1 - z * (M * q * q)) = u5 at *
  generalize hu6 : (z - M * q * q) = u6 at *
  generalize hu7 : (1 - M * q * q) = u7 at *
  field_simp
  subst hu2 hu3 hu4 hu8 hu5 hu6 hu7
  ring

include hz hzq hzq' in
lemma sp_step (n r : ℕ) (hr : r ≤ n) :
    Fs q z (n + 2) r - (1 + rho q z n) * Fs q z (n + 1) r + rho q z n * Fs q z n r = Gs q z n (r + 1) - Gs q z n r := by
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · exact sp_bot hq hz hzq hzq' n
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = d + t + 1 := ⟨n - t - 1, by omega⟩
    have := sp_mid hq hz hzq hzq' d t
    rw [show d + t + 3 = d + t + 1 + 2 by omega, show d + t + 2 = d + t + 1 + 1 by omega,
      show t + 2 = t + 1 + 1 by omega] at this
    exact this

include hz hzq hzq' in
theorem SF_rec (n : ℕ) : SF q z (n + 2) - (1 + rho q z n) * SF q z (n + 1) + rho q z n * SF q z n = 0 := by
  unfold SF
  rw [show n + 2 + 1 = (n + 1) + 1 + 1 by omega, sum_range_succ, sum_range_succ, sum_range_succ (fun r => Fs q z (n + 1) r)]
  have hD : ∑ r ∈ range (n + 1), (Fs q z (n + 2) r - (1 + rho q z n) * Fs q z (n + 1) r + rho q z n * Fs q z n r)
      = Gs q z n (n + 1) - Gs q z n 0 :=
    (sum_congr rfl fun r hr => sp_step hq hz hzq hzq' n r (by have := mem_range.mp hr; omega)).trans
      (sum_range_sub (fun s => Gs q z n s) (n + 1))
  have h0 : Gs q z n 0 = 0 := by simp [Gs]
  have hn1 := sp_n1 hq hz hzq hzq' n
  have htop := sp_top hq hz hzq hzq' n
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hD
  rw [show n + 1 + 1 = n + 2 by omega]
  linear_combination hD + hn1 + htop - h0

omit hz hzq hzq' in
lemma TS_succ (n : ℕ) : TS q z (n + 1) - TS q z n = tz q z (n + 1) := by
  unfold TS; rw [sum_range_succ]; ring

include hz hzq hzq' in
theorem SF_diff (n : ℕ) : SF q z (n + 1) - SF q z n = tz q z (n + 1) := by
  induction n with
  | zero =>
    unfold SF tz zp Fs Fr alL
    simp [Wn, P]
    have e0 := hq 0
    have e1 := hq 1
    rw [show (1 : ℕ) + 1 = 2 by rfl] at e1
    have e6 := hzq 0
    have e9 := hzq' 0
    simp only [pow_one, zero_add, one_mul] at *
    have hinv : ∀ x : K, 1 - z⁻¹ * x = (z - x) / z := fun x => by field_simp
    simp only [hinv]
    have hz1 : (1 : K) - z⁻¹ = (z - 1) / z := by field_simp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ, Finset.prod_range_zero,
      zero_add, if_true, show (1 : ℕ) ≠ 0 by omega, if_false, Nat.sub_zero, Nat.sub_self, add_zero, one_mul, mul_one,
      pow_zero, show (1 : ℕ) ^ 2 = 1 by rfl, show (0 : ℕ) ^ 2 = 0 by rfl, show (1 + 1).choose 2 = 1 by rfl, pow_one,
      show (1 : ℕ) + 1 = 2 by rfl, show (0 : ℕ) + 1 = 1 by rfl]
    rw [hz1]
    generalize hu1 : (1 - q) = u1 at *
    generalize hu2 : (1 - q ^ 2) = u2 at *
    generalize hu3 : (1 - z * q) = u3 at *
    generalize hu4 : (z - q) = u4 at *
    field_simp
    subst hu1 hu2 hu3 hu4
    ring
  | succ n ih =>
    have hr := SF_rec hq hz hzq hzq' n
    rw [tz_succ_succ hq, ← ih]
    linear_combination hr

include hz hzq hzq' in
/-- **The finite spt-crank identity**: `Σ_{r≤n} q^{r²}α_r W_n/((q)_{n−r}(q)_{n+r}) = Σ_{j≤n} (z)_j(z⁻¹)_j q^j/(q)_j`. -/
theorem SF_eq_TS (n : ℕ) : SF q z n = TS q z n := by
  induction n with
  | zero => simp [SF, TS, Fs, Fr, alL, Wn, P, tz, zp]
  | succ n ih =>
    have h1 := SF_diff hq hz hzq hzq' n
    have h2 := TS_succ (q := q) (z := z) hq n
    linear_combination h1 - h2 + ih

end SptSteps

end RankProof
