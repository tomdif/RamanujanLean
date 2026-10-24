/-
# Theta product identities by splitting to a common modulus

With `u = t^d` and the atoms `PA r M = ιN_d (u^r; u^M)_∞`:

* `θu`: `j(u^b; u^a) = Π_j PA(b + aj, ka) · Π_j PA(a − b + aj, ka) · Π_j PA(a + aj, ka)` (`1 ≤ b < a`);
* `θb`: `j(−u^b; u^a) = j(u^{2b}; u^{2a}) j(u^a; u^{2a}) / j(u^b; u^a)` (HM (1.4b) at `y = −x`), split likewise;
* `θb0`: `j(−1; u^a) = 2 j(−u^a; u^{4a})`.

A product identity between thetas then becomes an identity between monomials in the atoms, closed by
`field_simp; ring`.
-/
import RamanujanTau.MTC.ProdCalc
import RamanujanTau.MTC.Bridge
import RamanujanTau.MTC.ThetaMul
import RamanujanTau.MTC.GX373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

lemma h84 : 1 ≤ 84 := by norm_num

section Atoms
variable {d : ℕ} (hd : 1 ≤ d)

/-- the atom `(u^r; u^M)_∞`, `u = t^d`. -/
noncomputable def PA (r M : ℕ) : L := ιN hd (Pinf r M)

lemma PA_ne (r M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) : PA hd r M ≠ 0 :=
  ((isUnit_Pinf r M hr hM).map (ιN hd)).ne_zero

lemma ιN_Pinf_split (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    ιN hd (Pinf r a) = ∏ j ∈ range k, PA hd (r + a * j) (k * a) := by
  rw [Pinf_splitk r a k hr ha hk, map_prod]; rfl

/-- the split product of `J_{b,a}`. -/
noncomputable def PJ (b a k : ℕ) : L :=
  (∏ j ∈ range k, PA hd (b + a * j) (k * a)) * (∏ j ∈ range k, PA hd (a - b + a * j) (k * a)) *
    ∏ j ∈ range k, PA hd (a + a * j) (k * a)

lemma PJ_ne (b a k : ℕ) (hb : 1 ≤ b) (hab : b < a) (hk : 1 ≤ k) : PJ hd b a k ≠ 0 := by
  unfold PJ
  have hM : 1 ≤ k * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> exact prod_ne_zero_iff.mpr fun j _ => PA_ne hd _ _ (by omega) hM

/-- **unbarred theta as atoms**. -/
theorem θu {N : ℕ} (h : 1 ≤ N) (a b k : ℕ) (hN : N = d * a) (e : ℤ) (he : e = d * b) (hb : 1 ≤ b)
    (hab : b < a) (hk : 1 ≤ k) : θ h e 1 = PJ hd b a k := by
  subst hN he
  have := θ_eq_ιN_prod (d := d) (a := a) (b := b) hd hb hab h
  rw [show ((d * b : ℕ) : ℤ) = d * (b : ℤ) by push_cast; ring] at this
  rw [this, map_mul, map_mul, ιN_Pinf_split hd b a k hb (by omega) hk,
    ιN_Pinf_split hd (a - b) a k (by omega) (by omega) hk, ιN_Pinf_split hd a a k (by omega) (by omega) hk]
  rfl

/-- **barred theta as atoms**. -/
theorem θb {N : ℕ} (h : 1 ≤ N) (a b k : ℕ) (hN : N = d * a) (e : ℤ) (he : e = d * b) (hb : 1 ≤ b)
    (hab : b < a) (hk : 1 ≤ k) : θ h e (-1) = PJ hd (2 * b) (2 * a) k * PJ hd a (2 * a) k / PJ hd b a (2 * k) := by
  have hm := θ_mul h e e one_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)
  have hq : θ (h2N h) (2 * N + e - e) 1 = 0 := by
    rw [show (2 * N + e - e : ℤ) = ((2 * N : ℕ) : ℤ) * 1 by push_cast; ring]
    exact θ_qpow (h2N h) 1
  simp only [mul_neg, mul_one, neg_neg, div_neg, div_one, one_div] at hm
  rw [show (N + e - e : ℤ) = N by ring, hq, mul_zero, mul_zero, sub_zero] at hm
  have h1 : θ h e 1 = PJ hd b a (2 * k) := θu hd h a b (2 * k) hN e he hb hab (by omega)
  have h2 : θ (h2N h) (e + e) 1 = PJ hd (2 * b) (2 * a) k :=
    θu hd (h2N h) (2 * a) (2 * b) k (by rw [hN]; ring) (e + e) (by rw [he]; push_cast; ring) (by omega) (by omega) hk
  have h3 : θ (h2N h) N 1 = PJ hd a (2 * a) k :=
    θu hd (h2N h) (2 * a) a k (by rw [hN]; ring) N (by rw [hN]; push_cast; ring) (by omega) (by omega) hk
  rw [h1, h2, h3] at hm
  have hne := PJ_ne hd b a (2 * k) hb hab (by omega)
  rw [eq_div_iff hne, mul_comm]
  exact hm

lemma inv_m' {N : ℕ} (hN : 1 ≤ N) (e : ℤ) : θ hN (-e) (-1) = -mono (-e) (-1) * θ hN e (-1) := by
  have h := θ_inv hN e (by norm_num : (-1 : ℂ) ≠ 0)
  rwa [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h

/-- **`j(−1; u^a) = 2 j(−u^a; u^{4a})`** as atoms. -/
theorem θb0 {N : ℕ} (h : 1 ≤ N) (a k : ℕ) (hN : N = d * a) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    θ h 0 (-1) = 2 * (PJ hd (2 * a) (2 * (4 * a)) k * PJ hd (4 * a) (2 * (4 * a)) k / PJ hd a (4 * a) (2 * k)) := by
  have hdis := dissect2 h 0 (by norm_num : (-1 : ℂ) ≠ 0)
  simp only [mul_zero, add_zero, zero_sub, sub_zero, show ((-1 : ℂ)) ^ 2 = 1 by norm_num,
    show -((-1 : ℂ))⁻¹ = 1 by norm_num] at hdis
  rw [inv_m'] at hdis
  have hmm : (mono N 1 : L) * -mono (-(N : ℤ)) (-1) = 1 := by
    rw [show -(mono (-(N : ℤ)) (-1) : L) = mono (-(N : ℤ)) 1 by simp [mono], mono_mul,
      show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  have hb := θb hd (hN' h 2 two_pos) (4 * a) a k (by rw [hN]; ring) N (by rw [hN]; push_cast; ring) ha (by omega) hk
  rw [show (mono 0 1 : L) = 1 from rfl, one_mul] at hdis
  rw [hdis, ← hb]
  linear_combination θ (hN' h 2 two_pos) N (-1) * hmm

end Atoms

/-- test: `J_{6,15} J_{12,60} = J_{3,12} J̄_{3,30}` (base `Q = u²`). -/
example (h1 : 1 ≤ 2520) (h2 : 1 ≤ 10080) (h3 : 1 ≤ 2016) (h4 : 1 ≤ 5040) :
    θ h1 1008 1 * θ h2 2016 1 = θ h3 504 1 * θ h4 504 (-1) := by
  rw [θu h84 h1 30 12 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h84 h2 120 24 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h84 h3 24 6 5 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h84 h4 60 6 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h84 r 120 ≠ 0 := fun r hr => PA_ne h84 r 120 hr (by norm_num)
  field_simp [hP]

end MTC
