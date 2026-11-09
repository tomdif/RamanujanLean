/-
# Tools for the forty identities: theta normal forms, the two-term shape, injectivity of `q ↦ q^a`
-/
import RamanujanTau.Forty.Bridge
import RamanujanTau.Forty.Chi

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

lemma θu' {N : ℕ} (h : 1 ≤ N) (e : ℕ) {e' : ℤ} (he : e' = e) (h1 : 1 ≤ e) (h2 : e < N) :
    θ h e' 1 = ι (J e N) := by
  rw [he]; exact θ_unb h e h1 h2

lemma θ_zero_pt {N : ℕ} (h : 1 ≤ N) : θ h 0 1 = 0 := θ_one h

lemma θ_refl1 {N : ℕ} (h : 1 ≤ N) (e e' : ℤ) (he : e' = N - e) : θ h e' 1 = θ h e 1 := by
  rw [he, ← θ_reflect h e one_ne_zero, inv_one]

lemma θ_reflm {N : ℕ} (h : 1 ≤ N) (e e' : ℤ) (he : e' = N - e) : θ h e' (-1) = θ h e (-1) := by
  rw [he, ← θ_reflect h e (by norm_num : (-1 : ℂ) ≠ 0), inv_neg, inv_one]

/-- the generic two-term shape: from `(zw + kxy)·den = num·xyzw` and `Ax = By = Cz = Dw = 1`,
`(AB + kCD)·den = num`. -/
lemma two_term {A B C D x y z w k den num : PowerSeries ℤ} (hA : A * x = 1) (hB : B * y = 1)
    (hC : C * z = 1) (hD : D * w = 1) (core : (z * w + k * x * y) * den = num * (x * y * z * w)) :
    (A * B + k * C * D) * den = num := by
  linear_combination (A * B * C * D) * core + (-(A * B * den * (D * w)) + num * (D * w)) * hC
    + (-(A * B * den) + num) * hD + (-(k * C * D * den * (B * y)) + num * (B * y) * (C * z) * (D * w)) * hA
    + (-(k * C * D * den) + num * (C * z) * (D * w)) * hB

lemma eq_mul_inv_of {a b c : PowerSeries ℤ} (hc : IsUnit c) (h : a * c = b) : a = b * Ring.inverse c := by
  rw [← h, mul_assoc, Ring.mul_inverse_cancel _ hc, mul_one]

lemma two_ne : (2 : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

lemma ne_zero_of_unit {a : PowerSeries ℤ} (h : IsUnit a) : a ≠ 0 := h.ne_zero

/-- quasi-periodicity in normal form: `θ_N(e₀ + N s, c) = t^E C θ_N(e₀, c)`. -/
lemma θ_sh {N : ℕ} (h : 1 ≤ N) {e : ℤ} (e0 s : ℤ) {c : ℂ} (hc : c ≠ 0) (E : ℤ) (C : ℂ) (he : e = e0 + N * s)
    (hE : E = -(N * c2 (s + 1)) - e0 * s + N * s) (hC : C = (-1) ^ s * c ^ (-s)) :
    θ h e c = mono E C * θ h e0 c := by
  rw [he, θ_qshift h e0 hc s, hE, hC]

lemma θz' {N : ℕ} (h : 1 ≤ N) (m : ℤ) {e : ℤ} (he : e = N * m) : θ h e 1 = 0 := by
  rw [he]; exact θ_qpow h m

lemma S_inj (a : ℕ) [NeZero a] : Function.Injective (S a) := fun f g h => by
  ext n
  have := congrArg (PowerSeries.coeff (a * n)) h
  simp only [S, RankProof.coeff_Ea, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a))] at this
  exact this

lemma mono_neg1 (E : ℤ) : (mono E (-1) : L) = -mono E 1 := by simp [mono]

lemma ι_Xpow' (E : ℕ) {E' : ℤ} (h : E' = E) : (mono E' 1 : L) = ι (PowerSeries.X ^ E) := by
  rw [ι_Xpow, h]

/-! ## normalising products of monomials and thetas (simp set `mono_nf`) -/

lemma θ_mono_comm {N : ℕ} (h : 1 ≤ N) (e : ℤ) (c : ℂ) (E : ℤ) (C : ℂ) (x : L) :
    θ h e c * (mono E C * x) = mono E C * (θ h e c * x) := by ring

lemma θ_mono_comm' {N : ℕ} (h : 1 ≤ N) (e : ℤ) (c : ℂ) (E : ℤ) (C : ℂ) :
    θ h e c * mono E C = mono E C * θ h e c := by ring

lemma mono_mono (a c : ℤ) (b d : ℂ) (x : L) : mono a b * (mono c d * x) = mono (a + c) (b * d) * x := by
  rw [← mul_assoc, mono_mul]

lemma θ_nfr1 {N : ℕ} (h : 1 ≤ N) {e : ℤ} (g s : ℤ) (E : ℤ) (C : ℂ) (he : e = (N - g) + N * s)
    (hE : E = -(N * c2 (s + 1)) - (N - g) * s + N * s) (hC : C = (-1) ^ s) :
    θ h e 1 = mono E C * θ h g 1 := by
  rw [θ_sh h (N - g) s one_ne_zero E C he hE (by rw [hC]; simp), θ_refl1 h g (N - g) rfl]

lemma θ_nfrm {N : ℕ} (h : 1 ≤ N) {e : ℤ} (g s : ℤ) (E : ℤ) (C : ℂ) (he : e = (N - g) + N * s)
    (hE : E = -(N * c2 (s + 1)) - (N - g) * s + N * s) (hC : C = (-1) ^ s * (-1) ^ (-s)) :
    θ h e (-1) = mono E C * θ h g (-1) := by
  rw [θ_sh h (N - g) s (by norm_num) E C he hE hC, θ_reflm h g (N - g) rfl]

lemma S_J (a : ℕ) [NeZero a] (e N : ℕ) (he : 1 ≤ e) (heN : e < N) : S a (J e N) = J (a * e) (a * N) := by
  simp only [J, map_mul]
  rw [S_Pinf a e N he (by omega), S_Pinf a (N - e) N (by omega) (by omega), S_Pinf a N N (by omega) (by omega),
    Nat.mul_sub]

lemma G_E : G * Pinf 1 1 = J 2 5 := by
  have hs := MockTheta5.JTP.RR.Pinf_split5
  simp only [prod_range_succ, prod_range_zero, one_mul] at hs
  norm_num at hs
  have hG := G_mul_uu
  rw [hs, J]
  simp only [uu] at hG
  norm_num
  linear_combination (Pinf 2 5 * Pinf 3 5 * Pinf 5 5) * hG

lemma H_E : H * Pinf 1 1 = J 1 5 := by
  have hs := MockTheta5.JTP.RR.Pinf_split5
  simp only [prod_range_succ, prod_range_zero, one_mul] at hs
  norm_num at hs
  have hH := H_mul_vv
  rw [hs, J]
  simp only [vv] at hH
  norm_num
  linear_combination (Pinf 1 5 * Pinf 4 5 * Pinf 5 5) * hH

/-- `G(q^a) f(−q^a) = f(−q^{2a}, −q^{3a})`. -/
lemma SG_E (a : ℕ) [NeZero a] : S a G * Pinf a a = J (2 * a) (5 * a) := by
  have h := congrArg (S a) G_E
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)
  rw [map_mul, S_Pinf a 1 1 le_rfl le_rfl, S_J a 2 5 (by norm_num) (by norm_num), mul_one] at h
  rw [h, mul_comm 2 a, mul_comm 5 a]

/-- `H(q^a) f(−q^a) = f(−q^a, −q^{4a})`. -/
lemma SH_E (a : ℕ) [NeZero a] : S a H * Pinf a a = J a (5 * a) := by
  have h := congrArg (S a) H_E
  rw [map_mul, S_Pinf a 1 1 le_rfl le_rfl, S_J a 1 5 (by norm_num) (by norm_num), mul_one] at h
  rw [h, mul_comm 5 a]

lemma Pinf_ne (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : Pinf b a ≠ 0 := (isUnit_Pinf b a hb ha).ne_zero

end Forty
