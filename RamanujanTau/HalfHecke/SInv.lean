import RamanujanTau.HalfHecke.SFacts

/-!
# The coset sum transforms correctly under `S`

With `cM = Q^{k−5/2} (−24/Q) e(3(Q−1)/24)`,

  `η(−1/z) · T F(−1/z) = z^k · η(z) · T F(z)`.

Each of the `Q² + Q` cosets is moved to another one by `S` (`transfer`): `d = 1 ↔ (d = Q², b = 0)`;
`(d = Q², Q ∤ b) ↔ (d = Q², b')` with `576bb' ≡ −1 (mod Q²)`; `(d = Q², b = Qb₁) ↔ (d = Q, b₂)` with
`576b₁b₂ ≡ −1 (mod Q)`. The multiplier factors are computed in `SFacts`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex ModularForm Finset
open RamanujanTau.ThetaLift
open scoped Real MatrixGroups

noncomputable section

variable {k : ℤ} (G : CuspForm 𝒮ℒ k) {Q : ℕ} [hQ : Fact Q.Prime] {z : ℂ}

variable (Q k) in
/-- The middle coefficient `Q^{k−5/2} (−24/Q) e(3(Q−1)/24)`. -/
def cMd : ℂ := (Q : ℂ) ^ (k - 3) * (Real.sqrt Q : ℂ) * chiQ Q (-24) * e24 (3 * Q - 3)

lemma im_aff {z : ℂ} (hz : 0 < z.im) {r : ℝ} (hr : 0 < r) (s : ℝ) {w : ℂ}
    (hw : w = (r : ℂ) * z + s) : 0 < w.im := by
  subst hw; simp only [add_im, ofReal_im, add_zero, Complex.mul_im, ofReal_re, zero_mul]
  exact mul_pos hr hz

section Powers
variable (Q)

lemma pw1 (hQ0 : (Q : ℂ) ≠ 0) : (Q : ℂ) ^ (2 * k - 3) = ((Q : ℂ) ^ k) ^ 2 / (Q : ℂ) ^ 3 := by
  rw [zpow_sub₀ hQ0, mul_comm, zpow_mul, zpow_two, zpow_ofNat, sq]

lemma pw2 (hQ0 : (Q : ℂ) ≠ 0) : (Q : ℂ) ^ (k - 3) = (Q : ℂ) ^ k / (Q : ℂ) ^ 3 := by
  rw [zpow_sub₀ hQ0, zpow_ofNat]

lemma rp_sq : ((((Q : ℝ) ^ 2 : ℝ)) : ℂ) ^ k = ((Q : ℂ) ^ k) ^ 2 := by
  push_cast
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

lemma rp_isq : (((((Q : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) ^ k = (((Q : ℂ) ^ k) ^ 2)⁻¹ := by
  rw [Complex.ofReal_inv, inv_zpow, rp_sq]

lemma rp_one : (((Q : ℝ) : ℝ) : ℂ) ^ k = (Q : ℂ) ^ k := by push_cast; rfl

lemma rp_inv : ((((Q : ℝ)⁻¹ : ℝ)) : ℂ) ^ k = ((Q : ℂ) ^ k)⁻¹ := by
  rw [Complex.ofReal_inv, inv_zpow]; push_cast; rfl

lemma sq_sq : (Real.sqrt ((Q : ℝ) ^ 2) : ℂ) = Q := by
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]; push_cast; rfl

lemma sq_isq : (Real.sqrt (((Q : ℝ) ^ 2)⁻¹) : ℂ) = (Q : ℂ)⁻¹ := by
  rw [Real.sqrt_inv, Real.sqrt_sq (Nat.cast_nonneg _)]; push_cast; rfl

lemma sq_inv : (Real.sqrt ((Q : ℝ)⁻¹) : ℂ) = ((Real.sqrt Q : ℝ) : ℂ)⁻¹ := by
  rw [Real.sqrt_inv]; push_cast; rfl

lemma sQ_sq : ((Real.sqrt Q : ℝ) : ℂ) ^ 2 = Q := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

end Powers

lemma Qpos : (0 : ℝ) < Q := by exact_mod_cast hQ.out.pos

/-! ### The five kinds of cosets -/

/-- `d = 1` goes to `d = Q²`, `b = 0`. -/
lemma case_V (hz : 0 < (z : ℂ).im) :
    η (-1 / z) * ((Q : ℂ) ^ (2 * k - 3) * Fc G ((Q : ℂ) ^ 2 * (-1 / z))) =
      z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ * Fc G (z / (Q : ℂ) ^ 2))) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hr : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by have := Qpos (Q := Q); positivity
  have hu : 0 < (z / (Q : ℂ) ^ 2).im :=
    im_aff hz hr 0 (by push_cast; ring)
  have ht := transfer G 0 (-1) 0 1 odd_one (by norm_num) hz hu hr
    (by push_cast; ring) (w := (Q : ℂ) ^ 2 * (-1 / z)) (by simp; field_simp)
  simp only [Nat.cast_one] at ht
  rw [mult_S, rp_isq, sq_isq] at ht
  rw [show η (-1 / z) * ((Q : ℂ) ^ (2 * k - 3) * Fc G ((Q : ℂ) ^ 2 * (-1 / z))) =
    (Q : ℂ) ^ (2 * k - 3) * (η (-1 / z) * Fc G ((Q : ℂ) ^ 2 * (-1 / z))) by ring, ht, pw1 Q hQ0]
  have hX : (Q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hQ0
  field_simp

/-- `d = Q²`, `b = 0` goes to `d = 1`. -/
lemma case_U0 (hz : 0 < (z : ℂ).im) :
    η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z) / (Q : ℂ) ^ 2)) =
      z ^ k * (η z * ((Q : ℂ) ^ (2 * k - 3) * Fc G ((Q : ℂ) ^ 2 * z))) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hr : (0 : ℝ) < (Q : ℝ) ^ 2 := by have := Qpos (Q := Q); positivity
  have hu : 0 < ((Q : ℂ) ^ 2 * z).im := im_aff hz hr 0 (by push_cast; ring)
  have ht := transfer G 0 (-1) 0 1 odd_one (by norm_num) hz hu hr
    (by push_cast; ring) (w := (-1 / z) / (Q : ℂ) ^ 2) (by simp; field_simp)
  simp only [Nat.cast_one] at ht
  rw [mult_S, rp_sq, sq_sq] at ht
  rw [show η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z) / (Q : ℂ) ^ 2)) =
    ((Q : ℂ) ^ 2)⁻¹ * (η (-1 / z) * Fc G ((-1 / z) / (Q : ℂ) ^ 2)) by ring, ht, pw1 Q hQ0]
  have hX : (Q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hQ0
  field_simp

/-- The integer relation behind `576 x σx = −1` in `ZMod (Q^m)`. -/
lemma rel_int {m : ℕ} [NeZero (Q ^ m)] (x y : ZMod (Q ^ m)) (h : 576 * x * y = -1) :
    ∃ t : ℤ, 576 * (x.val : ℤ) * (y.val : ℤ) + 1 = ((Q ^ m : ℕ) : ℤ) * t := by
  have h0 : ((576 * (x.val : ℤ) * (y.val : ℤ) + 1 : ℤ) : ZMod (Q ^ m)) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; linear_combination h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

lemma rel_int1 (x y : ZMod Q) (h : 576 * x * y = -1) :
    ∃ t : ℤ, 576 * (x.val : ℤ) * (y.val : ℤ) + 1 = (Q : ℤ) * t := by
  have h0 : ((576 * (x.val : ℤ) * (y.val : ℤ) + 1 : ℤ) : ZMod Q) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; linear_combination h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

lemma ne_of_rel (b b' t : ℤ) (h : 576 * b * b' + 1 = (Q : ℤ) * t) : ((-24 * b' : ℤ) : ZMod Q) ≠ 0 := by
  intro h0
  have h1 : ((576 * b * b' + 1 : ℤ) : ZMod Q) = 0 := by rw [h]; push_cast; simp
  push_cast at h0 h1
  have : (1 : ZMod Q) = 0 := by linear_combination h1 + (24 * (b : ZMod Q)) * h0
  exact one_ne_zero this

/-- `d = Q²`, `Q ∤ b` goes to `d = Q²`, `b' = σ(b)`. -/
lemma case_Unit (hQ5 : 5 ≤ Q) (hz : 0 < (z : ℂ).im) (x : ZMod (Q ^ 2)) (hx : ¬ Q ∣ x.val) :
    η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)) =
      z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ *
        Fc G ((z + 24 * ((sig (Q ^ 2) x).val : ℂ)) / (Q : ℂ) ^ 2))) := by
  haveI : NeZero (Q ^ 2) := ⟨pow_ne_zero _ hQ.out.ne_zero⟩
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hu1 : IsUnit x := (isUnit_iff_not_dvd 2 (by norm_num) x).mpr hx
  obtain ⟨t, ht⟩ := rel_int x (sig (Q ^ 2) x) (sig_spec hQ5 (by norm_num) hu1)
  set b : ℤ := (x.val : ℤ)
  obtain ⟨b', hb'⟩ : ∃ b' : ℤ, b' = ((sig (Q ^ 2) x).val : ℤ) := ⟨_, rfl⟩
  rw [← hb'] at ht
  have hb : ((-24 * b' : ℤ) : ZMod Q) ≠ 0 :=
    ne_of_rel b b' (Q * t) (by rw [ht]; push_cast; ring)
  have hdet : 24 * b * (-24 * b') - (-t) * ((Q ^ 2 : ℕ) : ℤ) = 1 := by linear_combination -ht
  have hr : (0 : ℝ) < 1 := one_pos
  have hu : 0 < ((z + 24 * (b' : ℂ)) / (Q : ℂ) ^ 2).im := by
    have hr2 : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by have := Qpos (Q := Q); positivity
    exact im_aff hz hr2 (24 * b' / (Q : ℝ) ^ 2) (by push_cast; ring)
  have htC : (576 : ℂ) * b * b' + 1 = (Q : ℂ) ^ 2 * t := by exact_mod_cast ht
  have htr := transfer G (24 * b) (-t) (-24 * b') (Q ^ 2) ((Q_odd hQ5).pow) hdet hz hu hr
    (z := z) (u := (z + 24 * (b' : ℂ)) / (Q : ℂ) ^ 2)
    (w := (-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)
    (by push_cast; field_simp; ring)
    (by rw [show (((Q ^ 2 : ℕ) : ℂ)) * ((z + 24 * (b' : ℂ)) / (Q : ℂ) ^ 2) + ((-24 * b' : ℤ) : ℂ) = z by
          push_cast; field_simp; ring]
        push_cast; field_simp; linear_combination (-1 : ℂ) * htC)
  rw [mult_Q2 hQ5 b b' t hb] at htr
  simp only [Complex.ofReal_one, one_zpow, Real.sqrt_one, div_one, mul_one, one_mul] at htr
  rw [show η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)) =
    ((Q : ℂ) ^ 2)⁻¹ * (η (-1 / z) * Fc G ((-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)) by ring, htr, hb']
  push_cast; ring

/-- `d = Q²`, `b = Qb₁` goes to `d = Q`, `b₂ = σ(b₁)`. -/
lemma case_Umul (hQ5 : 5 ≤ Q) (hz : 0 < (z : ℂ).im) (y : ZMod Q) (hy : y ≠ 0) :
    η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2)) =
      z ^ k * (η z * (cMd k Q * (chiQ Q (sig Q y) * Fc G (z + 24 * ((sig Q y).val : ℂ) / Q)))) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hrel := sig1_spec hQ5 hy
  obtain ⟨t, ht⟩ := rel_int1 y (sig Q y) hrel
  set b : ℤ := (y.val : ℤ)
  set b2 : ℤ := ((sig Q y).val : ℤ)
  have hb : ((-24 * b2 : ℤ) : ZMod Q) ≠ 0 := ne_of_rel b b2 t ht
  have hdet : 24 * b * (-24 * b2) - (-t) * (Q : ℤ) = 1 := by linear_combination -ht
  have hr : (0 : ℝ) < Q := Qpos
  have hu : 0 < (z + 24 * (b2 : ℂ) / Q).im :=
    im_aff hz one_pos (24 * b2 / Q) (by push_cast; ring)
  have htC : (576 : ℂ) * b * b2 + 1 = (Q : ℂ) * t := by exact_mod_cast ht
  have hiv : ((iota Q y).val : ℂ) = (Q : ℂ) * b := by rw [iota_val]; push_cast; rfl
  have htr := transfer G (24 * b) (-t) (-24 * b2) Q (Q_odd hQ5) hdet hz hu hr
    (z := z) (u := z + 24 * (b2 : ℂ) / Q)
    (w := (-1 / z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2)
    (by push_cast; field_simp; ring)
    (by rw [show ((Q : ℕ) : ℂ) * (z + 24 * (b2 : ℂ) / Q) + ((-24 * b2 : ℤ) : ℂ) = Q * z by
          push_cast; field_simp; ring, hiv]
        push_cast; field_simp; linear_combination (-1 : ℂ) * htC)
  rw [mult_Q hQ5 b b2 t hb, rp_one] at htr
  have hsig : (((-24 * b2 : ℤ)) : ZMod Q) = -24 * sig Q y := by
    simp only [b2]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [hsig, map_mul] at htr
  rw [show η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ * Fc G ((-1 / z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2)) =
    ((Q : ℂ) ^ 2)⁻¹ * (η (-1 / z) * Fc G ((-1 / z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2)) by ring, htr]
  have hs := sQ_sq Q
  have hs0 : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Qpos (Q := Q))).ne'
  have hb2 : ((b2 : ℤ) : ℂ) = (((sig Q y).val : ℕ) : ℂ) := by simp [b2]
  unfold cMd
  rw [pw2 Q hQ0, ← hs, hb2]
  have hX : (((Real.sqrt Q : ℝ) : ℂ) ^ 2) ^ k ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ hs0)
  field_simp

/-- `d = Q`, `b` goes to `d = Q²`, `b' = Q·σ(b)`. -/
lemma case_M (hQ5 : 5 ≤ Q) (hz : 0 < (z : ℂ).im) (y : ZMod Q) (hy : y ≠ 0) :
    η (-1 / z) * (cMd k Q * (chiQ Q y * Fc G (-1 / z + 24 * (y.val : ℂ) / Q))) =
      z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ *
        Fc G ((z + 24 * ((iota Q (sig Q y)).val : ℂ)) / (Q : ℂ) ^ 2))) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hrel := sig1_spec hQ5 hy
  obtain ⟨t, ht⟩ := rel_int1 y (sig Q y) hrel
  set b : ℤ := (y.val : ℤ)
  set b2 : ℤ := ((sig Q y).val : ℤ)
  have hb : ((-24 * b2 : ℤ) : ZMod Q) ≠ 0 := ne_of_rel b b2 t ht
  have hdet : 24 * b * (-24 * b2) - (-t) * (Q : ℤ) = 1 := by linear_combination -ht
  have hr : (0 : ℝ) < (Q : ℝ)⁻¹ := inv_pos.mpr Qpos
  have hiv : ((iota Q (sig Q y)).val : ℂ) = (Q : ℂ) * b2 := by rw [iota_val]; push_cast; rfl
  have hu : 0 < ((z + 24 * ((iota Q (sig Q y)).val : ℂ)) / (Q : ℂ) ^ 2).im := by
    have hr2 : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by have := Qpos (Q := Q); positivity
    exact im_aff hz hr2 (24 * Q * b2 / (Q : ℝ) ^ 2) (by rw [hiv]; push_cast; ring)
  have htC : (576 : ℂ) * b * b2 + 1 = (Q : ℂ) * t := by exact_mod_cast ht
  have htr := transfer G (24 * b) (-t) (-24 * b2) Q (Q_odd hQ5) hdet hz hu hr
    (z := z) (w := -1 / z + 24 * (y.val : ℂ) / Q)
    (by rw [hiv]; push_cast; field_simp; ring)
    (by rw [show ((Q : ℕ) : ℂ) * ((z + 24 * ((iota Q (sig Q y)).val : ℂ)) / (Q : ℂ) ^ 2) +
            ((-24 * b2 : ℤ) : ℂ) = z / Q by rw [hiv]; push_cast; field_simp; ring, hiv]
        push_cast; field_simp; linear_combination (-(Q : ℂ)) * htC)
  rw [mult_Q hQ5 b b2 t hb, rp_inv, sq_inv] at htr
  have hsig : (((-24 * b2 : ℤ)) : ZMod Q) = -24 * sig Q y := by
    simp only [b2]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [hsig, map_mul] at htr
  rw [show η (-1 / z) * (cMd k Q * (chiQ Q y * Fc G (-1 / z + 24 * (y.val : ℂ) / Q))) =
    cMd k Q * chiQ Q y * (η (-1 / z) * Fc G (-1 / z + 24 * (y.val : ℂ) / Q)) by ring, htr]
  -- the coefficient
  have h24 : (-24 : ZMod Q) ≠ 0 := by
    intro h; apply n576 hQ5; rw [show (576 : ZMod Q) = (-24) * (-24) by norm_num, h, zero_mul]
  have hc := chiQ_sq Q (-24) h24
  have hyy := chi_sig hQ5 hy
  have hm := chi_neg_one_e24 hQ5
  have hee : e24 (3 * Q - 3) * e24 (3 * Q - 3) = e24 (6 * ((Q : ℤ) - 1)) := by
    rw [← e24_add]; congr 1; ring
  have hs := sQ_sq Q
  have hs0 : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Qpos (Q := Q))).ne'
  have hX : (Q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hQ0
  have hcoef : cMd k Q * chiQ Q y * (chiQ Q (-24) * chiQ Q (sig Q y) * e24 (3 * Q - 3) *
      (((Q : ℂ) ^ k)⁻¹ / ((Real.sqrt Q : ℝ) : ℂ)⁻¹)) = ((Q : ℂ) ^ 2)⁻¹ := by
    unfold cMd
    rw [pw2 Q hQ0]
    have e : (Q : ℂ) ^ k / (Q : ℂ) ^ 3 * ((Real.sqrt Q : ℝ) : ℂ) * chiQ Q (-24) * e24 (3 * Q - 3) *
        chiQ Q y * (chiQ Q (-24) * chiQ Q (sig Q y) * e24 (3 * Q - 3) *
          (((Q : ℂ) ^ k)⁻¹ / ((Real.sqrt Q : ℝ) : ℂ)⁻¹)) =
        (((Real.sqrt Q : ℝ) : ℂ) ^ 2 / (Q : ℂ) ^ 3) * (chiQ Q (-24) * chiQ Q (-24)) *
          ((chiQ Q y * chiQ Q (sig Q y)) * (e24 (3 * Q - 3) * e24 (3 * Q - 3))) *
          ((Q : ℂ) ^ k * ((Q : ℂ) ^ k)⁻¹) := by
      field_simp
    rw [e, hc, hyy, hee, hm, mul_inv_cancel₀ hX, hs]
    field_simp
  linear_combination (z ^ k * (η z * Fc G ((z + 24 * ((iota Q (sig Q y)).val : ℂ)) / (Q : ℂ) ^ 2))) * hcoef

/-- **`S`-covariance of the coset sum**: `η(−1/z)·TF(−1/z) = z^k·η(z)·TF(z)`. -/
theorem TF_S (hQ5 : 5 ≤ Q) (hz : 0 < (z : ℂ).im) :
    η (-1 / z) * TF G Q (cMd k Q) (-1 / z) = z ^ k * (η z * TF G Q (cMd k Q) z) := by
  set s := univ.filter (fun y : ZMod Q => y ≠ 0)
  set u := univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val)
  have hL := sum_split Q (fun x => Fc G ((-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))
  have hR := sum_split Q (fun x => Fc G ((z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at hL hR
  have hM : ∀ w : ℂ, ∑ y : ZMod Q, chiQ Q y * Fc G (w + 24 * (y.val : ℂ) / Q) =
      ∑ y ∈ s, chiQ Q y * Fc G (w + 24 * (y.val : ℂ) / Q) := by
    intro w
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h; subst h; simp [MulChar.map_zero]
  unfold TF
  rw [hL, hR, hM, hM]
  have hA := case_V G (Q := Q) hz
  have hB := case_U0 G (Q := Q) hz
  have hC : η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ *
        ∑ y ∈ s, Fc G ((-1 / z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2)) =
      z ^ k * (η z * (cMd k Q * ∑ y ∈ s, chiQ Q y * Fc G (z + 24 * (y.val : ℂ) / Q))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun y hy => case_Umul G hQ5 hz y (by simpa [s] using hy)]
    exact sum_sig1 hQ5 (fun y => z ^ k * (η z * (cMd k Q * (chiQ Q y * Fc G (z + 24 * (y.val : ℂ) / Q)))))
  have hD : η (-1 / z) * (cMd k Q * ∑ y ∈ s, chiQ Q y * Fc G (-1 / z + 24 * (y.val : ℂ) / Q)) =
      z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ *
        ∑ y ∈ s, Fc G ((z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun y hy => case_M G hQ5 hz y (by simpa [s] using hy)]
    exact sum_sig1 hQ5 (fun y => z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ *
      Fc G ((z + 24 * ((iota Q y).val : ℂ)) / (Q : ℂ) ^ 2))))
  have hE : η (-1 / z) * (((Q : ℂ) ^ 2)⁻¹ *
        ∑ x ∈ u, Fc G ((-1 / z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)) =
      z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ * ∑ x ∈ u, Fc G ((z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x hx => case_Unit G hQ5 hz x (by simpa [u] using hx)]
    exact sum_sig2 hQ5 (fun x => z ^ k * (η z * (((Q : ℂ) ^ 2)⁻¹ *
      Fc G ((z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))))
  have hdiv : (-1 / z) / (Q : ℂ) ^ 2 = (-1 / z) / (Q : ℂ) ^ 2 := rfl
  linear_combination hA + hB + hC + hD + hE

end

end RamanujanTau.HalfHecke
