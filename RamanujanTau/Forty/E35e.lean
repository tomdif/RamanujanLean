/-
# Entry 3.35: barred thetas as products, and `L47` in product form

* `fb e N = f(q^e, q^{N−e}) = J_{2e,2N} J_{N,2N} / J_{e,N}` and `fb0 N = f(1, q^N) = 2ψ(q^N)`, with
  `θ_N(e, −1) = ι(fb e N)` (`θfb`, from `θ_bar`) and `θ_N(0, −1) = ι(fb0 N)` (`θfb0`, from `θ_bar0`).
* `S_fb`, `S_fb0`: `S k` scales both arguments.
* `Ng_fb_odd`: for `e` odd and `N` even, `f(q^e, q^{N−e}) ↦ f(−q^e, −q^{N−e}) = J_{e,N}` under `q ↦ −q`;
  `Ng_fb_even`, `Ng_fb0`: thetas in `q²` are fixed.
* The theta series of the three classes of discriminant `−47` in product form:
  `T1 = Θ(x²+xy+12y²) = φ(q)φ(Q) + 4q¹²ψ(q²)ψ(Q²)`,
  `T2 = Θ(2x²+xy+6y²) = φ(q²)φ(Q²) + 2q⁶ψ(q)ψ(Q) + 4q²⁴ψ(q⁴)ψ(Q⁴)`,
  `T3 = Θ(3x²+xy+4y²) = φ(q³)φ(Q³) + 2q⁴f(q²,q⁴)f(Q²,Q⁴) + 2q¹⁶f(q,q⁵)f(Q,Q⁵) + 4q³⁶ψ(q⁶)ψ(Q⁶)` (`Q = q⁴⁷`).
* `E47`: `T2 − T3 = 2q² f(−q)f(−Q)` (`L47` in product form).
-/
import RamanujanTau.Forty.E35d
import RamanujanTau.Forty.E35

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

lemma isUnit_J (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : IsUnit (J e N) := by
  unfold J
  exact ((isUnit_Pinf e N h1 (by omega)).mul (isUnit_Pinf (N - e) N (by omega) (by omega))).mul
    (isUnit_Pinf N N (by omega) (by omega))

lemma ι_ne_zero_of_unit {x : PowerSeries ℤ} (hx : IsUnit x) : ι x ≠ 0 := fun h =>
  hx.ne_zero (ι_inj (h.trans (map_zero ι).symm))

lemma map_inverse_unit (f : PowerSeries ℤ →+* PowerSeries ℤ) {x : PowerSeries ℤ} (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  have h1 : f x * f (Ring.inverse x) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel _ hx, map_one]
  have h2 := Ring.inverse_mul_cancel _ (hx.map f)
  calc f (Ring.inverse x) = (Ring.inverse (f x) * f x) * f (Ring.inverse x) := by rw [h2, one_mul]
    _ = Ring.inverse (f x) := by rw [mul_assoc, h1, mul_one]

/-- `f(q^e, q^{N−e})` (for `0 < e < N`). -/
noncomputable def fb (e N : ℕ) : PowerSeries ℤ := J (2 * e) (2 * N) * J N (2 * N) * Ring.inverse (J e N)

/-- `f(1, q^N) = 2ψ(q^N)`. -/
noncomputable def fb0 (N : ℕ) : PowerSeries ℤ := 2 * Pinf (2 * N) (2 * N) * Ring.inverse (Pinf N (2 * N))

lemma fb_mul (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : fb e N * J e N = J (2 * e) (2 * N) * J N (2 * N) := by
  rw [fb, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_J e N h1 h2), mul_one]

lemma fb0_mul (N : ℕ) (h : 1 ≤ N) : fb0 N * Pinf N (2 * N) = 2 * Pinf (2 * N) (2 * N) := by
  rw [fb0, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_Pinf N (2 * N) h (by omega)), mul_one]

lemma θfb {N : ℕ} (h : 1 ≤ N) (e : ℕ) {e' : ℤ} (he : e' = e) (h1 : 1 ≤ e) (h2 : e < N) :
    θ h e' (-1) = ι (fb e N) := by
  subst he
  apply mul_right_cancel₀ (ι_ne_zero_of_unit (isUnit_J e N h1 h2))
  rw [θ_bar h e h1 h2, ← map_mul, fb_mul e N h1 h2]

lemma θfb0 {N : ℕ} [NeZero N] (h : 1 ≤ N) : θ h 0 (-1) = ι (fb0 N) := by
  have hu := isUnit_Pinf N (2 * N) h (by omega)
  apply mul_right_cancel₀ (ι_ne_zero_of_unit hu)
  rw [θ_bar0 h, ← map_mul, fb0, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one, map_mul, map_ofNat]

lemma S_fb (k : ℕ) [NeZero k] (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) {e' N' : ℕ} (he : e' = k * e)
    (hN : N' = k * N) : S k (fb e N) = fb e' N' := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  subst he hN
  simp only [fb, map_mul, map_inverse_unit _ (isUnit_J e N h1 h2), S_J k e N h1 h2,
    S_J k (2 * e) (2 * N) (by omega) (by omega), S_J k N (2 * N) (by omega) (by omega)]
  rw [show k * (2 * e) = 2 * (k * e) by ring, show k * (2 * N) = 2 * (k * N) by ring]

lemma S_fb0 (k : ℕ) [NeZero k] (N : ℕ) (h : 1 ≤ N) {N' : ℕ} (hN : N' = k * N) : S k (fb0 N) = fb0 N' := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  subst hN
  simp only [fb0, map_mul, map_ofNat, map_inverse_unit _ (isUnit_Pinf N (2 * N) h (by omega)),
    S_Pinf k N (2 * N) h (by omega), S_Pinf k (2 * N) (2 * N) (by omega) (by omega)]
  rw [show k * (2 * N) = 2 * (k * N) by ring]

lemma J_Ng_J (e N : ℕ) (he : Odd e) (hN : Even N) (h2 : e < N) :
    J e N * Ng (J e N) = J (2 * e) (2 * N) * J N (2 * N) := by
  obtain ⟨m, rfl⟩ := hN
  have h1 : 1 ≤ e := he.pos
  have ho : Odd (m + m - e) := by
    obtain ⟨k, hk⟩ := he
    exact ⟨m - k - 1, by omega⟩
  have hev : Even (m + m) := ⟨m, rfl⟩
  have a1 := Ng_mul_odd e (m + m) he hev (by omega)
  have a2 := Ng_mul_odd (m + m - e) (m + m) ho hev (by omega)
  have a3 : Ng (Pinf (m + m) (m + m)) = Pinf (m + m) (m + m) := by
    have := Ng_Pinf_even m m (by omega) (by omega)
    rwa [show 2 * m = m + m by ring] at this
  have sp := Pinf_split' (m + m) (m + m) (by omega) (by omega) (rfl : 2 * (m + m) = 2 * (m + m)) rfl
  simp only [J, map_mul, a3]
  rw [show 2 * (m + m) - 2 * e = 2 * (m + m - e) by omega, show 2 * (m + m) - (m + m) = m + m by omega,
    ← a1, ← a2, sp, show m + m + (m + m) = 2 * (m + m) by ring]
  ring

lemma Ng_fb_odd (e N : ℕ) (he : Odd e) (hN : Even N) (h2 : e < N) : Ng (fb e N) = J e N := by
  have h1 : 1 ≤ e := he.pos
  obtain ⟨m, hm⟩ := hN
  have hu := isUnit_J e N h1 h2
  have hnum : Ng (J (2 * e) (2 * N) * J N (2 * N)) = J (2 * e) (2 * N) * J N (2 * N) := by
    simp only [J, map_mul]
    rw [show 2 * N - 2 * e = 2 * (N - e) by omega, show 2 * N - N = N by omega]
    simp only [Ng_Pinf_even _ _ (by omega : 1 ≤ e) (by omega : 1 ≤ N),
      Ng_Pinf_even _ _ (by omega : 1 ≤ N - e) (by omega : 1 ≤ N), Ng_Pinf_even N N (by omega) (by omega)]
    rw [show N = 2 * m by omega, Ng_Pinf_even m (2 * m) (by omega) (by omega)]
  have hJ := J_Ng_J e N he ⟨m, hm⟩ h2
  have hNu : IsUnit (Ng (J e N)) := hu.map Ng
  apply mul_left_cancel₀ hNu.ne_zero
  rw [← map_mul, mul_comm (J e N) (fb e N), fb_mul e N h1 h2, hnum, mul_comm (Ng (J e N)), hJ]

lemma Ng_fb_even (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : Ng (fb (2 * e) (2 * N)) = fb (2 * e) (2 * N) := by
  rw [← S_fb 2 e N h1 h2 rfl rfl, Ng_S_ev 2 (dvd_refl 2)]

lemma Ng_fb0 (N : ℕ) (h : 1 ≤ N) : Ng (fb0 (2 * N)) = fb0 (2 * N) := by
  rw [← S_fb0 2 N h rfl, Ng_S_ev 2 (dvd_refl 2)]

/-! ## the three theta series of discriminant `−47` -/

/-- `Θ(x²+xy+12y²) = φ(q)φ(Q) + 4q¹²ψ(q²)ψ(Q²)`. -/
noncomputable def T1 : PowerSeries ℤ := fb 1 2 * fb 47 94 + X ^ 12 * (fb0 2 * fb0 94)
/-- `Θ(2x²+xy+6y²) = φ(q²)φ(Q²) + 2q⁶ψ(q)ψ(Q) + 4q²⁴ψ(q⁴)ψ(Q⁴)`. -/
noncomputable def T2 : PowerSeries ℤ :=
  fb 2 4 * fb 94 188 + 2 * X ^ 6 * (fb 1 4 * fb 47 188) + X ^ 24 * (fb0 4 * fb0 188)
/-- `Θ(3x²+xy+4y²) = φ(q³)φ(Q³) + 2q⁴f(q²,q⁴)f(Q²,Q⁴) + 2q¹⁶f(q,q⁵)f(Q,Q⁵) + 4q³⁶ψ(q⁶)ψ(Q⁶)`. -/
noncomputable def T3 : PowerSeries ℤ :=
  fb 3 6 * fb 141 282 + 2 * X ^ 4 * (fb 2 6 * fb 94 282) + 2 * X ^ 16 * (fb 1 6 * fb 47 282)
    + X ^ 36 * (fb0 6 * fb0 282)

private lemma monoT (k : ℕ) : (mono (k : ℤ) 1 : L) = mono 1 1 ^ k := by
  rw [mono, single_pow]; simp

lemma S2X : S 2 X = X ^ 2 := RankProof.Ea_X 2 _

/-- **`L47` in product form**: `Θ(2x²+xy+6y²) − Θ(3x²+xy+4y²) = 2q² f(−q)f(−q⁴⁷)`. -/
theorem E47 : T2 - T3 = 2 * X ^ 2 * (J 1 3 * J 47 141) := by
  apply S_inj 2
  have h := L47
  rw [θfb (by norm_num : 1 ≤ 8) 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 376) 188 (e' := 188) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 8) 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 376) 94 (e' := 94) (by norm_num) (by norm_num) (by norm_num),
    θfb0 (N := 8) (by norm_num), θfb0 (N := 376) (by norm_num),
    θfb (by norm_num : 1 ≤ 12) 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 564) 282 (e' := 282) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 12) 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 564) 188 (e' := 188) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 12) 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θfb (by norm_num : 1 ≤ 564) 94 (e' := 94) (by norm_num) (by norm_num) (by norm_num),
    θfb0 (N := 12) (by norm_num), θfb0 (N := 564) (by norm_num),
    θu' (by norm_num : 1 ≤ 6) 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' (by norm_num : 1 ≤ 282) 94 (e' := 94) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [show (mono 4 1 : L) = mono 1 1 ^ 4 from monoT 4, show (mono 8 1 : L) = mono 1 1 ^ 8 from monoT 8,
    show (mono 12 1 : L) = mono 1 1 ^ 12 from monoT 12, show (mono 32 1 : L) = mono 1 1 ^ 32 from monoT 32,
    show (mono 48 1 : L) = mono 1 1 ^ 48 from monoT 48, show (mono 72 1 : L) = mono 1 1 ^ 72 from monoT 72] at h
  apply ι_inj
  simp only [T2, T3, map_sub, map_add, map_mul, map_pow, map_ofNat, S2X,
    S_fb 2 2 4 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 8 = 2 * 4),
    S_fb 2 94 188 (by norm_num) (by norm_num) (rfl : 188 = 2 * 94) (rfl : 376 = 2 * 188),
    S_fb 2 1 4 (by norm_num) (by norm_num) (rfl : 2 = 2 * 1) (rfl : 8 = 2 * 4),
    S_fb 2 47 188 (by norm_num) (by norm_num) (rfl : 94 = 2 * 47) (rfl : 376 = 2 * 188),
    S_fb0 2 4 (by norm_num) (rfl : 8 = 2 * 4), S_fb0 2 188 (by norm_num) (rfl : 376 = 2 * 188),
    S_fb 2 3 6 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 12 = 2 * 6),
    S_fb 2 141 282 (by norm_num) (by norm_num) (rfl : 282 = 2 * 141) (rfl : 564 = 2 * 282),
    S_fb 2 2 6 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 12 = 2 * 6),
    S_fb 2 94 282 (by norm_num) (by norm_num) (rfl : 188 = 2 * 94) (rfl : 564 = 2 * 282),
    S_fb 2 1 6 (by norm_num) (by norm_num) (rfl : 2 = 2 * 1) (rfl : 12 = 2 * 6),
    S_fb 2 47 282 (by norm_num) (by norm_num) (rfl : 94 = 2 * 47) (rfl : 564 = 2 * 282),
    S_fb0 2 6 (by norm_num) (rfl : 12 = 2 * 6), S_fb0 2 282 (by norm_num) (rfl : 564 = 2 * 282),
    S_J 2 1 3 (by norm_num) (by norm_num), S_J 2 47 141 (by norm_num) (by norm_num), ι_X]
  simp only [Nat.reduceMul, ← pow_mul]
  linear_combination h

end Forty
