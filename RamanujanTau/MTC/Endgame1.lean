/-
# The MTC₀ endgame, part 1: reduction to a single theta identity

All Appell–Lerch sums in base `Q³⁰` (`Q = t^{168}`). From

* `hm03_xstar` + E1/E2/E3 (`main_x`): `J̄₀ (Q;Q)_∞ f₀ = 2 J₁ (A(Q¹⁴,−1) + Q⁻² A(Q⁴,−1)) + 2 κ₄₀ j(Q³;Q¹²) S`,
* `L5_lam` at `q = Q²` with (2.2a/b/c) (`hΦ`):
  `(1 + φ(Q²)) (Q¹⁰;Q¹⁰)_∞ = j₂₀ + Q²⁰ A(Q¹⁴,Q⁻²⁰) + Q² J³/j₆ + Q⁸ A(Q⁴,Q⁻¹⁰)`,
* four changes of `z` to `z₀ = Q⁴` (`I1`–`I4`), `LemA`, `LemB`,

the unknown values `A(Q¹⁴,Q⁴)`, `A(Q⁴,Q⁴)` cancel and

  `J̄₀ ((Q;Q)_∞ f₀ + 2 J₁ φ(Q²)) = 2 J₁ J³ Q⁻² j̄₆ j₁₀/(j₂ j₁₂ j₈) + 2 κ₄₀ j(Q³;Q¹²) S`   (`endgame_reduce`).
-/
import RamanujanTau.MTC.L5
import RamanujanTau.MTC.LamInv
import RamanujanTau.MTC.ThetaLem
import RamanujanTau.MTC.Zeros373
import RamanujanTau.MTC.KapJ
import RamanujanTau.MTC.Bridge

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-! ## `Av` versions of the Appell–Lerch facts -/

section AvL
variable {N : ℕ} (hN : 1 ≤ N)

lemma Av_eq_Alam {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Av hN ex cx ez cz = Alam hN hx hz hok := by
  unfold Av; rw [dif_pos ⟨hx, hz, hok⟩]

lemma Av_eq_Ab' {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz)
    (hlo : -N < ex + ez) (hhi : ex + ez < N) : Av hN ex cx ez cz = ALz.Ab hN hlo hhi cx cz := by
  rw [Av_eq_Alam hN hx hz hok]; exact Alam_eq_Ab hN hx hz hok hlo hhi

lemma Av_inv' {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Av hN (-ex) cx⁻¹ (-ez) cz⁻¹ = -(mono ex cx * mono (-ez) cz⁻¹) * Av hN ex cx ez cz := by
  rw [Av_eq_Alam hN (inv_ne_zero hx) (inv_ne_zero hz) (lamOK_inv hok), Av_eq_Alam hN hx hz hok]
  exact Alam_inv hN hx hz hok

lemma Av_zshift' {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Av hN ex cx ez cz = -mono ez cz * Av hN ex cx (ez + N) cz := by
  rw [Av_eq_Alam hN hx hz hok, Av_eq_Alam hN hx hz (lamOK_zshift hok)]
  exact Alam_zshift hN hx hz hok

lemma Av_N {N' : ℕ} (h : N = N') (hN' : 1 ≤ N') (ex : ℤ) (cx : ℂ) (ez : ℤ) (cz : ℂ) :
    Av hN ex cx ez cz = Av hN' ex cx ez cz := by subst h; rfl

end AvL

lemma mono_ne_one {e : ℤ} {c : ℂ} (he : e ≠ 0) : (mono e c : L) ≠ 1 := by
  intro h
  have := congrArg (fun f : L => f.coeff 0) h
  simp only [mono, HahnSeries.coeff_one, if_true, HahnSeries.coeff_single_of_ne (Ne.symm he)] at this
  exact zero_ne_one this

lemma lamOK_c1 (ex ez : ℤ) (h : ∀ m : ℤ, ex + ez ≠ 5040 * m) : LamOK (120 * 42) ex 1 ez 1 := fun r ⟨h1, _⟩ => by
  unfold wE at h1; push_cast at h1
  exact h (1 - r) (by linarith)

lemma lamOK_cm (ex ez : ℤ) : LamOK (120 * 42) ex 1 ez (-1) := fun r ⟨_, h2⟩ => by norm_num at h2

/-! ## The four changes of `z` (`J = (Q³⁰;Q³⁰)_∞`) -/

/-- `x = Q¹⁴`, `z₀ = Q⁴`, `z₁ = −1`. -/
lemma I1 : j30 4 * j30 18 * jb30 14 * Av (h120 hqT) 2352 1 0 (-1) -
    Av (h120 hqT) 2352 1 672 1 * j30 18 * jb30 0 * jb30 14 +
    mono 672 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * jb30 (-4) * jb30 18 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 2352) (b₀ := 672) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := -1)
    one_ne_zero one_ne_zero (by norm_num) (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero (by norm_num) (lamOK_cm 2352 0),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 2352 672 (by intro m; omega))] at h
  unfold j30 jb30
  norm_num at h ⊢
  linear_combination h

/-- `x = Q¹⁴`, `z₀ = Q⁴`, `z₁ = Q⁻²⁰`. -/
lemma I2 : j30 4 * j30 18 * j30 (-6) * Av (h120 hqT) 2352 1 (-3360) 1 -
    Av (h120 hqT) 2352 1 672 1 * j30 18 * j30 (-20) * j30 (-6) +
    mono 672 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 (-24) * j30 (-2) = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 2352) (b₀ := 672) (b₁ := -3360) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := 1)
    one_ne_zero one_ne_zero one_ne_zero (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 2352 (-3360) (by intro m; omega)),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 2352 672 (by intro m; omega))] at h
  unfold j30
  norm_num at h ⊢
  linear_combination h

/-- `x = Q⁴`, `z₀ = Q⁴`, `z₁ = −1`. -/
lemma I3 : j30 4 * j30 8 * jb30 4 * Av (h120 hqT) 672 1 0 (-1) -
    Av (h120 hqT) 672 1 672 1 * j30 8 * jb30 0 * jb30 4 +
    mono 672 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * jb30 (-4) * jb30 8 = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 672) (b₀ := 672) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := -1)
    one_ne_zero one_ne_zero (by norm_num) (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero (by norm_num) (lamOK_cm 672 0),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 672 672 (by intro m; omega))] at h
  unfold j30 jb30
  norm_num at h ⊢
  linear_combination h

/-- `x = Q⁴`, `z₀ = Q⁴`, `z₁ = Q⁻¹⁰`. -/
lemma I4 : j30 4 * j30 8 * j30 (-6) * Av (h120 hqT) 672 1 (-1680) 1 -
    Av (h120 hqT) 672 1 672 1 * j30 8 * j30 (-10) * j30 (-6) +
    mono 672 1 * -(ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 * j30 (-14) * j30 (-2) = 0 := by
  have h := change_of_z2 (h120 hqT) (a := 672) (b₀ := 672) (b₁ := -1680) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (cx := 1) (c₀ := 1) (c₁ := 1)
    one_ne_zero one_ne_zero one_ne_zero (mono_ne_one (by norm_num)) (mono_ne_one (by norm_num))
  rw [kappa_jacobi, ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 672 (-1680) (by intro m; omega)),
    ← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 672 672 (by intro m; omega))] at h
  unfold j30
  norm_num at h ⊢
  linear_combination h

/-! ## `L5` at `q = Q²` -/

lemma h336 : 1 ≤ 336 := by norm_num

lemma hs_LF (b : ℤ) : hs (LF h336 b) = Av (h120 hqT) ((18 - b) * ((336 : ℕ) : ℤ)) 1 (b * ((336 : ℕ) : ℤ)) 1 := by
  rw [← Av_N (h15 h336) (by norm_num) (h120 hqT), Av_eq_Alam (h15 h336) one_ne_zero one_ne_zero (lamOK18 h336 b)]
  rfl

lemma hA10 : Av (h120 hqT) 2688 1 3360 1 = j30 20 + mono 3360 1 * Av (h120 hqT) 2352 1 (-3360) 1 := by
  have q := Av_qshift (h120 hqT) (ex := -2352) (cx := 1) (ez := 3360) (cz := 1) one_ne_zero one_ne_zero
    (lamOK_c1 _ _ (by intro m; omega))
  have i := Av_inv' (h120 hqT) (ex := 2352) (ez := -3360) one_ne_zero one_ne_zero
    (lamOK_c1 2352 (-3360) (by intro m; omega))
  have e : (mono (-2352) 1 : L) * mono 2352 1 = 1 := by
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]; exact mono_ext (by norm_num) (by norm_num)
  rw [show (-2352 : ℤ) + ((120 * 42 : ℕ) : ℤ) = 2688 by norm_num] at q
  simp only [inv_one, neg_neg] at i
  unfold j30
  rw [show (168 : ℤ) * 20 = 3360 by norm_num]
  linear_combination q - (mono (-2352) 1 : L) * i + (mono 3360 1 * Av (h120 hqT) 2352 1 (-3360) 1) * e

lemma hA15 : j30 6 * Av (h120 hqT) 1008 1 5040 1 = (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 := by
  have z := Av_zshift' (h120 hqT) (ex := 1008) (ez := 0) one_ne_zero one_ne_zero (lamOK_c1 1008 0 (by intro m; omega))
  have k := kappa_eq_jacobi (h120 hqT) (a := 1008) (by norm_num) (by norm_num) (cx := 1) one_ne_zero
    (mono_ne_one (by norm_num))
  rw [← Av_eq_Ab' (h120 hqT) one_ne_zero one_ne_zero (lamOK_c1 1008 0 (by intro m; omega))] at k
  rw [show (mono 0 1 : L) = 1 from rfl] at z
  norm_num at z
  unfold j30
  norm_num
  linear_combination -k + θ (h120 hqT) 1008 1 * z

lemma hA20 : Av (h120 hqT) (-672) 1 6720 1 = mono 672 1 * Av (h120 hqT) 672 1 (-1680) 1 := by
  have z := Av_zshift' (h120 hqT) (ex := -672) (ez := 1680) one_ne_zero one_ne_zero
    (lamOK_c1 (-672) 1680 (by intro m; omega))
  have i := Av_inv' (h120 hqT) (ex := 672) (ez := -1680) one_ne_zero one_ne_zero
    (lamOK_c1 672 (-1680) (by intro m; omega))
  have e : (mono (-1680) 1 : L) * mono 1680 1 = 1 := by
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]; exact mono_ext (by norm_num) (by norm_num)
  rw [show (1680 : ℤ) + ((120 * 42 : ℕ) : ℤ) = 6720 by norm_num] at z
  simp only [inv_one, neg_neg] at i
  linear_combination (mono (-1680) 1 : L) * z - (mono (-1680) 1 : L) * i -
    (Av (h120 hqT) (-672) 1 6720 1 - mono 672 1 * Av (h120 hqT) 672 1 (-1680) 1) * e

/-- `(1 + φ(Q²))(Q¹⁰;Q¹⁰)_∞` in terms of `A(Q¹⁴, Q⁻²⁰)`, `A(Q⁴, Q⁻¹⁰)`. -/
theorem hΦ : ιN h336 (RankProof.Phi 1) * ιN h336 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) =
    j30 20 + mono 3360 1 * Av (h120 hqT) 2352 1 (-3360) 1 +
      mono 336 1 * (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 / j30 6 +
      mono 336 1 ^ 2 * (mono 672 1 * Av (h120 hqT) 672 1 (-1680) 1) := by
  have h := L5_lam h336
  rw [hs_LF, hs_LF, hs_LF] at h
  simp only [Nat.cast_ofNat] at h
  rw [show ((18 : ℤ) - 10) * 336 = 2688 by norm_num, show (10 : ℤ) * 336 = 3360 by norm_num,
    show ((18 : ℤ) - 15) * 336 = 1008 by norm_num, show (15 : ℤ) * 336 = 5040 by norm_num,
    show ((18 : ℤ) - 20) * 336 = -672 by norm_num, show (20 : ℤ) * 336 = 6720 by norm_num] at h
  have h6 := j30_ne 6 (by norm_num)
  have hv : Av (h120 hqT) 1008 1 5040 1 = (ιN (h120 hqT) MockTheta5.JTP.qfacInf) ^ 3 / j30 6 := by
    rw [eq_div_iff h6, mul_comm]; exact hA15
  rw [h, hA10, hA20, hv]
  ring

end MTC
