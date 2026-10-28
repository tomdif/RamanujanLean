/-
# The Tate addition theorem over `T`, then over `R3 = ℚ[a,c]⟦b⟧`

With `P(u)`, `P(v)` (`v = 1 + t`), `P(uv)` the three Tate points in `T` (scaled short model),
the chord sum `P(u) + P(v)` (computed in the regular form `Xc = X₁ + t·Rt·Dl⁻²`,
`Yc = −(Nl·Rt·Dl⁻³ + Y₁)`) is killed by `D` (translation invariance, `invX`/`invY`) and agrees with
`P(uv)` at `t = 0`; by uniqueness (`eq_zero_of_D`) it is `P(uv)` (`Xc_eq`, `Yc_eq`).

Cleared of denominators this is `Ix = Iy = 0` (`chord_T`), and since `Ψ : R3 → T` is injective,
`chord_R3`: the identity holds in `ℚ[a][c]⟦b⟧`, ready to be specialised.
-/
import RamanujanTau.TateAdd.Points

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot

/-! ### Cleared chord identities -/

section Ichord
variable {R : Type*} [CommRing R]

/-- `x`-chord identity `(X₃ + X₁ + X₂)(X₁ − X₂)² = (Y₁ − Y₂)²` for `Xᵢ = cXᵢ/dᵢ²`, `Yᵢ = cYᵢ/dᵢ³`,
cleared of denominators. -/
def Ix (cX1 cY1 d1 cX2 cY2 d2 cX3 d3 : R) : R :=
  (cX3 * d1 ^ 2 * d2 ^ 2 + cX1 * d2 ^ 2 * d3 ^ 2 + cX2 * d1 ^ 2 * d3 ^ 2) *
    (cX1 * d2 ^ 2 - cX2 * d1 ^ 2) ^ 2 - (cY1 * d2 ^ 3 - cY2 * d1 ^ 3) ^ 2 * d3 ^ 2

/-- `y`-chord identity `(Y₃ + Y₁)(X₁ − X₂) + (Y₁ − Y₂)(X₃ − X₁) = 0`, cleared. -/
def Iy (cX1 cY1 d1 cX2 cY2 d2 cX3 cY3 d3 : R) : R :=
  (cY3 * d1 ^ 3 + cY1 * d3 ^ 3) * (cX1 * d2 ^ 2 - cX2 * d1 ^ 2) * d2 +
    (cY1 * d2 ^ 3 - cY2 * d1 ^ 3) * (cX3 * d1 ^ 2 - cX1 * d3 ^ 2) * d3

lemma Ix_map {S : Type*} [CommRing S] (f : R →+* S) (cX1 cY1 d1 cX2 cY2 d2 cX3 d3 : R) :
    f (Ix cX1 cY1 d1 cX2 cY2 d2 cX3 d3) = Ix (f cX1) (f cY1) (f d1) (f cX2) (f cY2) (f d2) (f cX3)
      (f d3) := by simp [Ix]

lemma Iy_map {S : Type*} [CommRing S] (f : R →+* S) (cX1 cY1 d1 cX2 cY2 d2 cX3 cY3 d3 : R) :
    f (Iy cX1 cY1 d1 cX2 cY2 d2 cX3 cY3 d3) = Iy (f cX1) (f cY1) (f d1) (f cX2) (f cY2) (f d2)
      (f cX3) (f cY3) (f d3) := by simp [Iy]

end Ichord

/-! ### The points in `T` -/

abbrev z0u : T := ιu (zB 0)
abbrev z1u : T := ιu (zB 1)
abbrev z2u : T := ιu (zB 2)
abbrev z0v : T := ιv (zB 0)
abbrev z1v : T := ιv (zB 1)
abbrev z2v : T := ιv (zB 2)
abbrev z0w : T := ιw (zB 0)
abbrev z1w : T := ιw (zB 1)

def X1 : T := 36 * z0u * αi ^ 2 + 3
def Y1 : T := 108 * z1u * αi ^ 3
def x2 : T := 36 * z0v + 3 * tT ^ 2
def y2 : T := 108 * z1v
def X3 : T := 36 * z0w * βi ^ 2 + 3
def Y3 : T := 108 * z1w * βi ^ 3
def AA : T := 1296 * a4T - 27
def BB : T := 46656 * a6T - 3888 * a4T + 54

/-- `Dl = x₂ − t² X₁` (a unit). -/
def Dl : T := x2 - tT ^ 2 * X1
/-- `Nl = y₂ − t³ Y₁`. -/
def Nl : T := y2 - tT ^ 3 * Y1

lemma ε3_z0v : ε3 z0v = 1 := by rw [show z0v = _ from z0v_eq]; simp [ε3_tT]

lemma isUnit_Dl : IsUnit Dl := isUnit_T (by simp [Dl, x2, ε3_z0v, ε3_tT, map_ofNat])

def Dli : T := Ring.inverse Dl
lemma hDli : Dl * Dli = 1 := Ring.mul_inverse_cancel _ isUnit_Dl

def RtT : T := Rt tT X1 Y1 eT fT

/-- the chord sum, `x`. -/
def Xc : T := X1 + tT * RtT * Dli ^ 2
/-- the chord sum, `y`. -/
def Yc : T := -(Nl * RtT * Dli ^ 3 + Y1)

/-! ### Relations -/

lemma hru0 : αT * D z0u = 2 * aT * z0u + z1u := by
  have := rel_img ιu 0 (by norm_num)
  rw [ιu_vB, ιu_wB, ← D_ιu] at this
  simpa using this
lemma hru1 : αT * D z1u = 3 * aT * z1u + z2u := by
  have := rel_img ιu 1 (by norm_num)
  rw [ιu_vB, ιu_wB, ← D_ιu] at this
  rw [this]; norm_num
lemma hrv0 : tT * D z0v = -(2 * (1 + tT) * z0v + z1v) := by
  have := rel_img ιv 0 (by norm_num)
  rw [ιv_vB, ιv_wB] at this
  rw [D_ιv, mul_neg, this]; simp
lemma hrv1 : tT * D z1v = -(3 * (1 + tT) * z1v + z2v) := by
  have := rel_img ιv 1 (by norm_num)
  rw [ιv_vB, ιv_wB] at this
  rw [D_ιv, mul_neg, this]; norm_num
lemma hz2u : z2u = 6 * z0u ^ 2 + αT ^ 2 * z0u + 2 * αT ^ 4 * a4T := by
  have := z2_img ιu; rwa [ιu_vB, ιu_a4B] at this
lemma hz2v : z2v = 6 * z0v ^ 2 + tT ^ 2 * z0v + 2 * tT ^ 4 * a4T := by
  have := z2_img ιv; rwa [ιv_vB, ιv_a4B] at this
lemma hcu : z1u ^ 2 = 4 * z0u ^ 3 + αT ^ 2 * z0u ^ 2 + 4 * αT ^ 4 * a4T * z0u +
    4 * αT ^ 6 * a6T := by
  have := curve_img ιu; rwa [ιu_vB, ιu_a4B, ιu_a6B] at this
lemma hcv : z1v ^ 2 = 4 * z0v ^ 3 + tT ^ 2 * z0v ^ 2 + 4 * tT ^ 4 * a4T * z0v +
    4 * tT ^ 6 * a6T := by
  have := curve_img ιv; rwa [ιv_vB, ιv_a4B, ιv_a6B] at this

lemma D_ofNat_mul (n : ℕ) [n.AtLeastTwo] (x : T) : D (OfNat.ofNat n * x) = OfNat.ofNat n * D x := by
  rw [isDer_D.mul, isDer_D.ofNat]; ring

lemma F1 : 6 * D X1 = 2 * Y1 := by
  have hD : D X1 = 36 * (z0u * (2 * αi * D αi) + αi ^ 2 * D z0u) := by
    rw [X1, isDer_D.add, isDer_D.ofNat, add_zero, mul_assoc, D_ofNat_mul, isDer_D.mul, isDer_D.sq]
  rw [hD, Y1]
  have h1 := hru0; have h2 := D_αi; have h3 := hαi
  linear_combination (432*z0u*αi) * h2 + (216*αi^3) * h1 + (-216*D z0u*αi^2) * h3

lemma F2 : 6 * D Y1 = 3 * X1 ^ 2 + AA := by
  have hD : D Y1 = 108 * (z1u * (3 * αi ^ 2 * D αi) + αi ^ 3 * D z1u) := by
    rw [Y1, mul_assoc, D_ofNat_mul, isDer_D.mul, isDer_D.cube]
  rw [hD, X1, AA]
  have h1 := hru1; have h2 := D_αi; have h3 := hαi; have h4 := hz2u
  linear_combination (1944*z1u*αi^2) * h2 + (648*αi^4) * h1 +
    (-648*(D z1u*αi^3 - 2*a4T*αT^3*αi^3 - 2*a4T*αT^2*αi^2 - 2*a4T*αT*αi - 2*a4T -
      z0u*αT*αi^3 - z0u*αi^2)) * h3 + (648*αi^4) * h4

lemma F3 : tT * (6 * D x2) = 2 * (6 * D tT) * x2 - 2 * y2 := by
  have hD : D x2 = 36 * D z0v + 3 * (2 * tT * D tT) := by
    rw [x2, isDer_D.add, D_ofNat_mul, D_ofNat_mul, isDer_D.sq]
  rw [hD, x2, y2]
  have h1 := hrv0; have h2 := D_tT
  linear_combination (216) * h1 + (-432*z0v) * h2

lemma F4 : tT * (6 * D y2) = 3 * (6 * D tT) * y2 - 3 * x2 ^ 2 - AA * tT ^ 4 := by
  have hD : D y2 = 108 * D z1v := by rw [y2, D_ofNat_mul]
  rw [hD, x2, y2, AA]
  have h1 := hrv1; have h2 := D_tT; have h3 := hz2v
  linear_combination (648) * h1 + (-648) * h3 + (-1944*z1v) * h2

lemma F5 : Y1 ^ 2 = X1 ^ 3 + AA * X1 + BB := by
  rw [X1, Y1, AA, BB]
  have h1 := hcu; have h3 := hαi
  linear_combination (11664*αi^6) * h1 + (11664*(αT*αi + 1)*(4*a4T*z0u*αT^2*αi^4 +
    4*a4T*z0u*αi^2 + 4*a6T*αT^4*αi^4 + 4*a6T*αT^2*αi^2 + 4*a6T + z0u^2*αi^4)) * h3

lemma F6 : y2 ^ 2 = x2 ^ 3 + AA * tT ^ 4 * x2 + BB * tT ^ 6 := by
  rw [x2, y2, AA, BB]
  linear_combination (11664) * hcv

lemma hx2 : x2 = 36 * (1 + tT) + 3 * tT ^ 2 + 36 * tT ^ 4 * eT := by
  rw [x2, show z0v = _ from z0v_eq]; ring
lemma hy2 : y2 = 108 * (-((1 + tT) * (2 + tT)) + tT ^ 4 * fT) := by
  rw [y2, show z1v = _ from z1v_eq]

lemma hE : tT ^ 2 * (x2 - tT ^ 2 * X1) ^ 2 * Xc =
    (y2 - tT ^ 3 * Y1) ^ 2 - tT ^ 2 * (x2 - tT ^ 2 * X1) ^ 2 * X1 - (x2 - tT ^ 2 * X1) ^ 2 * x2 := by
  have hreg := chord_reg tT X1 Y1 eT fT
  rw [← hx2, ← hy2] at hreg
  have hd := hDli
  rw [Dl] at hd
  rw [Xc, RtT]
  linear_combination (tT ^ 3 * Rt tT X1 Y1 eT fT * ((x2 - tT ^ 2 * X1) * Dli + 1)) * hd - hreg

lemma hF : tT * (x2 - tT ^ 2 * X1) * (Yc + Y1) + (y2 - tT ^ 3 * Y1) * (Xc - X1) = 0 := by
  have hd := hDli
  rw [Dl] at hd
  rw [Yc, Xc, Nl]
  linear_combination (-(tT * (y2 - tT ^ 3 * Y1) * RtT * Dli ^ 2)) * hd

lemma tT_ne : tT ≠ 0 := by
  intro h
  have := congrArg (fun g : T => coeff 1 (constantCoeff g)) h
  simp at this

lemma Dl_ne : x2 - tT ^ 2 * X1 ≠ 0 := by
  rw [← Dl]; exact isUnit_Dl.ne_zero

lemma six_ne : (6 : T) ≠ 0 := by
  intro h; have := congrArg ε3 h; rw [map_ofNat, map_zero] at this; norm_num at this

/-! ### Invariance -/

lemma D_Xc : D Xc = 0 := by
  have hDE := congrArg D hE
  simp only [isDer_D.mul, isDer_D.sub, isDer_D.sq, isDer_D.cube] at hDE
  have key := invX tT (6 * D tT) X1 Y1 x2 y2 AA BB Xc (6 * D X1) (6 * D Y1) (6 * D x2) (6 * D y2)
    (6 * D Xc) F1 F2 F3 F4 F5 F6 hE (by linear_combination 6 * hDE) tT_ne Dl_ne
  exact (mul_eq_zero.mp key).resolve_left six_ne

lemma D_Yc : D Yc = 0 := by
  have hDF := congrArg D hF
  simp only [isDer_D.mul, isDer_D.sub, isDer_D.add, isDer_D.sq, isDer_D.cube, D_Xc,
    isDer_D.zero] at hDF
  have key := invY tT (6 * D tT) X1 Y1 x2 y2 AA BB Xc Yc (6 * D X1) (6 * D Y1) (6 * D x2)
    (6 * D y2) (6 * D Yc) F1 F2 F3 F4 F5 F6 hE hF (by linear_combination 6 * hDF) tT_ne Dl_ne
  exact (mul_eq_zero.mp key).resolve_left six_ne

lemma D_X3 : D X3 = 0 := by
  rw [X3, isDer_D.add, isDer_D.ofNat, add_zero, mul_assoc, D_ofNat_mul, isDer_D.mul,
    isDer_D.sq, D_βi, D_ιw]; ring

lemma D_Y3 : D Y3 = 0 := by
  rw [Y3, mul_assoc, D_ofNat_mul, isDer_D.mul, isDer_D.cube, D_βi, D_ιw]; ring

/-! ### At `t = 0` -/

lemma ev0_tT : ev0 tT = 0 := by simp [ev0]

lemma ev0_αi_βi : ev0 αi = ev0 βi := by
  have h1 := congrArg ev0 hαi
  have h2 := congrArg ev0 hβi
  have h3 : ev0 αT = ev0 βT := by simp [ev0_tT]
  simp only [map_mul, map_one] at h1 h2
  linear_combination ev0 βi * h1 - ev0 αi * h2 - ev0 αi * ev0 βi * h3

lemma ev0_X1 : ev0 X1 = ev0 X3 := by
  simp only [X1, X3, map_add, map_mul, map_pow, map_ofNat, ev0_ιu_ιw, ev0_αi_βi]

lemma ev0_Y1 : ev0 Y1 = ev0 Y3 := by
  simp only [Y1, Y3, map_mul, map_pow, map_ofNat, ev0_ιu_ιw, ev0_αi_βi]

lemma Rt_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') (t X Y e g : S) :
    f (Rt t X Y e g) = Rt (f t) (f X) (f Y) (f e) (f g) := by
  simp only [Rt, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

lemma ev0_Xc : ev0 Xc = ev0 X3 := by
  rw [Xc, map_add, map_mul, map_mul, ev0_tT, zero_mul, zero_mul, add_zero, ev0_X1]

lemma ev0_Yc : ev0 Yc = ev0 Y3 := by
  have hd := congrArg ev0 hDli
  rw [map_mul, map_one, Dl, map_sub, map_mul, map_pow, ev0_tT, hx2] at hd
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, ev0_tT] at hd
  simp only [Yc, Nl, RtT, hy2, map_neg, map_add, map_mul, map_pow, map_ofNat, map_one, map_sub,
    Rt_map, ev0_tT, Rt_zero]
  rw [← ev0_Y1]
  linear_combination (2 * ev0 Y1 * ((36 * ev0 Dli) ^ 2 + 36 * ev0 Dli + 1)) * hd

/-! ### The addition theorem in `T` -/

theorem Xc_eq : Xc = X3 :=
  sub_eq_zero.mp (eq_zero_of_D (by rw [isDer_D.sub, D_Xc, D_X3, sub_zero])
    (by rw [map_sub, ev0_Xc, sub_self]))

theorem Yc_eq : Yc = Y3 :=
  sub_eq_zero.mp (eq_zero_of_D (by rw [isDer_D.sub, D_Yc, D_Y3, sub_zero])
    (by rw [map_sub, ev0_Yc, sub_self]))

lemma hX1c : X1 * αT ^ 2 = 36 * z0u + 3 * αT ^ 2 := by
  rw [X1]; linear_combination (36 * z0u * (αT * αi + 1)) * hαi
lemma hY1c : Y1 * αT ^ 3 = 108 * z1u := by
  rw [Y1]; linear_combination (108 * z1u * ((αT * αi) ^ 2 + αT * αi + 1)) * hαi
lemma hX3c : X3 * βT ^ 2 = 36 * z0w + 3 * βT ^ 2 := by
  rw [X3]; linear_combination (36 * z0w * (βT * βi + 1)) * hβi
lemma hY3c : Y3 * βT ^ 3 = 108 * z1w := by
  rw [Y3]; linear_combination (108 * z1w * ((βT * βi) ^ 2 + βT * βi + 1)) * hβi

/-- **The Tate addition theorem in `T`**, cleared of denominators. -/
theorem chord_T :
    Ix (36 * z0u + 3 * αT ^ 2) (108 * z1u) αT (36 * z0v + 3 * tT ^ 2) (108 * z1v) tT
        (36 * z0w + 3 * βT ^ 2) βT = 0 ∧
    Iy (36 * z0u + 3 * αT ^ 2) (108 * z1u) αT (36 * z0v + 3 * tT ^ 2) (108 * z1v) tT
        (36 * z0w + 3 * βT ^ 2) (108 * z1w) βT = 0 := by
  have hE3 := hE; rw [Xc_eq] at hE3
  have hF3 := hF; rw [Xc_eq, Yc_eq] at hF3
  rw [← hX1c, ← hY1c, ← hX3c, ← hY3c]
  rw [show 36 * z0v + 3 * tT ^ 2 = x2 from rfl, show 108 * z1v = y2 from rfl]
  constructor
  · simp only [Ix]; linear_combination αT ^ 6 * βT ^ 2 * hE3
  · simp only [Iy]; linear_combination (-(αT ^ 5 * βT ^ 3)) * hF3

/-! ### Over `R3` -/

/-- `a − 1`, `c − 1`, `ac − 1` in `R3`. -/
abbrev αR : R3 := C (A3 - 1)
abbrev γR : R3 := C (C3 - 1)
abbrev βR : R3 := C (A3 * C3 - 1)

lemma Ψ_αR : Ψ αR = αT := by simp [Ψ, ψ_A3]
lemma Ψ_γR : Ψ γR = tT := by simp [Ψ, ψ_C3]
lemma Ψ_βR : Ψ βR = βT := by simp [Ψ, ψ_A3, ψ_C3]

/-- **The Tate addition theorem over `ℚ[a][c]⟦b⟧`** (`u = a`, `v = c`, `q = acb`), cleared. -/
theorem chord_R3 :
    Ix (36 * ιu3 (zB 0) + 3 * αR ^ 2) (108 * ιu3 (zB 1)) αR (36 * ιv3 (zB 0) + 3 * γR ^ 2)
        (108 * ιv3 (zB 1)) γR (36 * ιw3 (zB 0) + 3 * βR ^ 2) βR = 0 ∧
    Iy (36 * ιu3 (zB 0) + 3 * αR ^ 2) (108 * ιu3 (zB 1)) αR (36 * ιv3 (zB 0) + 3 * γR ^ 2)
        (108 * ιv3 (zB 1)) γR (36 * ιw3 (zB 0) + 3 * βR ^ 2) (108 * ιw3 (zB 1)) βR = 0 := by
  obtain ⟨h1, h2⟩ := chord_T
  constructor
  · apply Ψ_injective
    rw [Ix_map, map_zero]
    simpa only [map_add, map_mul, map_pow, map_ofNat, Ψ_αR, Ψ_γR, Ψ_βR] using h1
  · apply Ψ_injective
    rw [Iy_map, map_zero]
    simpa only [map_add, map_mul, map_pow, map_ofNat, Ψ_αR, Ψ_γR, Ψ_βR] using h2

end TateAdd
