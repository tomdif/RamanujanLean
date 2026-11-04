/-
# The derivative chain of Riemann's kernel in polynomial form

Write `z_k(u) = π K_k e^{2u}` (`K_k = (k+1)²`) and, for an integer coefficient list `l`,
`tz l k u = e^{u/2} · pe l (z_k u) · e^{−z_k u}`, `Ser l u = Σ_k tz l k u`.
Since `z_k' = 2 z_k`, `d/du tz l k = ½ tz (stepZ l) k` with `stepZ p = p + 4z p' − 4z p` (**`hasDerivAt_Ser`**).
With `Zs 0 = [0, −3, 2]` (i.e. `2z² − 3z`) and `Zs (i+1) = stepZ (Zs i)`, the functions
`Phi i = Ser (Zs i) / 2^i` form a derivative chain on all of `ℝ` (**`hasDerivAt_Phi`**), and
`Phi 0 = PhiR`, `Phi 1 = PhiD` (**`PhiR_eq`**, **`PhiD_eq`**).
-/
import RamanujanTau.GORZXiEff.Main

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Filter Topology GORZXiEff

/-! ## integer polynomials as coefficient lists -/

/-- `pe [c₀, c₁, …] z = c₀ + c₁ z + …` (Horner). -/
def pe : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: l, z => (c : ℝ) + z * pe l z

def addL : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

def smulL (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

/-- formal derivative. -/
def dL : List ℤ → List ℤ
  | [] => []
  | _ :: l => addL l (0 :: dL l)

/-- `p ↦ p + 4z p' − 4z p` (twice the `u`-derivative operator). -/
def stepZ (l : List ℤ) : List ℤ := addL l (addL (0 :: smulL 4 (dL l)) (0 :: smulL (-4) l))

/-- `Zs 0 = 2z² − 3z`, `Zs (i+1) = stepZ (Zs i)`. -/
def Zs : ℕ → List ℤ
  | 0 => [0, -3, 2]
  | i + 1 => stepZ (Zs i)

@[simp] lemma pe_nil (z : ℝ) : pe [] z = 0 := rfl
@[simp] lemma pe_cons (c : ℤ) (l : List ℤ) (z : ℝ) : pe (c :: l) z = c + z * pe l z := rfl

lemma pe_addL : ∀ (l m : List ℤ) (z : ℝ), pe (addL l m) z = pe l z + pe m z
  | [], m, z => by simp [addL]
  | a :: l, [], z => by simp [addL]
  | a :: l, b :: m, z => by simp only [addL, pe_cons, pe_addL l m z]; push_cast; ring

lemma pe_smulL (c : ℤ) : ∀ (l : List ℤ) (z : ℝ), pe (smulL c l) z = c * pe l z
  | [], z => by simp [smulL]
  | a :: l, z => by
    have := pe_smulL c l z
    simp only [smulL, List.map_cons, pe_cons] at this ⊢
    rw [this]; push_cast; ring

lemma hasDerivAt_pe : ∀ (l : List ℤ) (z : ℝ), HasDerivAt (pe l) (pe (dL l) z) z
  | [], z => by simpa [dL] using hasDerivAt_const z (0 : ℝ)
  | c :: l, z => by
    have h : HasDerivAt (fun y => (c : ℝ) + y * pe l y) (1 * pe l z + z * pe (dL l) z) z :=
      ((hasDerivAt_id' z).mul (hasDerivAt_pe l z)).const_add (c : ℝ)
    have e : pe (c :: l) = fun y => (c : ℝ) + y * pe l y := by funext y; simp
    rw [e]
    convert h using 1
    simp [dL, pe_addL]

lemma pe_stepZ (l : List ℤ) (z : ℝ) :
    pe (stepZ l) z = pe l z + 4 * z * pe (dL l) z - 4 * z * pe l z := by
  simp only [stepZ, pe_addL, pe_cons, pe_smulL]; push_cast; ring

/-- `Σ |cᵢ|`. -/
noncomputable def aS : List ℤ → ℝ
  | [] => 0
  | c :: l => |(c : ℝ)| + aS l

lemma aS_nonneg : ∀ l : List ℤ, 0 ≤ aS l
  | [] => le_rfl
  | c :: l => by simp only [aS]; have := aS_nonneg l; positivity

lemma abs_pe_le : ∀ (l : List ℤ) (z : ℝ), |pe l z| ≤ aS l * (1 + |z|) ^ l.length
  | [], z => by simp [aS]
  | c :: l, z => by
    have ih := abs_pe_le l z
    have h1 : (1 : ℝ) ≤ (1 + |z|) ^ (l.length + 1) := one_le_pow₀ (by linarith [abs_nonneg z])
    have h0 := aS_nonneg l
    simp only [pe_cons, aS, List.length_cons]
    calc |(c : ℝ) + z * pe l z| ≤ |(c : ℝ)| + |z| * |pe l z| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| * (1 + |z|) ^ (l.length + 1) + (1 + |z|) * (aS l * (1 + |z|) ^ l.length) := by
          gcongr
          · nlinarith [abs_nonneg (c : ℝ)]
          · linarith
      _ = _ := by ring

/-! ## the series -/

noncomputable def zk (k : ℕ) (u : ℝ) : ℝ := π * Kk k * rexp (2 * u)

noncomputable def tz (l : List ℤ) (k : ℕ) (u : ℝ) : ℝ :=
  rexp (u / 2) * pe l (zk k u) * rexp (-zk k u)

noncomputable def Ser (l : List ℤ) (u : ℝ) : ℝ := ∑' k, tz l k u

lemma zk_pos (k : ℕ) (u : ℝ) : 0 < zk k u := by
  unfold zk; have := Kk_ge_one k; positivity

lemma hasDerivAt_zk (k : ℕ) (u : ℝ) : HasDerivAt (zk k) (2 * zk k u) u := by
  have h : HasDerivAt (fun u => rexp (2 * u)) (rexp (2 * u) * 2) u :=
    ((hasDerivAt_id u).const_mul 2).exp.congr_deriv (by simp)
  have := h.const_mul (π * Kk k)
  unfold zk
  convert this using 1; ring

lemma hasDerivAt_tz (l : List ℤ) (k : ℕ) (u : ℝ) :
    HasDerivAt (tz l k) ((1 / 2) * tz (stepZ l) k u) u := by
  have h1 : HasDerivAt (fun u : ℝ => rexp (u / 2)) (rexp (u / 2) * (1 / 2)) u :=
    ((hasDerivAt_id u).div_const 2).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun u => pe l (zk k u)) (pe (dL l) (zk k u) * (2 * zk k u)) u :=
    (hasDerivAt_pe l (zk k u)).comp u (hasDerivAt_zk k u)
  have h3 : HasDerivAt (fun u => rexp (-zk k u)) (rexp (-zk k u) * (-(2 * zk k u))) u :=
    (hasDerivAt_zk k u).neg.exp
  have := (h1.mul h2).mul h3
  simp only [Pi.mul_apply] at this
  unfold tz
  convert this using 1
  rw [pe_stepZ]; ring

/-- the summable majorant `K^n e^{−cK}`. -/
lemma summable_Kpow_exp (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => Kk k ^ n * rexp (-c * Kk k) := by
  have hs : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (2 * n) * rexp (-c * ((k + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 (summable_pow_mul_exp_neg_nat_mul (2 * n) hc)
  refine Summable.of_nonneg_of_le (fun k => by have := Kk_ge_one k; positivity) (fun k => ?_) hs
  unfold Kk; push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [pow_mul]
  have : rexp (-c * ((k : ℝ) + 1) ^ 2) ≤ rexp (-c * ((k : ℝ) + 1)) := by
    apply exp_le_exp.2
    have h1 : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- local domination of `tz l k` on `(−B, B)`. -/
lemma abs_tz_le (l : List ℤ) (k : ℕ) {B v : ℝ} (hv : v ∈ Ioo (-B) B) :
    |tz l k v| ≤ (rexp (B / 2) * aS l * (1 + π * rexp (2 * B)) ^ l.length) *
      (Kk k ^ l.length * rexp (-(π * rexp (-(2 * B))) * Kk k)) := by
  have hK := Kk_ge_one k
  have hz := zk_pos k v
  obtain ⟨hv1, hv2⟩ := hv
  have hzle : zk k v ≤ Kk k * (π * rexp (2 * B)) := by
    unfold zk
    have : rexp (2 * v) ≤ rexp (2 * B) := exp_le_exp.2 (by linarith)
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ π * Kk k by positivity)
    linarith
  have hzge : π * rexp (-(2 * B)) * Kk k ≤ zk k v := by
    unfold zk
    have : rexp (-(2 * B)) ≤ rexp (2 * v) := exp_le_exp.2 (by linarith)
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ π * Kk k by positivity)
    linarith
  have hp : |pe l (zk k v)| ≤ aS l * (Kk k * (1 + π * rexp (2 * B))) ^ l.length := by
    refine (abs_pe_le l _).trans (mul_le_mul_of_nonneg_left ?_ (aS_nonneg l))
    rw [abs_of_pos hz]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith [mul_le_mul_of_nonneg_right hK (show (0 : ℝ) ≤ 1 by norm_num)]
  have he1 : rexp (v / 2) ≤ rexp (B / 2) := exp_le_exp.2 (by linarith)
  have he2 : rexp (-zk k v) ≤ rexp (-(π * rexp (-(2 * B))) * Kk k) := exp_le_exp.2 (by linarith)
  have hA := aS_nonneg l
  unfold tz
  rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  calc rexp (v / 2) * |pe l (zk k v)| * rexp (-zk k v)
      ≤ rexp (B / 2) * (aS l * (Kk k * (1 + π * rexp (2 * B))) ^ l.length) *
          rexp (-(π * rexp (-(2 * B))) * Kk k) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

lemma summable_major (l : List ℤ) (B : ℝ) :
    Summable fun k => (rexp (B / 2) * aS l * (1 + π * rexp (2 * B)) ^ l.length) *
      (Kk k ^ l.length * rexp (-(π * rexp (-(2 * B))) * Kk k)) :=
  (summable_Kpow_exp _ (by positivity)).mul_left _

lemma summable_tz (l : List ℤ) (v : ℝ) : Summable fun k => tz l k v := by
  have hv : v ∈ Ioo (-(|v| + 1)) (|v| + 1) := by
    constructor <;> linarith [neg_abs_le v, le_abs_self v]
  exact Summable.of_norm_bounded (summable_major l (|v| + 1))
    (fun k => by rw [Real.norm_eq_abs]; exact abs_tz_le l k hv)

theorem hasDerivAt_Ser (l : List ℤ) (u : ℝ) :
    HasDerivAt (Ser l) ((1 / 2) * Ser (stepZ l) u) u := by
  set B := |u| + 1
  have hu : u ∈ Ioo (-B) B := by constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have h0 : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith [abs_nonneg u]
  have := hasDerivAt_tsum_of_isPreconnected (g := tz l) (g' := fun k y => (1 / 2) * tz (stepZ l) k y)
    ((summable_major (stepZ l) B).mul_left (1 / 2)) isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => hasDerivAt_tz l k y)
    (fun k y hy => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_tz_le (stepZ l) k hy) (by norm_num))
    h0 (summable_tz l 0) hu
  unfold Ser
  rw [← tsum_mul_left]
  exact this

/-- the derivative chain `Φ^{(i)} = Ser (Zs i) / 2^i`. -/
noncomputable def Phi (i : ℕ) (u : ℝ) : ℝ := Ser (Zs i) u / 2 ^ i

theorem hasDerivAt_Phi (i : ℕ) (u : ℝ) : HasDerivAt (Phi i) (Phi (i + 1) u) u := by
  have := (hasDerivAt_Ser (Zs i) u).div_const (2 ^ i)
  unfold Phi
  convert this using 1
  simp only [Zs, pow_succ]; field_simp

lemma Zs_one : Zs 1 = [0, -15, 30, -8] := by decide

lemma exp_shift (u : ℝ) (m : ℕ) (a : ℝ) (ha : a = 1 / 2 + 2 * m) :
    rexp (a * u) = rexp (u / 2) * rexp (2 * u) ^ m := by
  rw [← Real.exp_nat_mul, ← exp_add, ha]; congr 1; ring

theorem PhiR_eq : PhiR = Phi 0 := by
  funext u
  simp only [PhiR, Phi, Ser, pow_zero, div_one]
  congr 1; funext k
  simp only [phik, tz, Zs, mono, zk, pe_cons, pe_nil]
  rw [exp_shift u 2 (9 / 2) (by norm_num), exp_shift u 1 (5 / 2) (by norm_num)]
  push_cast
  ring_nf

theorem PhiD_eq : PhiD = Phi 1 := by
  funext u
  simp only [PhiD, Phi, Ser, Zs_one, pow_one]
  rw [← tsum_div_const]
  congr 1; funext k
  simp only [phik', tz, mono, zk, pe_cons, pe_nil]
  rw [exp_shift u 2 (9 / 2) (by norm_num), exp_shift u 3 (13 / 2) (by norm_num),
    exp_shift u 1 (5 / 2) (by norm_num)]
  push_cast
  ring_nf

end GORZXiEff.CV
