/-
# The shifted theta-type sums `σ_l(x) = Σ_k pe l (K_k x) e^{−(K_k−1)x}` and their interval enclosures

* `Ser l u = e^{u/2} e^{−x} σ_l(x)` with `x = π e^{2u}` (**`Ser_eq_sig`**);
* a geometric tail bound `|Σ_{k ≥ k₁} …| ≤ 2 A (1 + K_{k₁} x)^n e^{−(K_{k₁}−1)x}` (**`tail_le`**);
* the interval evaluator `sigIv` with its soundness lemma **`mem_sigIv`**, and the cell enclosure
  `xCell p q ∋ π e^{2u}` for `u ∈ [p/2^12, q/2^12]` (**`mem_xCell`**).
-/
import RamanujanTau.GORZXiEff.CVSeries
import RamanujanTau.GORZXiEff.CVExp

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Filter Topology Finset GORZXiEff JensenThreshold.Tail JensenThreshold.Tail.Iv

noncomputable def sigT (l : List ℤ) (x : ℝ) (k : ℕ) : ℝ := pe l (Kk k * x) * rexp (-(Kk k - 1) * x)

noncomputable def sig (l : List ℤ) (x : ℝ) : ℝ := ∑' k, sigT l x k

noncomputable def xOf (u : ℝ) : ℝ := π * rexp (2 * u)

lemma xOf_pos (u : ℝ) : 0 < xOf u := by unfold xOf; positivity

lemma tz_eq (l : List ℤ) (k : ℕ) (u : ℝ) :
    tz l k u = rexp (u / 2) * rexp (-xOf u) * sigT l (xOf u) k := by
  unfold tz sigT zk xOf
  have : rexp (-(π * Kk k * rexp (2 * u))) =
      rexp (-(π * rexp (2 * u))) * rexp (-(Kk k - 1) * (π * rexp (2 * u))) := by
    rw [← exp_add]; congr 1; ring
  rw [this, show π * Kk k * rexp (2 * u) = Kk k * (π * rexp (2 * u)) by ring]; ring

theorem Ser_eq_sig (l : List ℤ) (u : ℝ) : Ser l u = rexp (u / 2) * rexp (-xOf u) * sig l (xOf u) := by
  unfold Ser sig
  rw [← tsum_mul_left]
  congr 1; funext k; exact tz_eq l k u

lemma summable_sigT (l : List ℤ) {x : ℝ} (hx : 0 < x) : Summable (sigT l x) := by
  set u := Real.log (x / π) / 2
  have hxu : xOf u = x := by
    unfold xOf; rw [show 2 * u = Real.log (x / π) by ring, exp_log (by positivity)]; field_simp
  have h := (summable_tz l u).mul_left ((rexp (u / 2) * rexp (-xOf u))⁻¹)
  refine h.congr fun k => ?_
  rw [tz_eq, ← hxu]
  field_simp

/-! ## geometric tail bound -/

noncomputable def gT (A : ℝ) (n : ℕ) (x : ℝ) (k : ℕ) : ℝ := A * (1 + Kk k * x) ^ n * rexp (-(Kk k - 1) * x)

lemma abs_sigT_le (l : List ℤ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : |sigT l x k| ≤ gT (aS l) l.length x k := by
  unfold sigT gT
  rw [abs_mul, abs_of_pos (exp_pos _)]
  refine mul_le_mul_of_nonneg_right ((abs_pe_le l _).trans_eq ?_) (exp_pos _).le
  rw [abs_of_nonneg (by have := Kk_ge_one k; positivity)]

lemma Kk_succ (k : ℕ) : Kk (k + 1) = Kk k + (2 * k + 3) := by unfold Kk; push_cast; ring

/-- the ratio condition `g(k+1) ≤ g(k)/2` for `k ≥ k₁`, from a numeric inequality. -/
lemma gT_ratio {A : ℝ} (hA : 0 ≤ A) (n k₁ : ℕ) {x x₀ : ℝ} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x)
    (hcond : 2 * (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * n) ≤ rexp ((2 * k₁ + 3) * x₀))
    (k : ℕ) (hk : k₁ ≤ k) : gT A n x (k + 1) ≤ gT A n x k / 2 := by
  have hK := Kk_ge_one k
  have hx0 : 0 ≤ x := le_trans hx₀ hx
  have hkR : (k₁ : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k₁ := Nat.cast_nonneg _
  -- (1 + K' x) ≤ ((k+2)/(k+1))² (1 + K x) ≤ ((k₁+2)/(k₁+1))² (1 + K x)
  have hq : ((k : ℝ) + 2) / ((k : ℝ) + 1) ≤ ((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hKs : Kk (k + 1) = (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ 2 * Kk k := by
    unfold Kk; push_cast; field_simp; ring
  have hq1 : 1 ≤ ((k : ℝ) + 2) / ((k : ℝ) + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
  have h1 : 1 + Kk (k + 1) * x ≤ (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ 2 * (1 + Kk k * x) := by
    rw [hKs]
    have hsq : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ 2 ≤ (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hq 2
    have hsq1 : 1 ≤ (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ 2 := one_le_pow₀ hq1
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Kk k) hx0]
  have h2 : (1 + Kk (k + 1) * x) ^ n ≤ (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * n) * (1 + Kk k * x) ^ n := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by nlinarith [mul_nonneg (by linarith [Kk_ge_one (k + 1)] : (0 : ℝ) ≤ Kk (k + 1)) hx0]) h1 n
  have h3 : rexp (-(Kk (k + 1) - 1) * x) = rexp (-(Kk k - 1) * x) * rexp (-((2 * k + 3) * x)) := by
    rw [← exp_add, Kk_succ]; congr 1; ring
  have h4 : rexp (-((2 * k + 3) * x)) ≤ rexp (-((2 * k₁ + 3) * x₀)) := by
    apply exp_le_exp.2
    have : (2 * (k₁ : ℝ) + 3) * x₀ ≤ (2 * k + 3) * x := by
      apply mul_le_mul (by linarith) hx hx₀ (by positivity)
    linarith
  have h5 : (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * n) * rexp (-((2 * k₁ + 3) * x₀)) ≤ 1 / 2 := by
    rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]; linarith
  unfold gT
  rw [h3]
  set P := (1 + Kk k * x) ^ n
  set E := rexp (-(Kk k - 1) * x)
  have hP : 0 ≤ P := by positivity
  have hE : 0 ≤ E := (exp_pos _).le
  calc A * (1 + Kk (k + 1) * x) ^ n * (E * rexp (-((2 * k + 3) * x)))
      ≤ A * ((((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * n) * P) * (E * rexp (-((2 * k₁ + 3) * x₀))) := by
        gcongr
    _ = A * P * E * ((((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * n) * rexp (-((2 * k₁ + 3) * x₀))) := by ring
    _ ≤ A * P * E * (1 / 2) := by gcongr
    _ = A * P * E / 2 := by ring

/-- **geometric tail bound.** -/
lemma tail_le (l : List ℤ) (k₁ : ℕ) {x x₀ : ℝ} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x)
    (hcond : 2 * (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * l.length) ≤ rexp ((2 * k₁ + 3) * x₀)) :
    |∑' k, sigT l x (k + k₁)| ≤ 2 * gT (aS l) l.length x k₁ := by
  have hx0 : 0 ≤ x := le_trans hx₀ hx
  have hA := aS_nonneg l
  have hg : ∀ m, gT (aS l) l.length x (m + k₁) ≤ gT (aS l) l.length x k₁ * (1 / 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := gT_ratio hA l.length k₁ hx₀ hx hcond (m + k₁) (by omega)
      rw [show m + 1 + k₁ = m + k₁ + 1 by ring, pow_succ]
      linarith
  have hgs : Summable fun m : ℕ => gT (aS l) l.length x k₁ * (1 / 2 : ℝ) ^ m :=
    (summable_geometric_two).mul_left _
  have hb : ∀ m, ‖sigT l x (m + k₁)‖ ≤ gT (aS l) l.length x k₁ * (1 / 2) ^ m := fun m => by
    rw [Real.norm_eq_abs]; exact (abs_sigT_le l hx0 _).trans (hg m)
  have := tsum_of_norm_bounded hgs.hasSum hb
  rw [Real.norm_eq_abs, tsum_mul_left, tsum_geometric_two] at this
  linarith

lemma sig_split (l : List ℤ) {x : ℝ} (hx : 0 < x) (k₁ : ℕ) :
    sig l x = ∑ k ∈ range k₁, sigT l x k + ∑' k, sigT l x (k + k₁) :=
  ((summable_sigT l hx).sum_add_tsum_nat_add k₁).symm

/-! ## interval evaluation -/

def peIv : List ℤ → Iv → Iv
  | [], _ => zeroI
  | c :: l, Z => ofInt c + Z * peIv l Z

lemma mem_peIv {z : ℝ} {Z : Iv} (hz : z ∈ᵢ Z) : ∀ l : List ℤ, pe l z ∈ᵢ peIv l Z
  | [] => by simpa [peIv] using mem_zeroI
  | c :: l => by simp only [pe_cons, peIv]; exact mem_add (mem_ofInt c) (mem_mul hz (mem_peIv hz l))

def aZ (l : List ℤ) : ℤ := (l.map fun c => (c.natAbs : ℤ)).sum

lemma aS_eq : ∀ l : List ℤ, aS l = (aZ l : ℝ)
  | [] => by simp [aS, aZ]
  | c :: l => by
    have := aS_eq l
    simp only [aS, aZ, List.map_cons, List.sum_cons] at this ⊢
    rw [this]; push_cast; try rfl

/-- `K_k = (k+1)²` as an integer. -/
def KZ (k : ℕ) : ℤ := ((k : ℤ) + 1) ^ 2

lemma KZ_eq (k : ℕ) : (KZ k : ℝ) = Kk k := by unfold KZ Kk; push_cast; ring

/-- enclosure of the `k`-th term. -/
def sigTIv (l : List ℤ) (X : Iv) (k : ℕ) : Iv :=
  peIv l (ofInt (KZ k) * X) * expNeg (ofInt (KZ k - 1) * X)

lemma mem_sigTIv (l : List ℤ) {x : ℝ} {X : Iv} (hx0 : 0 ≤ x) (hx : x ∈ᵢ X) (k : ℕ) :
    sigT l x k ∈ᵢ sigTIv l X k := by
  unfold sigT sigTIv
  have h1 : Kk k * x ∈ᵢ ofInt (KZ k) * X := by rw [← KZ_eq]; exact mem_mul (mem_ofInt _) hx
  have h2 : (Kk k - 1) * x ∈ᵢ ofInt (KZ k - 1) * X := by
    rw [← KZ_eq]; have := mem_mul (mem_ofInt (KZ k - 1)) hx; push_cast at this; exact this
  have h3 := mem_expNeg (mul_nonneg (by linarith [Kk_ge_one k]) hx0) h2
  rw [show -(Kk k - 1) * x = -((Kk k - 1) * x) by ring]
  exact mem_mul (mem_peIv h1 l) h3

def sumTIv (l : List ℤ) (X : Iv) : ℕ → Iv
  | 0 => zeroI
  | k + 1 => sumTIv l X k + sigTIv l X k

lemma mem_sumTIv (l : List ℤ) {x : ℝ} {X : Iv} (hx0 : 0 ≤ x) (hx : x ∈ᵢ X) :
    ∀ k₁ : ℕ, (∑ k ∈ range k₁, sigT l x k) ∈ᵢ sumTIv l X k₁
  | 0 => by simpa [sumTIv] using mem_zeroI
  | k + 1 => by rw [sum_range_succ]; exact mem_add (mem_sumTIv l hx0 hx k) (mem_sigTIv l hx0 hx k)

/-- upper bound of the tail majorant `2 A (1 + K x)^n e^{−(K−1)x}`. -/
def tailHi (l : List ℤ) (X : Iv) (k₁ : ℕ) : ℤ :=
  (ofInt (2 * aZ l) * (oneI + ofInt (KZ k₁) * X).pow l.length * expNeg (ofInt (KZ k₁ - 1) * X)).hi

lemma tail_le_tailHi (l : List ℤ) {x : ℝ} {X : Iv} (hx0 : 0 ≤ x) (hx : x ∈ᵢ X) (k₁ : ℕ) :
    2 * gT (aS l) l.length x k₁ ≤ (tailHi l X k₁ : ℝ) / S := by
  unfold tailHi gT
  have h1 : Kk k₁ * x ∈ᵢ ofInt (KZ k₁) * X := by rw [← KZ_eq]; exact mem_mul (mem_ofInt _) hx
  have h2 : (Kk k₁ - 1) * x ∈ᵢ ofInt (KZ k₁ - 1) * X := by
    rw [← KZ_eq]; have := mem_mul (mem_ofInt (KZ k₁ - 1)) hx; push_cast at this; exact this
  have h3 := mem_expNeg (mul_nonneg (by linarith [Kk_ge_one k₁]) hx0) h2
  have h4 := mem_mul (mem_mul (mem_ofInt (2 * aZ l)) (mem_pow (mem_add mem_oneI h1) l.length)) h3
  refine le_trans (le_of_eq ?_) h4.2
  rw [aS_eq, show -(Kk k₁ - 1) * x = -((Kk k₁ - 1) * x) by ring]; push_cast; ring

/-- **interval enclosure of `σ_l(x)`**: `k₁` exact terms plus the symmetric tail interval. -/
def sigIv (l : List ℤ) (X : Iv) (k₁ : ℕ) : Iv := sumTIv l X k₁ + symm (tailHi l X k₁)

theorem mem_sigIv (l : List ℤ) {x x₀ : ℝ} {X : Iv} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x) (hX : x ∈ᵢ X)
    (k₁ : ℕ)
    (hcond : 2 * (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * l.length) ≤ rexp ((2 * k₁ + 3) * x₀))
    (hpos : 0 < x) : sig l x ∈ᵢ sigIv l X k₁ := by
  rw [sig_split l hpos k₁]
  refine mem_add (mem_sumTIv l hpos.le hX k₁) (mem_symm ?_)
  exact (tail_le l k₁ hx₀ hx hcond).trans (tail_le_tailHi l hpos.le hX k₁)

lemma sigT_zero (l : List ℤ) (x : ℝ) : sigT l x 0 = pe l x := by
  simp [sigT, Kk]

lemma sig_eq_main (l : List ℤ) {x : ℝ} (hx : 0 < x) (k₁ : ℕ) (hk : 1 ≤ k₁) :
    sig l x - pe l x = ∑ k ∈ range (k₁ - 1), sigT l x (k + 1) + ∑' k, sigT l x (k + k₁) := by
  rw [sig_split l hx k₁]
  obtain ⟨m, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
  rw [sum_range_succ', sigT_zero, Nat.add_sub_cancel]; ring

def sumT1Iv (l : List ℤ) (X : Iv) : ℕ → Iv
  | 0 => zeroI
  | k + 1 => sumT1Iv l X k + sigTIv l X (k + 1)

lemma mem_sumT1Iv (l : List ℤ) {x : ℝ} {X : Iv} (hx0 : 0 ≤ x) (hx : x ∈ᵢ X) :
    ∀ m : ℕ, (∑ k ∈ range m, sigT l x (k + 1)) ∈ᵢ sumT1Iv l X m
  | 0 => by simpa [sumT1Iv] using mem_zeroI
  | k + 1 => by rw [sum_range_succ]; exact mem_add (mem_sumT1Iv l hx0 hx k) (mem_sigTIv l hx0 hx _)

/-- enclosure of `σ_l(x) − pe l x` (the terms `k ≥ 1`). -/
def tauIv (l : List ℤ) (X : Iv) (k₁ : ℕ) : Iv := sumT1Iv l X (k₁ - 1) + symm (tailHi l X k₁)

theorem mem_tauIv (l : List ℤ) {x x₀ : ℝ} {X : Iv} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x) (hX : x ∈ᵢ X)
    (k₁ : ℕ) (hk : 1 ≤ k₁)
    (hcond : 2 * (((k₁ : ℝ) + 2) / ((k₁ : ℝ) + 1)) ^ (2 * l.length) ≤ rexp ((2 * k₁ + 3) * x₀))
    (hpos : 0 < x) : (sig l x - pe l x) ∈ᵢ tauIv l X k₁ := by
  rw [sig_eq_main l hpos k₁ hk]
  refine mem_add (mem_sumT1Iv l hpos.le hX _) (mem_symm ?_)
  exact (tail_le l k₁ hx₀ hx hcond).trans (tail_le_tailHi l hpos.le hX k₁)

/-! ## `π` and the cell enclosure of `x = π e^{2u}` -/

def piIv : Iv := ⟨(ofFrac 314159265358979323846 (10 ^ 20)).lo, (ofFrac 314159265358979323847 (10 ^ 20)).hi⟩

lemma mem_piIv : π ∈ᵢ piIv := by
  have h1 := mem_ofFrac 314159265358979323846 (10 ^ 20) (by norm_num)
  have h2 := mem_ofFrac 314159265358979323847 (10 ^ 20) (by norm_num)
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  constructor
  · refine le_trans h1.1 ?_; push_cast; norm_num at p1 ⊢; linarith
  · refine le_trans ?_ h2.2; push_cast; norm_num at p2 ⊢; linarith

/-- `u = p / 2^12`. -/
def uZ (p : ℤ) : ℤ := p * 2 ^ 180

lemma uZ_div (p : ℤ) : ((uZ p : ℤ) : ℝ) / S = (p : ℝ) / 2 ^ 12 := by
  unfold uZ S; push_cast; field_simp; ring

/-- `x = π e^{2u}` for `u ∈ [p/2^12, q/2^12]`. -/
def xCell (p q : ℤ) : Iv := piIv * ⟨(expPt (2 * uZ p)).lo, (expPt (2 * uZ q)).hi⟩

lemma exp_two_u_mem {p q : ℤ} (hp : 0 ≤ p) (hq : q ≤ 2 ^ 20) {u : ℝ} (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) : rexp (2 * u) ∈ᵢ (⟨(expPt (2 * uZ p)).lo, (expPt (2 * uZ q)).hi⟩ : Iv) := by
  have hq0 : 0 ≤ q := by
    have : (p : ℝ) ≤ q := by
      have := le_trans hu1 hu2
      rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    have : p ≤ q := by exact_mod_cast this
    omega
  have hB : ∀ r : ℤ, 0 ≤ r → r ≤ 2 ^ 20 → 2 * uZ r ≤ BE := by
    intro r h0 h1; unfold uZ BE S mE; nlinarith
  have hp' : (0 : ℤ) ≤ 2 * uZ p := by unfold uZ; positivity
  have hq' : (0 : ℤ) ≤ 2 * uZ q := by unfold uZ; positivity
  have hpq : p ≤ 2 ^ 20 := by
    have : (p : ℝ) ≤ q := by
      have := le_trans hu1 hu2
      rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    have : p ≤ q := by exact_mod_cast this
    omega
  have m1 := mem_expPt hp' (hB p hp hpq)
  have m2 := mem_expPt hq' (hB q hq0 hq)
  have e : ∀ r : ℤ, ((2 * uZ r : ℤ) : ℝ) / S = 2 * ((r : ℝ) / 2 ^ 12) := by
    intro r; rw [show ((2 * uZ r : ℤ) : ℝ) = 2 * ((uZ r : ℤ) : ℝ) by push_cast; ring, mul_div_assoc, uZ_div]
  rw [e] at m1 m2
  exact ⟨le_trans m1.1 (exp_le_exp.2 (by linarith)), le_trans (exp_le_exp.2 (by linarith)) m2.2⟩

lemma mem_xCell {p q : ℤ} (hp : 0 ≤ p) (hq : q ≤ 2 ^ 20) {u : ℝ} (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) : xOf u ∈ᵢ xCell p q :=
  mem_mul mem_piIv (exp_two_u_mem hp hq hu1 hu2)

/-- the cell interval for `u` itself. -/
def uCell (p q : ℤ) : Iv := ⟨uZ p, uZ q⟩

lemma mem_uCell {p q : ℤ} {u : ℝ} (hu1 : (p : ℝ) / 2 ^ 12 ≤ u) (hu2 : u ≤ (q : ℝ) / 2 ^ 12) :
    u ∈ᵢ uCell p q := by
  unfold uCell Iv.mem; simp only; rw [uZ_div, uZ_div]; exact ⟨hu1, hu2⟩

end GORZXiEff.CV
