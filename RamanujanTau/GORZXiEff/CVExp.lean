/-
# Kernel-evaluable interval enclosures of `exp` (fixed point `2^{-192}`, outward rounding)

* `expPt a` encloses `e^{a/S}` for `0 ≤ a ≤ 2^12 S` (`a/S/2^12 ∈ [0,1]`: 24 Taylor terms with the
  remainder of `Real.exp_bound'`, then 12 squarings) — **`mem_expPt`**;
* `expNeg X` encloses `e^{−x}` for every `x ≥ 0` in `X` — **`mem_expNeg`** (always sound: out-of-range
  arguments fall back to the trivial bounds `0 ≤ e^{−x} ≤ 1`).
-/
import RamanujanTau.JensenThreshold.Tail.IvLemmas

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Finset JensenThreshold.Tail JensenThreshold.Tail.Iv

/-- `(yⁱ/i!, Σ_{j<i} yʲ/j!)`. -/
def expSer (Y : Iv) : ℕ → Iv × Iv
  | 0 => (oneI, zeroI)
  | i + 1 => ((expSer Y i).1 * Y * ofFrac 1 ((i : ℤ) + 1), (expSer Y i).2 + (expSer Y i).1)

lemma mem_expSer {y : ℝ} {Y : Iv} (hy : y ∈ᵢ Y) : ∀ i : ℕ,
    (y ^ i / (i.factorial : ℝ)) ∈ᵢ (expSer Y i).1 ∧
      (∑ j ∈ range i, y ^ j / (j.factorial : ℝ)) ∈ᵢ (expSer Y i).2
  | 0 => by simpa [expSer] using ⟨mem_oneI, mem_zeroI⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := mem_expSer hy i
    refine ⟨?_, ?_⟩
    · have h := mem_mul (mem_mul h1 hy) (mem_ofFrac 1 ((i : ℤ) + 1) (by omega))
      simp only [expSer]
      convert h using 1
      rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    · rw [sum_range_succ]; exact mem_add h2 h1

def mE : ℕ := 12
def nE : ℕ := 24

/-- repeated squaring. -/
def sqPow (J : Iv) : ℕ → Iv
  | 0 => J
  | m + 1 => sqPow J m * sqPow J m

lemma mem_sqPow {x : ℝ} {J : Iv} (hx : x ∈ᵢ J) : ∀ m : ℕ, (x ^ (2 ^ m)) ∈ᵢ sqPow J m
  | 0 => by simpa [sqPow] using hx
  | m + 1 => by
    have := mem_mul (mem_sqPow hx m) (mem_sqPow hx m)
    simp only [sqPow]; convert this using 1; rw [pow_succ, pow_mul]; ring

/-- the bound `2^12 S` up to which `expPt` is valid. -/
def BE : ℤ := 2 ^ mE * S

/-- enclosure of `e^{a/S}`, valid for `0 ≤ a ≤ 2^12 S`. -/
@[irreducible] def expPt (a : ℤ) : Iv :=
  let Y : Iv := ⟨fdv a (2 ^ mE), cdv a (2 ^ mE)⟩
  let p := expSer Y nE
  sqPow ⟨p.2.lo, (p.2 + p.1 * ofFrac ((nE : ℤ) + 1) nE).hi⟩ mE

lemma mem_expPt {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ BE) : rexp ((a : ℝ) / S) ∈ᵢ expPt a := by
  have hS := S_posR
  set y : ℝ := (a : ℝ) / S / 2 ^ mE with hy
  have hP : (0 : ℤ) < 2 ^ mE := by positivity
  set Y : Iv := ⟨fdv a (2 ^ mE), cdv a (2 ^ mE)⟩ with hYdef
  have hyY : y ∈ᵢ Y := by
    unfold Iv.mem
    have e : ∀ q : ℤ, ((q : ℝ) / (2 ^ mE : ℤ)) / S = (q : ℝ) / S / 2 ^ mE := by
      intro q; push_cast; ring
    constructor
    · have := div_le_div_of_nonneg_right (fdv_le a hP) hS.le
      rw [e] at this; exact this
    · have := div_le_div_of_nonneg_right (le_cdv a hP) hS.le
      rw [e] at this; exact this
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast h0
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_div, div_le_one (by positivity)]
    have : (a : ℝ) ≤ ((BE : ℤ) : ℝ) := by exact_mod_cast h1
    unfold BE at this
    push_cast at this; linarith
  obtain ⟨hT, hsum⟩ := mem_expSer hyY nE
  have hrem := mem_mul hT (mem_ofFrac ((nE : ℤ) + 1) nE (by decide))
  have hup := Real.exp_bound' hy0 hy1 (n := nE) (by decide)
  have hlo := Real.sum_le_exp_of_nonneg hy0 nE
  have hJ : rexp y ∈ᵢ (⟨(expSer Y nE).2.lo, ((expSer Y nE).2 + (expSer Y nE).1 *
      ofFrac ((nE : ℤ) + 1) nE).hi⟩ : Iv) := by
    refine ⟨le_trans hsum.1 hlo, le_trans hup ?_⟩
    have := (mem_add hsum hrem).2
    refine le_trans (le_of_eq ?_) this
    push_cast; field_simp
  have := mem_sqPow hJ mE
  unfold expPt
  convert this using 1
  rw [← Real.exp_nat_mul]; congr 1; rw [hy]; push_cast; field_simp

/-- enclosure of `e^{−x}` for `x ∈ X`, `x ≥ 0`. -/
def expNegLo (X : Iv) : ℤ := if X.hi ≤ BE ∧ 0 < (expPt X.hi).lo then (expPt X.hi).inv.lo else 0
def expNegHi (X : Iv) : ℤ :=
  if 0 < (expPt (max 0 (min X.lo BE))).lo then (expPt (max 0 (min X.lo BE))).inv.hi else S
def expNeg (X : Iv) : Iv := ⟨expNegLo X, expNegHi X⟩

lemma mem_expNeg {x : ℝ} {X : Iv} (hx0 : 0 ≤ x) (hx : x ∈ᵢ X) : rexp (-x) ∈ᵢ expNeg X := by
  have hS := S_posR
  constructor
  · show ((expNegLo X : ℤ) : ℝ) / S ≤ rexp (-x)
    unfold expNegLo
    by_cases h : X.hi ≤ BE ∧ 0 < (expPt X.hi).lo
    · rw [if_pos h]
      have hhi : (0 : ℤ) ≤ X.hi := by
        have h1 : (0 : ℝ) ≤ (X.hi : ℝ) / S := le_trans hx0 hx.2
        have h2 : (0 : ℝ) ≤ X.hi := by
          by_contra hc
          rw [not_le] at hc
          have : (X.hi : ℝ) / S < 0 := div_neg_of_neg_of_pos hc hS
          linarith
        exact_mod_cast h2
      have hm := JensenThreshold.Tail.mem_inv (mem_expPt hhi h.1) h.2
      refine le_trans hm.1 ?_
      rw [← Real.exp_neg]; exact exp_le_exp.2 (by linarith [hx.2])
    · rw [if_neg h, Int.cast_zero, zero_div]; exact (exp_pos _).le
  · show rexp (-x) ≤ ((expNegHi X : ℤ) : ℝ) / S
    unfold expNegHi
    by_cases h : 0 < (expPt (max 0 (min X.lo BE))).lo
    · rw [if_pos h]
      have ha0 : (0 : ℤ) ≤ max 0 (min X.lo BE) := le_max_left _ _
      have hB : (0 : ℤ) ≤ BE := by unfold BE S; positivity
      have ha1 : max 0 (min X.lo BE) ≤ BE := max_le hB (min_le_right _ _)
      have hm := JensenThreshold.Tail.mem_inv (mem_expPt ha0 ha1) h
      refine le_trans ?_ hm.2
      rw [← Real.exp_neg]; apply exp_le_exp.2
      have : ((max 0 (min X.lo BE) : ℤ) : ℝ) / S ≤ x := by
        rcases le_total X.lo 0 with h' | h'
        · have : max 0 (min X.lo BE) = 0 := max_eq_left (le_trans (min_le_left _ _) h')
          rw [this]; simpa using hx0
        · have : max 0 (min X.lo BE) ≤ X.lo := max_le h' (min_le_left _ _)
          have : ((max 0 (min X.lo BE) : ℤ) : ℝ) ≤ X.lo := by exact_mod_cast this
          exact le_trans (div_le_div_of_nonneg_right this hS.le) hx.1
      linarith
    · rw [if_neg h]
      have : rexp (-x) ≤ 1 := exp_le_one_iff.2 (by linarith)
      have e : ((S : ℤ) : ℝ) / S = 1 := div_self hS.ne'
      rw [e]; exact this

end GORZXiEff.CV
