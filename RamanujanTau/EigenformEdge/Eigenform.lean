/-
# Normalized Hecke eigenforms of level one, and their normalized data

Neither Mathlib nor this repo has Hecke operators on `CuspForm 𝒮ℒ k` for general `k` (see
`HeckeEigenform.lean`), so "Hecke eigenform" is expressed through its coefficients:

`IsNormalizedEigenform f` :  `a_f(n) ∈ ℝ`, `a_f(1) = 1`, `a_f(mn) = a_f(m)a_f(n)` for coprime
`m, n`, and `a_f(p^{e+2}) = a_f(p)a_f(p^{e+1}) − p^{k−1}a_f(p^e)`.

These are *true theorems* about every normalized Hecke eigenform of level one (Hecke 1937;
reality from the self-adjointness of `T_n` for the Petersson product), i.e. they describe which
`f` are being considered; they are not unproved analytic inputs about `L(f,s)`.

From them we build `eigenData f hf : EData` with `λ(n) = a_f(n)/n^{(k−1)/2}`,
`L(s) = L(f, s + (k−1)/2)` and Rankin's constant `rsConst f`, using

* `HeckeConvexGeneral.fL` (entire continuation, `fL_eq_LSeries` on `Re s > (k+1)/2`);
* `RankinExact.rankinSelberg_exact_general` (error `O(N^{3/5})`, every weight);
* `HardyZerosGeneral.heckeLambda_conj` (real coefficients ⇒ `Λ(s̄) = conj Λ(s)`);
* `RankinSelbergGeneral.rsConst_pos`.

We also prove `IsNormalizedEigenform Δ` (Mordell's multiplicativity and Hecke recurrence for `τ`).
-/
import RamanujanTau.EigenformEdge.Edge
import RamanujanTau.HeckeConvexGeneral.Main
import RamanujanTau.RankinExact.Main
import RamanujanTau.HardyZerosGeneral.Fourier
import RamanujanTau.RankinSelbergGeneral.Positive

set_option autoImplicit false

namespace RamanujanTau.EigenformEdge

open Complex Finset Filter LSeries ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups ComplexConjugate Real

variable {k : ℕ}

/-- **Normalized Hecke eigenform of level one, weight `k`**, expressed through its
q-expansion coefficients `a_f(n) = coef f n`. -/
structure IsNormalizedEigenform (f : CuspForm 𝒮ℒ (k : ℤ)) : Prop where
  real : ∀ n, (coef f n).im = 0
  one : coef f 1 = 1
  mul : ∀ {m n : ℕ}, m.Coprime n → coef f (m * n) = coef f m * coef f n
  hecke : ∀ {p : ℕ}, p.Prime → ∀ e : ℕ,
    coef f (p ^ (e + 2)) = coef f p * coef f (p ^ (e + 1)) - (p : ℂ) ^ (k - 1) * coef f (p ^ e)

section

variable {f : CuspForm 𝒮ℒ (k : ℤ)}

lemma IsNormalizedEigenform.ne_zero (hf : IsNormalizedEigenform f) : f ≠ 0 := by
  rintro rfl
  have := hf.one
  simp [coef, UpperHalfPlane.qExpansion_zero] at this

lemma IsNormalizedEigenform.twelve_le (hf : IsNormalizedEigenform f) : 12 ≤ k := by
  by_contra h
  exact hf.ne_zero (eq_zero_of_lt_twelve f (by omega))

lemma IsNormalizedEigenform.one_le (hf : IsNormalizedEigenform f) : 1 ≤ k := by
  have := hf.twelve_le; omega

lemma IsNormalizedEigenform.coef_eq (hf : IsNormalizedEigenform f) (n : ℕ) :
    coef f n = ((coef f n).re : ℂ) :=
  Complex.ext (by simp) (by simp [hf.real n])

end

/-! ## Normalization -/

/-- `n^{(k−1)/2} = (√n)^{k−1}`. -/
noncomputable def nrm (k n : ℕ) : ℝ := Real.sqrt n ^ (k - 1)

lemma nrm_mul (k m n : ℕ) : nrm k (m * n) = nrm k m * nrm k n := by
  simp only [nrm, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_pow]

lemma nrm_pow (k p e : ℕ) : nrm k (p ^ e) = nrm k p ^ e := by
  induction e with
  | zero => simp [nrm]
  | succ e ih => rw [pow_succ, nrm_mul, ih, pow_succ]

lemma nrm_sq (k p : ℕ) : nrm k p ^ 2 = (p : ℝ) ^ (k - 1) := by
  rw [nrm, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

lemma nrm_pos (k : ℕ) {n : ℕ} (hn : n ≠ 0) : 0 < nrm k n := by
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold nrm; positivity

/-- `n^{(k−1)/2}` as a complex power. -/
lemma natCast_cpow_half (hk : 1 ≤ k) (n : ℕ) :
    (n : ℂ) ^ (((k : ℂ) - 1) / 2) = (nrm k n : ℂ) := by
  have e : ((k : ℂ) - 1) / 2 = (((k - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) : ℝ) := by
    push_cast [Nat.cast_sub hk]; ring
  rw [e, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (Nat.cast_nonneg _), nrm, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

/-- The normalized coefficients `λ_f(n) = a_f(n)/n^{(k−1)/2}`. -/
noncomputable def nlam (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : ℝ := (coef f n).re / nrm k n

lemma nlam_zero (f : CuspForm 𝒮ℒ (k : ℤ)) : nlam f 0 = 0 := by simp [nlam, coef_zero]

/-- The normalized L-function `L(f, s + (k−1)/2)`. -/
noncomputable def Lf (f : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : ℂ := fL f (s + ((k : ℂ) - 1) / 2)

/-- `fL f (conj s) = conj (fL f s)` for real coefficients. -/
lemma fL_conj (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) (s : ℂ) :
    fL f (conj s) = conj (fL f s) := by
  have h2π : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [fL, fL, HardyZerosGeneral.heckeLambda_conj f hreal, Complex.Gamma_conj, map_mul, map_mul,
    map_inv₀, h2π, HeckeZeros.ofReal_cpow_conj (by positivity)]

section

variable {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f)
include hf

lemma nlam_one : nlam f 1 = 1 := by simp [nlam, nrm, hf.one]

lemma nlam_mul {m n : ℕ} (h : m.Coprime n) : nlam f (m * n) = nlam f m * nlam f n := by
  simp only [nlam, nrm_mul, hf.mul h, Complex.mul_re, hf.real m, hf.real n, mul_zero, sub_zero]
  rw [mul_div_mul_comm]

lemma nlam_rec {p : ℕ} (hp : p.Prime) (e : ℕ) :
    nlam f (p ^ (e + 2)) = nlam f p * nlam f (p ^ (e + 1)) - nlam f (p ^ e) := by
  have h := congrArg Complex.re (hf.hecke hp e)
  have hq : ((p : ℂ) ^ (k - 1)).im = 0 := by
    rw [← Nat.cast_pow]; exact Complex.natCast_im _
  have hq' : ((p : ℂ) ^ (k - 1)).re = (p : ℝ) ^ (k - 1) := by
    rw [← Nat.cast_pow, Complex.natCast_re]; push_cast; rfl
  simp only [Complex.sub_re, Complex.mul_re, hf.real, hq, mul_zero, sub_zero, hq'] at h
  have hn := nrm_pos k hp.ne_zero
  simp only [nlam, nrm_pow]
  rw [h]
  have hs := nrm_sq k p
  field_simp
  rw [← hs]; ring

lemma sum_nlam_sq (N : ℕ) :
    ∑ n ∈ Icc 1 N, nlam f n ^ 2 =
      ∑ n ∈ Icc 1 N, RankinSelbergGeneral.coeffSq f n / (n : ℝ) ^ (k - 1) := by
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hn' := nrm_pos k hn0
  have hsq : nrm k n ^ 2 = (n : ℝ) ^ (k - 1) := nrm_sq k n
  rw [nlam, div_pow, hsq, coeffSq_eq, Complex.sq_norm, Complex.normSq_apply, hf.real n]
  ring

lemma Lf_eq {s : ℂ} (hs : 1 < s.re) : Lf f s = LSeries (fun n => (nlam f n : ℂ)) s := by
  have hk := hf.one_le
  have hre : ((k : ℝ) + 1) / 2 < (s + ((k : ℂ) - 1) / 2).re := by
    simp; linarith
  rw [Lf, fL_eq_LSeries f hk hre, LSeries, LSeries]
  congr 1; funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, cpow_add _ _ (by exact_mod_cast hn),
    natCast_cpow_half hk, hf.coef_eq n, nlam]
  have h1 : (n : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hn (by exact_mod_cast h.1)
  have h2 : (nrm k n : ℂ) ≠ 0 := by exact_mod_cast (nrm_pos k hn).ne'
  push_cast
  field_simp

end

/-! ## The data of an eigenform -/

/-- The normalized data of a normalized eigenform. -/
noncomputable def eigenData (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : IsNormalizedEigenform f) : EData where
  lam := nlam f
  lam_zero := nlam_zero f
  lam_one := nlam_one hf
  lam_mul := nlam_mul hf
  lam_rec := nlam_rec hf
  rsc := RankinSelbergGeneral.rsConst f
  rsc_pos := RankinSelbergGeneral.rsConst_pos f hf.ne_zero
  rs_partial := by
    obtain ⟨C, hC⟩ := RankinExact.rankinSelberg_exact_general f
    exact ⟨C, fun N hN => by rw [sum_nlam_sq hf]; exact hC N hN⟩
  L := Lf f
  L_diff := (fL_entire f hf.one_le).comp (differentiable_id.add_const _)
  L_eq := fun _ hs => Lf_eq hf hs
  L_conj := fun s => by
    unfold Lf
    have e : conj s + ((k : ℂ) - 1) / 2 = conj (s + ((k : ℂ) - 1) / 2) := by
      simp [map_add, map_div₀, map_sub, map_natCast, map_one, map_ofNat]
    rw [e, fL_conj f hf.real]

section

variable {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f)
include hf

lemma Lf_shift (s : ℂ) : fL f s = Lf f (s - ((k : ℂ) - 1) / 2) := by
  rw [Lf, sub_add_cancel]

/-- **`L(f,s) ≠ 0` on `Re s > (k+1)/2`** (Euler product). -/
theorem fL_ne_zero_of_gt {s : ℂ} (hs : ((k : ℝ) + 1) / 2 < s.re) : fL f s ≠ 0 := by
  letI := eigenData f hf
  rw [Lf_shift hf]
  exact L_ne_zero_of_gt (s := s - ((k : ℂ) - 1) / 2) (by simp; linarith)

/-- **Edge non-vanishing off the real axis** (unconditional): `L(f, (k+1)/2 + it) ≠ 0` for
`t ≠ 0`. -/
theorem fL_ne_zero_edge_of_ne {t : ℝ} (ht : t ≠ 0) :
    fL f (((k : ℂ) + 1) / 2 + t * I) ≠ 0 := by
  letI := eigenData f hf
  rw [Lf_shift hf, show ((k : ℂ) + 1) / 2 + t * I - ((k : ℂ) - 1) / 2 = 1 + t * I by ring]
  exact L_ne_zero_edge_of_ne ht

/-- **Edge non-vanishing**: `L(f, (k+1)/2 + it) ≠ 0` for all `t`, given the real edge value
`L(f, (k+1)/2) ≠ 0` (which `fL_edge_real_ne_zero_of_imagAxis_nonneg` supplies when `f(iy) ≥ 0`,
e.g. for `Δ`). -/
theorem fL_ne_zero_edge (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) (t : ℝ) :
    fL f (((k : ℂ) + 1) / 2 + t * I) ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using h0
  · exact fL_ne_zero_edge_of_ne hf ht

/-- Non-vanishing on the closed half-plane `Re s ≥ (k+1)/2`, given the real edge value. -/
theorem fL_ne_zero_of_ge (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) {s : ℂ}
    (hs : ((k : ℝ) + 1) / 2 ≤ s.re) : fL f s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · exact fL_ne_zero_of_gt hf hs
  · have e : s = ((k : ℂ) + 1) / 2 + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [← hs]
    rw [e]; exact fL_ne_zero_edge hf h0 _

/-- By the functional equation: no zeros on `Re s ≤ (k−1)/2` except the trivial ones `s = −n`. -/
theorem fL_ne_zero_of_le (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) {s : ℂ}
    (hs : s.re ≤ ((k : ℝ) - 1) / 2) (hn : ∀ n : ℕ, s ≠ -n) : fL f s ≠ 0 := by
  have hk := hf.one_le
  intro h
  have hre : ((k : ℝ) + 1) / 2 ≤ ((k : ℂ) - s).re := by simp; linarith
  have hpos : 0 < ((k : ℂ) - s).re := lt_of_lt_of_le (by positivity) hre
  have hFE := fL_functional_equation f hk hn (HeckeZeros.ne_neg_nat_of_re_pos hpos)
  rw [h, mul_zero, mul_zero] at hFE
  have hG := Complex.Gamma_ne_zero (HeckeZeros.ne_neg_nat_of_re_pos hpos)
  have h2 := two_pi_cpow_ne_zero (-((k : ℂ) - s))
  exact fL_ne_zero_of_ge hf h0 hre (by simpa [h2, hG] using hFE)

/-- **The nontrivial zeros lie in the open strip** `(k−1)/2 < Re s < (k+1)/2`. -/
theorem fL_zeros_in_strip (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) {s : ℂ} (h : fL f s = 0)
    (hn : ∀ n : ℕ, s ≠ -n) : ((k : ℝ) - 1) / 2 < s.re ∧ s.re < ((k : ℝ) + 1) / 2 := by
  constructor
  · by_contra hc; push Not at hc; exact fL_ne_zero_of_le hf h0 hc hn h
  · by_contra hc; push Not at hc; exact fL_ne_zero_of_ge hf h0 hc h

end

end RamanujanTau.EigenformEdge
