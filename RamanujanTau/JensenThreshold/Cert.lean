/-
# Integer certificates for (non-)hyperbolicity of partition Jensen polynomials

All values `p(n+j)` are read from the packed table `ptP B N` (exact by `ptP_spec`), so a certificate is a
`Bool` computation that the kernel can evaluate.

* `checkPts B T d n pts` : `pts = [(u₀,v₀), …, (u_d,v_d)]` gives points `xᵢ = −uᵢ/vᵢ`, increasing in `i`, with
  `(−1)^{d−i}·vᵢᵈ·J^{d,n}(xᵢ) > 0` (an integer). Sound by `hyperbolic_of_checkPts`.
* `lagOK B T d n u v` : Laguerre's inequality fails at `x = −u/v`. Sound by `not_hyperbolic_of_lagOK`.
-/
import RamanujanTau.JensenThreshold.Table
import RamanujanTau.JensenThreshold.Basic

set_option autoImplicit false

namespace JensenThreshold
open Polynomial

/-- `vᵈ·J(−u/v)` from the table. -/
def S0 (B T d n u v : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), (d.choose j : ℤ) * (look B T (n + j) : ℤ) * (-(u : ℤ)) ^ j * (v : ℤ) ^ (d - j)

/-- `vᵈ⁻¹·J'(−u/v)` from the table. -/
def S1 (B T d n u v : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1),
    (d.choose j : ℤ) * (look B T (n + j) : ℤ) * j * (-(u : ℤ)) ^ (j - 1) * (v : ℤ) ^ (d - j)

/-- `vᵈ⁻²·J''(−u/v)` from the table. -/
def S2 (B T d n u v : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1),
    (d.choose j : ℤ) * (look B T (n + j) : ℤ) * j * ((j - 1 : ℕ) : ℤ) * (-(u : ℤ)) ^ (j - 2) * (v : ℤ) ^ (d - j)

def pt (pts : List (ℕ × ℕ)) (i : ℕ) : ℕ × ℕ := pts.getD i (0, 0)

def checkPts (B T d n : ℕ) (pts : List (ℕ × ℕ)) : Bool :=
  (List.range d).all (fun i => (pt pts (i + 1)).1 * (pt pts i).2 < (pt pts i).1 * (pt pts (i + 1)).2) &&
  (List.range (d + 1)).all (fun i => decide (0 < (pt pts i).2) &&
    decide (0 < (-1 : ℤ) ^ (d - i) * S0 B T d n (pt pts i).1 (pt pts i).2))

/-- check `checkPts` for `n = n₀, n₀+1, …` against consecutive certificates. -/
def checkAll (B T d : ℕ) : ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [] => true
  | n, l :: ls => checkPts B T d n l && checkAll B T d (n + 1) ls

def lagOK (B T d n u v : ℕ) : Bool :=
  decide (0 < v) && decide (((d : ℤ) - 1) * S1 B T d n u v ^ 2 < d * S0 B T d n u v * S2 B T d n u v)

lemma checkAll_spec {B T d : ℕ} : ∀ (L : List (List (ℕ × ℕ))) (n₀ : ℕ), checkAll B T d n₀ L = true →
    ∀ i < L.length, checkPts B T d (n₀ + i) (L.getD i []) = true
  | [], _, _, i, hi => by simp at hi
  | l :: ls, n₀, h, i, hi => by
    simp only [checkAll, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := checkAll_spec ls (n₀ + 1) h.2 i (by simpa using hi)
      simpa [show n₀ + (i + 1) = n₀ + 1 + i by omega] using this

variable {B N : ℕ}

lemma look_cast (hB : 0 < B) (hok : (ptP B N).ok = true) {m : ℕ} (hm : m ≤ N) :
    ((look B (ptP B N).T m : ℤ) : ℝ) = (pc m : ℝ) := by
  rw [ptP_spec hB hok hm]; rfl

lemma S0_eq (hB : 0 < B) (hok : (ptP B N).ok = true) {d n : ℕ} (hN : n + d ≤ N) (u v : ℕ) (hv : 0 < v) :
    (S0 B (ptP B N).T d n u v : ℝ) = (v : ℝ) ^ d * (jensen d n).eval (-((u : ℝ) / v)) := by
  rw [scaled_eval d n u v hv, S0]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have := look_cast hB hok (m := n + j) (by omega)
  push_cast at this
  rw [this]

lemma S1_eq (hB : 0 < B) (hok : (ptP B N).ok = true) {d n : ℕ} (hN : n + d ≤ N) (u v : ℕ) (hv : 0 < v) :
    (S1 B (ptP B N).T d n u v : ℝ) = (v : ℝ) ^ (d - 1) * (derivative (jensen d n)).eval (-((u : ℝ) / v)) := by
  rw [scaled_eval_derivative d n u v hv, S1]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have := look_cast hB hok (m := n + j) (by omega)
  push_cast at this
  rw [this]

lemma S2_eq (hB : 0 < B) (hok : (ptP B N).ok = true) {d n : ℕ} (hN : n + d ≤ N) (u v : ℕ) (hv : 0 < v) :
    (S2 B (ptP B N).T d n u v : ℝ) =
      (v : ℝ) ^ (d - 2) * (derivative (derivative (jensen d n))).eval (-((u : ℝ) / v)) := by
  rw [scaled_eval_derivative2 d n u v hv, S2]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have := look_cast hB hok (m := n + j) (by omega)
  push_cast at this
  rw [this]

theorem hyperbolic_of_checkPts (hB : 0 < B) (hok : (ptP B N).ok = true) {d n : ℕ} (hN : n + d ≤ N)
    (pts : List (ℕ × ℕ)) (h : checkPts B (ptP B N).T d n pts = true) : Hyperbolic (jensen d n) := by
  simp only [checkPts, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hmono, hsgn⟩ := h
  set x : ℕ → ℝ := fun i => -(((pt pts i).1 : ℝ) / (pt pts i).2)
  have hvpos : ∀ i < d + 1, 0 < (pt pts i).2 := fun i hi => (hsgn i hi).1
  -- sign of the scaled value
  have hval : ∀ i < d + 1, 0 < (-1 : ℝ) ^ (d - i) * ((pt pts i).2 : ℝ) ^ d * (jensen d n).eval (x i) := by
    intro i hi
    have h1 := (hsgn i hi).2
    have h2 := S0_eq hB hok hN (pt pts i).1 (pt pts i).2 (hvpos i hi)
    have : (0 : ℝ) < (-1 : ℝ) ^ (d - i) * (S0 B (ptP B N).T d n (pt pts i).1 (pt pts i).2 : ℝ) := by
      exact_mod_cast h1
    rw [h2] at this
    simpa [x, mul_assoc] using this
  apply hyperbolic_of_alternating _ d (natDegree_jensen_le d n) x
  · intro i hi
    have hm := hmono i hi
    have v1 := hvpos i (by omega)
    have v2 := hvpos (i + 1) (by omega)
    simp only [x, neg_lt_neg_iff]
    rw [div_lt_div_iff₀ (by exact_mod_cast v2) (by exact_mod_cast v1)]
    exact_mod_cast hm
  · intro i hi
    have a1 := hval i (by omega)
    have a2 := hval (i + 1) (by omega)
    have hs : (-1 : ℝ) ^ (d - i) = -(-1 : ℝ) ^ (d - (i + 1)) := by
      rw [show d - i = d - (i + 1) + 1 by omega, pow_succ]; ring
    rw [hs] at a1
    have p1 : (0 : ℝ) < ((pt pts i).2 : ℝ) ^ d := by have := hvpos i (by omega); positivity
    have p2 : (0 : ℝ) < ((pt pts (i + 1)).2 : ℝ) ^ d := by have := hvpos (i + 1) (by omega); positivity
    set s := (-1 : ℝ) ^ (d - (i + 1))
    have hs2 : s ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    set e1 := (jensen d n).eval (x i)
    set e2 := (jensen d n).eval (x (i + 1))
    have : 0 < (-s * ((pt pts i).2 : ℝ) ^ d * e1) * (s * ((pt pts (i + 1)).2 : ℝ) ^ d * e2) :=
      mul_pos a1 a2
    have key : (-s * ((pt pts i).2 : ℝ) ^ d * e1) * (s * ((pt pts (i + 1)).2 : ℝ) ^ d * e2) =
        -(((pt pts i).2 : ℝ) ^ d * ((pt pts (i + 1)).2 : ℝ) ^ d) * (e1 * e2) := by
      linear_combination (-(((pt pts i).2 : ℝ) ^ d * ((pt pts (i + 1)).2 : ℝ) ^ d) * (e1 * e2)) * hs2
    rw [key] at this
    have pp := mul_pos p1 p2
    by_contra hcon
    push Not at hcon
    nlinarith

theorem not_hyperbolic_of_lagOK (hB : 0 < B) (hok : (ptP B N).ok = true) {d n : ℕ} (hN : n + d ≤ N)
    (hd : 2 ≤ d) (u v : ℕ) (h : lagOK B (ptP B N).T d n u v = true) : ¬ Hyperbolic (jensen d n) := by
  simp only [lagOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hlag⟩ := h
  apply not_hyperbolic_of_laguerre _ (-((u : ℝ) / v))
  rw [natDegree_jensen]
  have e0 := S0_eq hB hok hN u v hv
  have e1 := S1_eq hB hok hN u v hv
  have e2 := S2_eq hB hok hN u v hv
  have hlagR : ((d : ℝ) - 1) * (S1 B (ptP B N).T d n u v : ℝ) ^ 2 <
      d * (S0 B (ptP B N).T d n u v : ℝ) * (S2 B (ptP B N).T d n u v : ℝ) := by exact_mod_cast hlag
  rw [e0, e1, e2] at hlagR
  set J := (jensen d n).eval (-((u : ℝ) / v))
  set J1 := (derivative (jensen d n)).eval (-((u : ℝ) / v))
  set J2 := (derivative (derivative (jensen d n))).eval (-((u : ℝ) / v))
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hw : (0 : ℝ) < (v : ℝ) ^ (d - 1) ^ 2 := by positivity
  have hpow1 : ((v : ℝ) ^ (d - 1)) ^ 2 = (v : ℝ) ^ d * (v : ℝ) ^ (d - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have : ((v : ℝ) ^ (d - 1)) ^ 2 * (((d : ℝ) - 1) * J1 ^ 2) < ((v : ℝ) ^ (d - 1)) ^ 2 * (d * J * J2) := by
    calc ((v : ℝ) ^ (d - 1)) ^ 2 * (((d : ℝ) - 1) * J1 ^ 2)
        = ((d : ℝ) - 1) * ((v : ℝ) ^ (d - 1) * J1) ^ 2 := by ring
      _ < d * ((v : ℝ) ^ d * J) * ((v : ℝ) ^ (d - 2) * J2) := hlagR
      _ = ((v : ℝ) ^ d * (v : ℝ) ^ (d - 2)) * (d * J * J2) := by ring
      _ = _ := by rw [hpow1]
  exact lt_of_mul_lt_mul_left this (by positivity)

end JensenThreshold
