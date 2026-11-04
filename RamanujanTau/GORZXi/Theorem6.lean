/-
# GORZ Theorem 6 (general sequences, general limit `F`)

GORZ, Theorem 6: let `δ(n) → 0` (`δ(n) > 0`), let `F(t) = Σ c_i t^i` be a formal power series, and suppose
there are sequences `C_i(n) → c_i` (`0 ≤ i ≤ d`) with

  `α(n+j)/α(n) · E(n)^{-j} = Σ_{i≤d} C_i(n) δ(n)^i j^i + o(δ(n)^d)`   for every `0 ≤ j ≤ d`   (eq. (8)).

Then `Ĵ^{d,n}(X) = δ^{-d}/α(n) · J^{d,n}_α((δX − 1)/E(n)) → H_{F,d}(X)`, uniformly on compact sets, where
`H_{F,d}(X) = d! Σ_{k≤d} (−1)^{d−k} c_{d−k} X^k / k!`.

* `tendsto_gk_of_thm6` : under (8), `γ_k(n) = Δ^k w_n(0)/δ^k → k! c_k` for `k ≤ d`.
* `HF`, `Hgen_eq_HF` : the paper's closed form of `H_{F,d}` and its identification with `Hgen (k! c_k) d`.
* **`thm6_coeff`, `thm6_uniform`** : GORZ Theorem 6 (coefficientwise and uniformly on compacts).
-/
import RamanujanTau.GORZXi.Core

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial Asymptotics

/-- `Δ^k [j ↦ j^i] (0)` as an alternating sum. -/
noncomputable def apow (k i : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ i

lemma apow_lt {k i : ℕ} (h : i < k) : apow k i = 0 := GORZ.alt_pow_sum_lt h
lemma apow_self (k : ℕ) : apow k k = (k.factorial : ℝ) := GORZ.alt_pow_sum_self k

/-- `o(δ^d)` divided by `δ^k` (`k ≤ d`) tends to `0`. -/
lemma tendsto_div_pow_of_isLittleO {δ e : ℕ → ℝ} {d k : ℕ} (hk : k ≤ d) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδne : ∀ᶠ n in atTop, δ n ≠ 0) (he : e =o[atTop] (fun n => δ n ^ d)) :
    Tendsto (fun n => e n / δ n ^ k) atTop (𝓝 0) := by
  have h1 := he.tendsto_div_nhds_zero
  have h2 := hδ0.pow (d - k)
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [hδne] with n hn
  have e' : δ n ^ d = δ n ^ k * δ n ^ (d - k) := by rw [← pow_add]; congr 1; omega
  rw [e']
  field_simp

/-- **Theorem 6 ⇒ limits of the normalized differences**: `γ_k(n) → k! c_k`. -/
theorem tendsto_gk_of_thm6 {α E δ : ℕ → ℝ} {d : ℕ} (c : ℕ → ℝ) (Cc : ℕ → ℕ → ℝ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hC : ∀ i ≤ d, Tendsto (Cc i) atTop (𝓝 (c i)))
    (herr : ∀ j ≤ d, (fun n => wr α E n j - ∑ i ∈ range (d + 1), Cc i n * δ n ^ i * (j : ℝ) ^ i)
      =o[atTop] (fun n => δ n ^ d))
    (k : ℕ) (hk : k ≤ d) :
    Tendsto (fun n => gk α E δ n k) atTop (𝓝 ((k.factorial : ℝ) * c k)) := by
  set main : ℕ → ℕ → ℝ := fun n j => ∑ i ∈ range (d + 1), Cc i n * δ n ^ i * (j : ℝ) ^ i with hmain
  set e : ℕ → ℕ → ℝ := fun n j => wr α E n j - main n j with he
  have hsplit : ∀ n, gk α E δ n k =
      ∑ i ∈ range (d + 1), Cc i n * apow k i * (δ n ^ i / δ n ^ k) +
        ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (e n j / δ n ^ k) := by
    intro n
    have hw : ∀ j, wr α E n j = main n j + e n j := fun j => by simp [he]
    simp only [gk, GORZ.fd, hw, mul_add, sum_add_distrib, add_div]
    congr 1
    · simp only [hmain, Finset.mul_sum, apow, Finset.sum_div, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun i _ => ?_
      refine sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_div]
      refine sum_congr rfl fun j _ => ?_
      ring
  simp_rw [hsplit]
  have hkd : k ∈ range (d + 1) := Finset.mem_range.mpr (by omega)
  have hlim1 : Tendsto (fun n => ∑ i ∈ range (d + 1), Cc i n * apow k i * (δ n ^ i / δ n ^ k)) atTop
      (𝓝 (∑ i ∈ range (d + 1), if i = k then (k.factorial : ℝ) * c k else 0)) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hi' : i ≤ d := by have := Finset.mem_range.mp hi; omega
    rcases lt_trichotomy i k with h | h | h
    · rw [if_neg h.ne]
      simp [apow_lt h]
    · subst h
      rw [if_pos rfl, apow_self]
      refine ((hC i hi').mul_const (i.factorial : ℝ)).congr' ?_ |>.trans (by rw [mul_comm])
      filter_upwards [hδne] with n hn
      rw [div_self (pow_ne_zero _ hn), mul_one]
    · rw [if_neg h.ne']
      have h2 := ((hC i hi').mul_const (apow k i)).mul (hδ0.pow (i - k))
      rw [zero_pow (by omega), mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [hδne] with n hn
      have e' : δ n ^ i = δ n ^ k * δ n ^ (i - k) := by rw [← pow_add]; congr 1; omega
      rw [e']
      field_simp
  rw [sum_ite_eq' _ _ (fun _ => (k.factorial : ℝ) * c k), if_pos hkd] at hlim1
  have hlim2 : Tendsto (fun n => ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) *
      (e n j / δ n ^ k)) atTop (𝓝 (∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * 0)) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hj' : j ≤ d := by have := Finset.mem_range.mp hj; omega
    exact (tendsto_div_pow_of_isLittleO hk hδ0 hδne (herr j hj')).const_mul _
  simp only [mul_zero, sum_const_zero] at hlim2
  simpa using hlim1.add hlim2

/-- GORZ's closed form `H_{F,d}(X) = d! Σ_{k≤d} (−1)^{d−k} c_{d−k} X^k / k!`. -/
noncomputable def HF (c : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d + 1), C ((d.factorial : ℝ) * (-1) ^ (d - k) * c (d - k) / (k.factorial : ℝ)) * X ^ k

lemma Hgen_eq_HF (c : ℕ → ℝ) (d : ℕ) : Hgen (fun k => (k.factorial : ℝ) * c k) d = HF c d := by
  unfold Hgen HF
  rw [← Finset.sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  rw [show d + 1 - 1 - k = d - k by omega, show d - (d - k) = k by omega, Nat.choose_symm hk']
  congr 2
  have hf := Nat.choose_mul_factorial_mul_factorial hk'
  have hf' : (d.choose k : ℝ) * (k.factorial : ℝ) * ((d - k).factorial : ℝ) = (d.factorial : ℝ) := by
    exact_mod_cast hf
  have hpos : ((d - k).factorial : ℝ) ≠ 0 := by positivity
  rw [← hf']
  field_simp

/-- **GORZ Theorem 6, coefficientwise.** -/
theorem thm6_coeff {α E δ : ℕ → ℝ} {d : ℕ} (c : ℕ → ℝ) (Cc : ℕ → ℕ → ℝ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hC : ∀ i ≤ d, Tendsto (Cc i) atTop (𝓝 (c i)))
    (herr : ∀ j ≤ d, (fun n => wr α E n j - ∑ i ∈ range (d + 1), Cc i n * δ n ^ i * (j : ℝ) ^ i)
      =o[atTop] (fun n => δ n ^ d)) (i : ℕ) :
    Tendsto (fun n => (Jhat α E δ d n).coeff i) atTop (𝓝 ((HF c d).coeff i)) := by
  rw [← Hgen_eq_HF]
  exact tendsto_coeff_Jhat_of_gk hδ0 hδne (fun k hk => tendsto_gk_of_thm6 c Cc hδ0 hδne hC herr k hk) i

/-- **GORZ Theorem 6**: `Ĵ^{d,n} → H_{F,d}` uniformly on compact subsets of `ℝ`. -/
theorem thm6_uniform {α E δ : ℕ → ℝ} {d : ℕ} (c : ℕ → ℝ) (Cc : ℕ → ℕ → ℝ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ n in atTop, δ n ≠ 0)
    (hC : ∀ i ≤ d, Tendsto (Cc i) atTop (𝓝 (c i)))
    (herr : ∀ j ≤ d, (fun n => wr α E n j - ∑ i ∈ range (d + 1), Cc i n * δ n ^ i * (j : ℝ) ^ i)
      =o[atTop] (fun n => δ n ^ d)) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => (Jhat α E δ d n).eval x) (fun x => (HF c d).eval x) atTop K := by
  rw [← Hgen_eq_HF]
  exact tendstoUniformlyOn_Jhat_of_gk hδ0 hδne (fun k hk => tendsto_gk_of_thm6 c Cc hδ0 hδne hC herr k hk) hK

end GORZXi
