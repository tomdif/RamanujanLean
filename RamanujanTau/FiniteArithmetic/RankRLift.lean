import RamanujanTau.FiniteArithmetic.RankRMod
import RamanujanTau.FiniteArithmetic.RankSLift
import RamanujanTau.FiniteArithmetic.OrbitLiftR

/-!
# The ℓ-adic recurrence of order `r` with `s + r` forms

If `ℓ s < δ`, `D` kills `a₀, …, a_s`, and the odd vectors satisfy `o_{n+r} = Σⱼ kⱼ o_{n+j}`.
The `r × r` matrix of `(a_{s+1}, …, a_{s+r})` on `o_n, …, o_{n+r-1}` is multiplied by the
companion matrix `C k` at each step (`oddM_succ`), so its determinant is `det₀ · (det C)ⁿ`.
When that is nonzero, `L(2n+2r+1) − Σⱼ κⱼ L(2(n+j)+1) = ℓ^(n+1) Gₙ` (`odd_padicR`).
The envelopes are those of `RankSLift`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankR
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal
open RankS (B Xop X_mem B_div B_mono odd_mem odd_succ odd_D even_U mem_lowKer toZMod_prime_zmod
  lift_val)

variable {ℓ s r : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Linear algebra of the coordinates -/

lemma mv_add {m n : ℕ} (M : Fin m → Fin n → ZMod ℓ) (u v : Fin n → ZMod ℓ) :
    mv M (u + v) = mv M u + mv M v := by
  ext j; simp [mv, mul_add, Finset.sum_add_distrib]

lemma mv_smul {m n : ℕ} (M : Fin m → Fin n → ZMod ℓ) (c : ZMod ℓ) (v : Fin n → ZMod ℓ) :
    mv M (c • v) = c • mv M v := by
  ext j; simp [mv, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

lemma mv_sum {m n : ℕ} {ι : Type*} (t : Finset ι) (M : Fin m → Fin n → ZMod ℓ)
    (v : ι → Fin n → ZMod ℓ) : mv M (∑ x ∈ t, v x) = ∑ x ∈ t, mv M (v x) := by
  ext j; simp only [mv, Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]

/-- The coefficient `a_{k+1}` in coordinates. -/
def lin (D : Data ℓ s r) (k : Fin (s + r)) (v : Fin (s + r) → ZMod ℓ) : ZMod ℓ := ∑ i, D.B k i * v i

lemma lin_add (D : Data ℓ s r) (k : Fin (s + r)) (u v : Fin (s + r) → ZMod ℓ) :
    lin D k (u + v) = lin D k u + lin D k v := by
  simp [lin, mul_add, Finset.sum_add_distrib]

lemma lin_smul (D : Data ℓ s r) (k : Fin (s + r)) (c : ZMod ℓ) (v : Fin (s + r) → ZMod ℓ) :
    lin D k (c • v) = c * lin D k v := by
  simp [lin, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

lemma lin_sum (D : Data ℓ s r) (k : Fin (s + r)) {ι : Type*} (t : Finset ι)
    (v : ι → Fin (s + r) → ZMod ℓ) : lin D k (∑ x ∈ t, v x) = ∑ x ∈ t, lin D k (v x) := by
  simp only [lin, Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]

/-- The index of `a_{s+1+i}`. -/
def high (s : ℕ) {r : ℕ} (i : Fin r) : Fin (s + r) := Fin.natAdd s i

/-- The companion matrix: column `j` of the next window is column `j+1`, the last is `Σ kₜ colₜ`. -/
def comp {p r : ℕ} (k : Fin r → ZMod p) : Matrix (Fin r) (Fin r) (ZMod p) := fun t j =>
  if j.val + 1 < r then (if t.val = j.val + 1 then 1 else 0) else k t

namespace Data
variable (D : Data ℓ s r)

lemma comb_sum {ι : Type*} (t : Finset ι) (v : ι → Fin (s + r) → ZMod ℓ) :
    D.comb (∑ x ∈ t, v x) = ∑ x ∈ t, D.comb (v x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Data.comb]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, D.comb_add, ih]


/-- The window matrix of `(a_{s+1}, …, a_{s+r})` on `o_n, …, o_{n+r-1}`. -/
def oddM (n : ℕ) : Matrix (Fin r) (Fin r) (ZMod ℓ) := fun i j => lin D (high s i) (D.odd (n + j.val))

def det (n : ℕ) : ZMod ℓ := (D.oddM n).det

variable {k : Fin r → ZMod ℓ} (hcay : D.odd r = ∑ j, k j • D.odd j.val)
include hcay

lemma odd_rec (n : ℕ) : D.odd (n + r) = ∑ j, k j • D.odd (n + j.val) := by
  induction n with
  | zero => simpa using hcay
  | succ n ih =>
    rw [show n + 1 + r = (n + r) + 1 by ring,
      show D.odd (n + r + 1) = mv D.Dmat (mv D.Umat (D.odd (n + r))) from rfl, ih, mv_sum, mv_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mv_smul, mv_smul, show n + 1 + j.val = (n + j.val) + 1 by ring]
    rfl

lemma oddM_succ (n : ℕ) : D.oddM (n + 1) = D.oddM n * comp k := by
  ext i j
  simp only [oddM, Matrix.mul_apply, comp]
  by_cases hj : j.val + 1 < r
  · simp only [if_pos hj, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨j.val + 1, hj⟩ (fun t _ ht => if_neg (fun h => ht (Fin.ext h)))
      (by simp), if_pos rfl]
    congr 2
    simp only
    ring
  · simp only [if_neg hj]
    have hjr : j.val = r - 1 := by have := j.isLt; omega
    rw [show n + 1 + j.val = n + r by omega, D.odd_rec hcay n, lin_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lin_smul]; ring

lemma det_eq (n : ℕ) : D.det n = D.det 0 * (comp k).det ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [det, D.oddM_succ hcay, Matrix.det_mul, ← det, ih, pow_succ]; ring

end Data

/-! ### Leading terms and the recurrence -/

section Lift
variable (h29 : 29 ≤ ℓ) (hlow : ℓ * s < δ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (D : Data ℓ s r)

include h29 hlow h24 in
/-- The first `s` coordinates of every odd vector vanish. -/
lemma lin_zero_odd (n : ℕ) (k : Fin (s + r)) (hk : k.val < s) : lin D k (D.odd n) = 0 := by
  have h := congrArg (coeff (k.val + 1)) (D.odd_reduction h24 n)
  rw [coeff_map, show coeff (k.val + 1) (Ll ℓ (2 * n + 1)) = 0 from
    mem_lowKer.mp (odd_mem h29 hlow n).2 ⟨k.val, hk⟩, map_zero] at h
  rw [h, D.coeff_comb]
  rfl

include h29 hlow h24 in
/-- **Leading terms of order `r`.** -/
lemma leadingR (hdet : ∀ n, D.det n ≠ 0) (n : ℕ) (F : PS ℓ) (hF : F ∈ B h29 s 1) :
    ∃ c : Fin r → ℤ_[ℓ], ∃ G : PS ℓ,
      F = ∑ j, c j • Ll ℓ (2 * (n + j.val) + 1) + (ℓ : ℤ_[ℓ]) • G := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (RankS.h5 h29) (β ℓ)
    (fun i hi => (envelopes_ge_two (RankS.h13 h29) i hi).2) F hF.1.2
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [he, coeff_map, hF.1.1, map_zero]
  have ha1 : ∀ t : Fin s, coeff (t.val + 1) (Ψ ℓ a) = 0 := fun t => by
    rw [he, coeff_map, mem_lowKer.mp hF.2 t, map_zero]
  set e : Fin (s + r) → ZMod ℓ := fun i => ∑ k : Fin (s + r), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  have hae : Ψ ℓ a = D.comb e := D.cusp_eq a ha ha0
  set M := D.oddM n
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (hdet n)
  set v : Fin r → ZMod ℓ := fun i => lin D (high s i) e
  set α := M⁻¹.mulVec v
  have hMα : M.mulVec α = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hcomb : D.comb e = D.comb (∑ j, α j • D.odd (n + j.val)) := by
    refine D.comb_eq_of_coeff fun k => ?_
    rw [D.coeff_comb, D.coeff_comb]
    change lin D k e = lin D k (∑ j, α j • D.odd (n + j.val))
    rw [lin_sum]
    simp only [lin_smul]
    rcases Nat.lt_or_ge k.val s with hk | hk
    · have he0 : lin D k e = 0 := by
        rw [show lin D k e = coeff (k.val + 1) (D.comb e) from (D.coeff_comb e k).symm,
          ← hae]; exact ha1 ⟨k.val, hk⟩
      rw [he0]
      exact (Finset.sum_eq_zero fun j _ => by rw [lin_zero_odd h29 hlow h24 D _ k hk, mul_zero]).symm
    · obtain ⟨i, rfl⟩ : ∃ i : Fin r, k = high s i :=
        ⟨⟨k.val - s, by have := k.isLt; omega⟩, Fin.ext (by simp [high]; omega)⟩
      have := congrFun hMα i
      simp only [Matrix.mulVec, dotProduct, M, Data.oddM] at this
      rw [show lin D (high s i) e = v i from rfl, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  set c : Fin r → ℤ_[ℓ] := fun j => (((α j).val : ℕ) : ℤ_[ℓ])
  obtain ⟨G, hG⟩ := PS_dvd_of_map (F - ∑ j, c j • Ll ℓ (2 * (n + j.val) + 1)) (by
    rw [map_sub, map_sum, ← he, hae, hcomb, D.comb_sum]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, lift_val, D.odd_reduction h24,
      D.comb_smul])
  exact ⟨c, G, by rw [← hG]; abel⟩

include h29 hlow h24 in
/-- **The ℓ-adic recurrence of order `r` on the odd chain.** -/
theorem odd_padicR {k : Fin r → ZMod ℓ} (hcay : D.odd r = ∑ j, k j • D.odd j.val)
    (hdet : ∀ n, D.det n ≠ 0) :
    ∃ κ : Fin r → ℤ_[ℓ], (∀ j, PadicInt.toZMod (κ j) = k j) ∧
      ∀ n : ℕ, ∃ G ∈ B h29 s 2,
        Ll ℓ (2 * (n + r) + 1) - ∑ j, κ j • Ll ℓ (2 * (n + j.val) + 1) =
          (ℓ : ℤ_[ℓ]) ^ (n + 1) • G := by
  let O : ℕ → PS ℓ := fun b => Ll ℓ (2 * b - 1)
  have hO (n : ℕ) : O (n + 1) = Ll ℓ (2 * n + 1) := by dsimp [O]; congr 1
  have hO' (n i : ℕ) : O (n + 1 + i * 1) = Ll ℓ (2 * (n + i) + 1) := by
    rw [mul_one, show n + 1 + i = (n + i) + 1 by ring, hO]
  have hrec (b : ℕ) (hb : 1 ≤ b) : O (b + 1) = Xop (O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO, odd_succ]
  have hmem (b : ℕ) (hb : 1 ≤ b) : O b ∈ B h29 s 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact odd_mem h29 hlow n
  have hlead (b : ℕ) (hb : 1 ≤ b) (F : PS ℓ) (hF : F ∈ B h29 s 1) :
      ∃ c : Fin r → ℤ_[ℓ], ∃ G : PS ℓ, F = ∑ j, c j • O (b + j.val * 1) + (ℓ : ℤ_[ℓ]) • G := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    simp only [hO']
    exact leadingR h29 hlow h24 D hdet n F hF
  set q : Fin r → ℤ_[ℓ] := fun j => (((k j).val : ℕ) : ℤ_[ℓ])
  have hbase (b : ℕ) (hb : 1 ≤ b) : Dvd (ℓ : ℤ_[ℓ]) 1 (recR 1 O q b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    obtain ⟨G, hG⟩ := PS_dvd_of_map (recR 1 O q (n + 1)) (by
      rw [recR, show n + 1 + r * 1 = (n + r) + 1 by ring, hO, map_sub, map_sum,
        D.odd_reduction h24, D.odd_rec hcay n, D.comb_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hO', PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, lift_val, D.odd_reduction h24,
        D.comb_smul])
    exact ⟨G, by simpa only [pow_one] using hG⟩
  obtain ⟨κ, hκ, h⟩ := lift_padic_memR 1 r ℓ q (fun _ => Xop) O (fun _ => B h29 s 1)
    (fun _ => B h29 s 2) PS_reg (fun _ => rfl) hrec (fun _ => rfl) hmem
    (fun _ _ F hF => X_mem h29 hlow F hF) hlead (fun _ _ F hF G hFG => B_div h29 F hF G hFG)
    (fun b hb j => B_mono h29 _ (hmem _ (by omega))) hbase
  refine ⟨κ, fun j => ?_, fun n => ?_⟩
  · obtain ⟨d, hd⟩ := hκ j
    rw [hd, map_add, map_mul, toZMod_prime_zmod, zero_mul, add_zero, lift_val]
  · obtain ⟨G, hGm, hG⟩ := h (n + 1) (by omega)
    refine ⟨G, hGm, ?_⟩
    rw [recR, show n + 1 + r * 1 = (n + r) + 1 by ring, hO] at hG
    simp only [hO'] at hG
    exact hG

end Lift

end RamanujanTau.FiniteArithmetic.RankR
