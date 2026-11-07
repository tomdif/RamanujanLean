import RamanujanTau.FiniteArithmetic.Rank607Final

/-! # The stable module at 607 modulo `607²`

`Λ = Λ^odd(3, 2)` is spanned by `L(3), L(5), …, L(51)`, and

`Λ ≅ (ℤ/607²)²⁴ ⊕ ℤ/607`.

So at precision two the module needs 25 generators but has exactly 24 free
summands. Explicitly, with `V_j = L(2j+3)` and

`w = L(51) - Σ_{j<24} t_j L(2j+3)`,

the generators `V_0, …, V_23, w` satisfy `Σ a_j g_j = 0` exactly when
`a_0 = … = a_23 = 0` and `607 ∣ a_24`.

Inputs, all checked here by the kernel:
* `L(1), …, L(53)` in the reconstruction basis (`Rank607Final.series_eq`);
* `L(53) = Σ rel_j L(2j+3)`, coordinate by coordinate;
* `607 w = 0`, coordinate by coordinate;
* an elimination matrix `P` with `P G = diag(1, …, 1, 607 u)`, `u` a unit,
  where `G` holds coefficients `q²⁶ … q⁵⁰` of the generators.
-/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamanujanTau.FiniteArithmetic.Rank607Structure

open PowerSeries Rank607Program Rank607Series Rank607Final BLBound
open BoylanWebb (L)

/-! ### Certificates -/

/-- Coordinate `k` of `L(b)`. -/
def crd (b k : ℕ) : R := ((coordAt b).getD k 0 : ℕ)

def tv (i : ℕ) : R := (tTable.getD i 0 : ℕ)

def rv (j : ℕ) : R := (relTable.getD j 0 : ℕ)

/-- Coefficients `q^(i+26)` of the generators `V_0, …, V_23, w`. -/
def Gm : Matrix (Fin 25) (Fin 25) R := fun i j =>
  if (j : ℕ) < 24 then (entryAt i j : R)
  else (entryAt i 24 : R) - ∑ l : Fin 24, tv l * (entryAt i l : R)

def Pm : Matrix (Fin 25) (Fin 25) R := fun i j => ((pTable.getD i []).getD j 0 : ℕ)

def Dm : Matrix (Fin 25) (Fin 25) R := fun i j =>
  if i = j then (if (i : ℕ) < 24 then 1 else 607 * (uVal : R)) else 0

theorem elim_ok : Pm * Gm = Dm := by decide +kernel

theorem rel53_ok : ∀ k : Fin 102,
    crd 53 k = ∑ j : Fin 25, rv j * crd (2 * (j : ℕ) + 3) k := by decide +kernel

theorem tor_ok : ∀ k : Fin 102,
    (607 : R) * (crd 51 k - ∑ j : Fin 24, tv j * crd (2 * (j : ℕ) + 3) k) = 0 := by
  decide +kernel

theorem u_ok : (uVal : R) * (uInv : R) = 1 := by decide +kernel

attribute [local irreducible] coordAt entryAt tTable relTable pTable uVal uInv

/-! ### Series in coordinates -/

lemma comboS_eq_sum (F : ℕ → PowerSeries R) : ∀ (ds : List ℕ) (t n : ℕ), ds.length ≤ n →
    comboS ds F t = ∑ k ∈ Finset.range n, C ((ds.getD k 0 : ℕ) : R) * F (t + k)
  | [], t, n, _ => by simp [comboS]
  | d :: ds, t, n, h => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', comboS, comboS_eq_sum F ds (t + 1) n (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show t + 1 + k = t + (k + 1) by omega]

lemma len_ok : ∀ b < 54, (coordAt b).length ≤ 102 := by
  obtain ⟨-, -, -, h, -⟩ := final_unroll
  exact h

/-- A fixed inverse of `E₄³` used by the basis. -/
noncomputable def vInv : PowerSeries R := (series_eq).choose

lemma vInv_spec : ModP.E4 R ^ 3 * vInv = 1 := (series_eq).choose_spec.1

noncomputable abbrev B (k : ℕ) : PowerSeries R := Bs vInv k

lemma L_coords (b : ℕ) (h1 : 1 ≤ b) (h53 : b ≤ 53) :
    rd (L 607 b) = ∑ k ∈ Finset.range 102, C (crd b k) * B k := by
  rw [(series_eq).choose_spec.2 b h1 h53, comboS_eq_sum _ _ 0 102 (len_ok b (by omega))]
  simp [crd, B, vInv]

/-- Linear combinations of iterates, in coordinates. -/
lemma sum_smul_L {n : ℕ} (a : Fin n → R) (b : Fin n → ℕ) (hb : ∀ j, 1 ≤ b j ∧ b j ≤ 53) :
    ∑ j, a j • rd (L 607 (b j)) =
      ∑ k ∈ Finset.range 102, C (∑ j, a j * crd (b j) k) * B k := by
  simp_rw [fun j => L_coords (b j) (hb j).1 (hb j).2, Finset.smul_sum, smul_eq_C_mul,
    ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← map_sum]

/-! ### Generators -/

/-- `V_j = L(2j+3)` modulo `607²`. -/
noncomputable abbrev V (j : ℕ) : PowerSeries R := rd (L 607 (2 * j + 3))

/-- The torsion generator `w = L(51) - Σ t_j L(2j+3)`. -/
noncomputable def w : PowerSeries R := V 24 - ∑ j : Fin 24, tv j • V j

noncomputable def gen (j : Fin 25) : PowerSeries R := if (j : ℕ) < 24 then V j else w

theorem L53_eq : rd (L 607 53) = ∑ j : Fin 25, rv j • V j := by
  rw [sum_smul_L (fun j : Fin 25 => rv j) (fun j => 2 * (j : ℕ) + 3)
    (fun j => ⟨by dsimp only; omega, by dsimp only; have := j.isLt; omega⟩), L_coords 53 (by norm_num) le_rfl]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [rel53_ok ⟨k, Finset.mem_range.mp hk⟩]

theorem w_torsion : (607 : R) • w = 0 := by
  have h1 := L_coords 51 (by norm_num) (by norm_num)
  have h2 := sum_smul_L (fun j : Fin 24 => tv j) (fun j => 2 * (j : ℕ) + 3)
    (fun j => ⟨by dsimp only; omega, by dsimp only; have := j.isLt; omega⟩)
  have hw : w = ∑ k ∈ Finset.range 102,
      C (crd 51 k - ∑ j : Fin 24, tv j * crd (2 * (j : ℕ) + 3) k) * B k := by
    rw [w, show V 24 = rd (L 607 51) from rfl, h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sub, sub_mul]
  rw [hw, Finset.smul_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← map_mul, tor_ok ⟨k, Finset.mem_range.mp hk⟩, map_zero,
    zero_mul]

/-! ### The span -/

/-- The span of `L(3), …, L(51)`. -/
noncomputable def S : Submodule R (PowerSeries R) := Submodule.span R (Set.range fun j : Fin 25 => V j)

lemma V_mem (j : ℕ) (hj : j < 25) : V j ∈ S :=
  Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

lemma X_V (j : ℕ) : Xm 607 2 (V j) = V (j + 1) := by
  have h := Xm_L (ℓ := 607) 2 (j + 1)
  rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1 + 1) + 1 = 2 * (j + 1) + 3 by ring]
    at h
  exact h

lemma S_stable : ∀ f ∈ S, Xm 607 2 f ∈ S := by
  intro f hf
  have hle : S ≤ S.comap (Xm 607 2) := by
    rw [S, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change Xm 607 2 (V j) ∈ S
    rw [X_V]
    by_cases hj : (j : ℕ) < 24
    · exact V_mem _ (by omega)
    · have h24 : (j : ℕ) + 1 = 25 := by omega
      rw [h24, show V 25 = rd (L 607 53) from rfl, L53_eq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (V_mem _ i.isLt)
  exact hle hf

lemma L_mem (k : ℕ) (hk : 1 ≤ k) : rd (L 607 (2 * k + 1)) ∈ S := by
  induction k, hk using Nat.le_induction with
  | base => exact V_mem 0 (by norm_num)
  | succ k hk ih =>
    have h := Xm_L (ℓ := 607) 2 k
    rw [← h]
    exact S_stable _ ih

theorem S_eq_Lam : S = Lam 607 2 3 := by
  apply le_antisymm
  · rw [S, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(j : ℕ) + 1, by omega, by congr 2⟩
  · rw [Lam, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact L_mem k (by omega)

theorem span_gen : Submodule.span R (Set.range gen) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold gen
    split_ifs with hj
    · exact V_mem _ (by omega)
    · rw [w]
      exact Submodule.sub_mem _ (V_mem 24 (by norm_num))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (V_mem _ (by omega)))
  · rw [S, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hg : ∀ i : Fin 25, gen i ∈ Submodule.span R (Set.range gen) :=
      fun i => Submodule.subset_span ⟨i, rfl⟩
    by_cases hj : (j : ℕ) < 24
    · have := hg j
      simp only [gen, if_pos hj] at this
      exact this
    · have hj24 : (j : ℕ) = 24 := by omega
      have hV : V 24 = w + ∑ i : Fin 24, tv i • gen (Fin.castSucc i) := by
        simp only [gen, Fin.val_castSucc, Fin.is_lt, if_true, w]
        abel
      change V (j : ℕ) ∈ _
      rw [hj24, hV]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg _))
      have := hg 24
      simpa [gen] using this

/-! ### Relations -/

lemma coeff_gen (i j : Fin 25) : coeff ((i : ℕ) + 26) (gen j) = Gm i j := by
  have hV : ∀ l : ℕ, l < 25 → coeff ((i : ℕ) + 26) (V l) = (entryAt i l : R) :=
    fun l hl => entries_eq i l i.isLt hl
  unfold gen Gm
  split_ifs with hj
  · exact hV j j.isLt
  · rw [w, map_sub, map_sum, hV 24 (by norm_num), sub_right_inj]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [coeff_smul, hV l (by have := l.isLt; omega), smul_eq_mul]

lemma dvd_of_mul_eq_zero {x : R} (h : (607 : R) * x = 0) : ∃ s : R, x = 607 * s := by
  have h' : ((607 * x.val : ℕ) : R) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  obtain ⟨s, hs⟩ : 607 ∣ x.val :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 607) (by simpa [Q, pow_two] using h')
  refine ⟨(s : R), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hs]
  push_cast
  rfl

/-- **Relations among the generators.** -/
theorem gen_relation (a : Fin 25 → R) :
    ∑ j, a j • gen j = 0 ↔ (∀ j : Fin 25, (j : ℕ) < 24 → a j = 0) ∧ ∃ s : R, a 24 = 607 * s := by
  constructor
  · intro h
    have hG : Gm.mulVec a = 0 := by
      funext i
      have hc := congrArg (coeff ((i : ℕ) + 26)) h
      rw [map_sum, map_zero] at hc
      simp only [coeff_smul, coeff_gen, smul_eq_mul] at hc
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hc
    have hD : Dm.mulVec a = 0 := by
      rw [← elim_ok, ← Matrix.mulVec_mulVec, hG, Matrix.mulVec_zero]
    have hDi : ∀ i : Fin 25, Dm i i * a i = 0 := by
      intro i
      have := congrFun hD i
      simpa [Matrix.mulVec, dotProduct, Dm, Finset.sum_ite_eq, Finset.mem_univ] using this
    refine ⟨fun j hj => ?_, ?_⟩
    · have := hDi j
      simpa [Dm, hj] using this
    · apply dvd_of_mul_eq_zero
      have h24 := hDi 24
      have hD24 : Dm 24 24 = 607 * (uVal : R) := by simp [Dm]
      rw [hD24] at h24
      calc (607 : R) * a 24 = 607 * (uVal : R) * a 24 * uInv := by
            rw [mul_right_comm _ _ (uInv : R), mul_assoc 607, u_ok, mul_one]
        _ = 0 := by rw [h24, zero_mul]
  · rintro ⟨h0, s, hs⟩
    rw [Finset.sum_eq_single (24 : Fin 25)]
    · rw [hs, show gen 24 = w from rfl, mul_comm, mul_smul, w_torsion, smul_zero]
    · intro j _ hj
      rw [h0 j (by
        have : (j : ℕ) ≠ 24 := fun h => hj (Fin.ext h)
        omega), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **At precision two, `Λ^odd(3, 2)` is generated by `V_0, …, V_23, w`, with
`607 w = 0` its only relation.** Hence `Λ ≅ (ℤ/607²)²⁴ ⊕ ℤ/607`. -/
theorem lam_structure :
    Submodule.span R (Set.range gen) = Lam 607 2 3 ∧
    ∀ a : Fin 25 → R,
      ∑ j, a j • gen j = 0 ↔ (∀ j : Fin 25, (j : ℕ) < 24 → a j = 0) ∧ ∃ s : R, a 24 = 607 * s :=
  ⟨span_gen.trans S_eq_Lam, gen_relation⟩

/-! ### The isomorphism -/

/-- The quotient ring `ℤ/607² ⧸ (607) ≅ ℤ/607`. -/
abbrev Tor : Type := R ⧸ Ideal.span {(607 : R)}

/-- `(x, y) ↦ Σ x_i V_i + y w`. -/
noncomputable def toSeries : ((Fin 24 → R) × Tor) →ₗ[R] PowerSeries R :=
  LinearMap.coprod
    { toFun := fun x => ∑ i, x i • gen i.castSucc
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [mul_smul, Finset.smul_sum] }
    ((Ideal.span {(607 : R)}).liftQ (LinearMap.smulRight LinearMap.id w) (by
      rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
      exact w_torsion))

lemma toSeries_mk (x : Fin 24 → R) (y : R) :
    toSeries (x, Submodule.Quotient.mk y) = ∑ j : Fin 25, (Fin.snoc x y : Fin 25 → R) j • gen j := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

lemma toSeries_mem (z : (Fin 24 → R) × Tor) : toSeries z ∈ Lam 607 2 3 := by
  rw [← (lam_structure).1]
  obtain ⟨x, q⟩ := z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [toSeries_mk]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **`Λ^odd(3, 2) ≅ (ℤ/607²)²⁴ ⊕ ℤ/607` at `ℓ = 607`.** -/
noncomputable def lamEquiv : ((Fin 24 → R) × Tor) ≃ₗ[R] Lam 607 2 3 :=
  LinearEquiv.ofBijective (LinearMap.codRestrict (Lam 607 2 3) toSeries toSeries_mem) (by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, q⟩ hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have h0 : toSeries (x, Submodule.Quotient.mk y) = 0 := congrArg Subtype.val hz
      rw [toSeries_mk] at h0
      obtain ⟨hx, s, hs⟩ := (gen_relation _).mp h0
      rw [show (24 : Fin 25) = Fin.last 24 from rfl, Fin.snoc_last] at hs
      refine Prod.ext (funext fun i => ?_) ?_
      · have := hx i.castSucc (by simp)
        simpa using this
      · change Submodule.Quotient.mk y = 0
        rw [Submodule.Quotient.mk_eq_zero, hs]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · rintro ⟨f, hf⟩
      rw [← (lam_structure).1, Submodule.mem_span_range_iff_exists_fun] at hf
      obtain ⟨c, hc⟩ := hf
      refine ⟨(fun i => c i.castSucc, Submodule.Quotient.mk (c (Fin.last 24))), Subtype.ext ?_⟩
      change toSeries _ = f
      rw [toSeries_mk, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]
      · rw [Fin.snoc_castSucc])

end RamanujanTau.FiniteArithmetic.Rank607Structure
