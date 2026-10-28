/-
# Roots of `[p]` and their simplicity

With the Weierstrass factorization `[p](T)/T = P·U` over `K` (`P = ∏ (X − ι rᵢ)`):
* `root_iff`: a point `z` with `‖ι z‖ < 1` is a root of `[p]` iff `z = 0` or `z = rᵢ` for some `i`;
* `injOn_roots`: the roots `rᵢ` with `‖ι rᵢ‖ < 1` are pairwise distinct. Indeed at a root `z`,
  `Ψ(z) · [p]'(z) = p · Ψ([p] z) = p ≠ 0` (`FGL.nmul_invariant`), whereas a double root of `P` would give
  `[p]'(z) = 0` after evaluation in `K`.
-/
import RamanujanTau.CanonicalIsogeny.Bridge
import RamanujanTau.FormalGroupLayer.CharP

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CanonicalIsogeny
open MvPowerSeries MvPowerSeries.WithPiTopology Lubin Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### bounded series -/

/-- bounded coefficients. -/
def Bdd (V : PowerSeries K) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖PowerSeries.coeff k V‖ ≤ C

lemma Bdd.mul {V W : PowerSeries K} (hV : Bdd V) (hW : Bdd W) : Bdd (V * W) := by
  obtain ⟨C, hC, hV⟩ := hV
  obtain ⟨D, hD, hW⟩ := hW
  exact ⟨C * D, by positivity, bdd_mul hC hD hV hW⟩

lemma Bdd.add {V W : PowerSeries K} (hV : Bdd V) (hW : Bdd W) : Bdd (V + W) := by
  obtain ⟨C, hC, hV⟩ := hV
  obtain ⟨D, hD, hW⟩ := hW
  refine ⟨max C D, le_max_of_le_left hC, fun k => ?_⟩
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hV k) (hW k))

lemma Bdd.poly (P : Polynomial K) : Bdd (P : PowerSeries K) := bdd_poly P

lemma Bdd.deriv {V : PowerSeries K} (hV : Bdd V) : Bdd (PowerSeries.derivative K V) := by
  obtain ⟨C, hC, hV⟩ := hV
  refine ⟨C, hC, fun k => ?_⟩
  rw [PowerSeries.coeff_derivative, norm_mul]
  have : ‖((k : K) + 1)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K (k + 1); push_cast at this; exact this
  calc _ ≤ C * 1 := mul_le_mul (hV _) this (norm_nonneg _) hC
    _ = C := mul_one C

lemma Bdd.sn {V : PowerSeries K} (hV : Bdd V) {t : K} (ht : ‖t‖ < 1) : SN V t := by
  obtain ⟨C, -, hV⟩ := hV; exact sn_of_bdd C hV ht

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

/-- `map ι` commutes with the derivative. -/
lemma map_pd (ι : O →+* K) (f : MvPowerSeries Unit O) :
    (MvPowerSeries.map ι (MvPowerSeries.pd () f) : PowerSeries K) =
      PowerSeries.derivative K (MvPowerSeries.map ι f : PowerSeries K) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  show MvPowerSeries.coeff _ _ = MvPowerSeries.coeff _ _ * _
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_pd, map_mul, ← Finsupp.single_add]
  simp

variable {F : FormalGroup O} [F.IsComm]

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) O)

/-- at a root `z` of `[p]`, `[p]'(z) ≠ 0` when `p ≠ 0`. -/
theorem pt_pd_nmul_ne_zero (p : ℕ) (hp : (p : O) ≠ 0) {z : O} (hz : IsTopologicallyNilpotent z)
    (hroot : pt (fun _ : Unit => z) (FGL.nmul F p) = 0) :
    pt (fun _ : Unit => z) (MvPowerSeries.pd () (FGL.nmul F p)) ≠ 0 := by
  have hx : AdmPt (fun _ : Unit => z) := fun _ => hz
  have hΨ : pt (fun _ : Unit => z) (FGL.Ψ F (FGL.nmul F p)) = 1 := by
    rw [FGL.Ψ, pt_subst (FGL.cc_vec2 (FGL.cc_nmul F p) (by simp)) hx]
    have : (fun s => pt (fun _ : Unit => z) ((![FGL.nmul F p, 0] : Fin 2 → MvPowerSeries Unit O) s)) =
        fun _ => 0 := by
      funext s; fin_cases s
      · exact hroot
      · exact pt_zero_series hz
    rw [this, pt_zero, ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pd, zero_add]
    simp [F.lin_coeff_Y]
  have h := congrArg (pt (fun _ : Unit => z)) (FGL.nmul_invariant F p)
  simp only [← PH_apply hx, map_mul, map_natCast] at h
  rw [PH_apply hx, PH_apply hx, PH_apply hx, hΨ, mul_one] at h
  intro h0
  rw [h0, mul_zero] at h
  exact hp h.symm

variable [CompleteSpace K]

/-- **the roots of `[p]` of norm `< 1`** are `0` and the Weierstrass roots. -/
theorem root_iff (ι : O →+* K) (hιc : Continuous ι) (hinj : Function.Injective ι)
    (hι : ∀ r, ‖ι r‖ ≤ 1) (p : ℕ) {κ : Type*} [Fintype κ] (r₀ : κ → O)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C (ι (r₀ i))) : Polynomial K) : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)))
    {z : O} (hz : IsTopologicallyNilpotent z) (hz1 : ‖ι z‖ < 1) :
    pt (fun _ : Unit => z) (FGL.nmul F p) = 0 ↔ z = 0 ∨ ∃ i, z = r₀ i := by
  have e := ι_pt_nmul ι hιc hι p _ U hU hW hz hz1
  have hu : evK U (ι z) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_evK_unit hU0 hU hz1]; exact one_ne_zero
  rw [← map_eq_zero_iff ι hinj, e, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, hu, or_false,
    map_eq_zero_iff ι hinj, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero,
    hinj.eq_iff]

/-- **simplicity**: the Weierstrass roots of norm `< 1` are pairwise distinct. -/
theorem injOn_roots (ι : O →+* K) (hιc : Continuous ι) (hinj : Function.Injective ι)
    (hι : ∀ r, ‖ι r‖ ≤ 1) (htn : ∀ x, ‖ι x‖ < 1 → IsTopologicallyNilpotent x)
    (p : ℕ) (hp : (p : K) ≠ 0) {κ : Type*} [Fintype κ] [DecidableEq κ] (r₀ : κ → O)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C (ι (r₀ i))) : Polynomial K) : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))) :
    Set.InjOn r₀ {i | ‖ι (r₀ i)‖ < 1} := by
  intro i hi j _ hij
  by_contra hne
  have hi1 : ‖ι (r₀ i)‖ < 1 := hi
  set z := r₀ i with hzdef
  set t := ι z
  have hz := htn z hi1
  have hroot : pt (fun _ : Unit => z) (FGL.nmul F p) = 0 :=
    (root_iff ι hιc hinj hι p r₀ U hU0 hU hW hz hi1).mpr (Or.inr ⟨i, rfl⟩)
  have hpO : (p : O) ≠ 0 := fun h => hp (by rw [← map_natCast ι, h, map_zero])
  have hA := pt_pd_nmul_ne_zero p hpO hz hroot
  apply hA
  apply hinj
  rw [map_zero, ι_pt ι hιc hz, map_pd]
  -- factor `P = (X − t)² Q`
  set f : κ → Polynomial K := fun k => Polynomial.X - Polynomial.C (ι (r₀ k))
  set Q := ∏ k ∈ (univ.erase i).erase j, f k
  have hji : j ∈ univ.erase i := mem_erase.mpr ⟨Ne.symm hne, mem_univ _⟩
  have hP : ∏ k, f k = (Polynomial.X - Polynomial.C t) ^ 2 * Q := by
    rw [← mul_prod_erase univ f (mem_univ i), ← mul_prod_erase _ f hji]
    simp only [f, ← hij, ← hzdef]; ring
  set A : PowerSeries K := ((Polynomial.X - Polynomial.C t : Polynomial K) : PowerSeries K)
  set M : PowerSeries K := PowerSeries.X * (Q : PowerSeries K) * U
  have hmap : (MvPowerSeries.map ι (FGL.nmul F p) : PowerSeries K) = A ^ 2 * M := by
    have h1 : (MvPowerSeries.map ι (FGL.nmul F p) : PowerSeries K) =
        PowerSeries.X * PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)) := by
      ext n
      rcases n with _ | n
      · rw [PowerSeries.coeff_zero_X_mul]
        show MvPowerSeries.coeff _ _ = _
        rw [MvPowerSeries.coeff_map, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply,
          FGL.cc_nmul, map_zero]
      · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
        show MvPowerSeries.coeff _ _ = _
        rw [MvPowerSeries.coeff_map]
    rw [h1, ← hW, hP, Polynomial.coe_mul, Polynomial.coe_pow]
    simp only [A, M]; ring
  have hDA : PowerSeries.derivative K A = 1 := by
    simp only [A, PowerSeries.derivative_coe, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, Polynomial.coe_one]
  have hD : PowerSeries.derivative K (A ^ 2 * M) =
      A * (A * PowerSeries.derivative K M + M + M) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDA]
    simp only [smul_eq_mul, nsmul_eq_mul]; push_cast; ring
  have hMb : Bdd M := by
    refine ((Bdd.poly Polynomial.X).mul (Bdd.poly Q)).mul ⟨1, zero_le_one, hU⟩ |> fun h => ?_
    simpa [M, Polynomial.coe_X] using h
  have hWb : Bdd (A * PowerSeries.derivative K M + M + M) :=
    (((Bdd.poly _).mul hMb.deriv).add hMb).add hMb
  have ht1 : ‖t‖ < 1 := hi1
  rw [hmap, hD, evK_mul (sn_poly _ _) (hWb.sn ht1), evK_poly]
  simp [t]

end CanonicalIsogeny
