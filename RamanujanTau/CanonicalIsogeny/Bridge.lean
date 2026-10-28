/-
# From points over `O` to evaluation over `K`

For `ι : O →+* K` continuous with `‖ι r‖ ≤ 1`:
* `ι (pt z f) = evK (map ι f) (ι z)` at topologically nilpotent `z`;
* `‖ι (x +_F y)‖ ≤ max ‖ι x‖ ‖ι y‖` (ultrametric bound for the point addition);
* `[p](x +_F y) = [p]x +_F [p]y` and `[n+1]x = x +_F [n]x` at points;
* with the Weierstrass factorization `[p](T)/T = P·U`: `ι([p] z) = ι z · P(ι z) · U(ι z)`.
-/
import RamanujanTau.CanonicalIsogeny.EvalK

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CanonicalIsogeny
open MvPowerSeries MvPowerSeries.WithPiTopology Lubin

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- `ℕ ≃ (Unit →₀ ℕ)`. -/
noncomputable def unitEquiv : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun d := d ()
  left_inv n := by simp
  right_inv d := Finsupp.ext fun u => by cases u; simp

/-- **`ι` carries point evaluation to `evK`.** -/
theorem ι_pt (ι : O →+* K) (hιc : Continuous ι) {z : O} (hz : IsTopologicallyNilpotent z)
    (f : MvPowerSeries Unit O) :
    ι (pt (fun _ : Unit => z) f) = evK (MvPowerSeries.map ι f) (ι z) := by
  have h := (MvPowerSeries.hasSum_eval₂ (φ := RingHom.id O) continuous_id (hasEvalPt (x := fun _ : Unit => z)
    (fun _ => hz)) f).map ι hιc
  have h2 := (unitEquiv.hasSum_iff).mpr h
  rw [pt, ← h2.tsum_eq, evK]
  refine tsum_congr fun n => ?_
  simp only [Function.comp_apply, unitEquiv, Equiv.coe_fn_mk, RingHom.id_apply, map_mul]
  rw [Finsupp.prod_single_index (by simp), map_pow]
  rfl

variable (F : FormalGroup O)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) O)

/-- **ultrametric bound** for `x +_F y`. -/
theorem norm_padd_le (ι : O →+* K) (hιc : Continuous ι) (hι : ∀ r, ‖ι r‖ ≤ 1) {x y : O}
    (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    ‖ι (padd F x y)‖ ≤ max ‖ι x‖ ‖ι y‖ := by
  have h := (MvPowerSeries.hasSum_eval₂ (φ := RingHom.id O) continuous_id (hasEvalPt (admPt2 hx hy)) Fs).map ι hιc
  rw [padd, pt, ← h.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (le_max_of_le_left (norm_nonneg _)) fun d => ?_
  simp only [Function.comp_apply, RingHom.id_apply]
  by_cases hd : d = 0
  · subst hd
    rw [coeff_zero_eq_constantCoeff_apply, F.zero_constantCoeff, zero_mul, map_zero, norm_zero]
    exact le_max_of_le_left (norm_nonneg _)
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, map_mul, map_mul, norm_mul,
    norm_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_pow, norm_pow]
  have hc := hι (coeff d Fs)
  have hx1 := hι x
  have hy1 := hι y
  have hd' : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra hc'; push Not at hc'
    exact hd (Finsupp.ext fun i => by fin_cases i <;> simp [hc'.1, hc'.2])
  rcases hd' with h0 | h1
  · calc ‖ι (coeff d Fs)‖ * (‖ι x‖ ^ d 0 * ‖ι y‖ ^ d 1) ≤ 1 * (‖ι x‖ * 1) :=
          mul_le_mul hc (mul_le_mul (pow_le_of_le_one (norm_nonneg _) hx1 h0)
            (pow_le_one₀ (norm_nonneg _) hy1) (by positivity) (norm_nonneg _)) (by positivity)
            zero_le_one
      _ ≤ _ := by rw [one_mul, mul_one]; exact le_max_left _ _
  · calc ‖ι (coeff d Fs)‖ * (‖ι x‖ ^ d 0 * ‖ι y‖ ^ d 1) ≤ 1 * (1 * ‖ι y‖) :=
          mul_le_mul hc (mul_le_mul (pow_le_one₀ (norm_nonneg _) hx1)
            (pow_le_of_le_one (norm_nonneg _) hy1 h1) (by positivity) zero_le_one) (by positivity)
            zero_le_one
      _ ≤ _ := by rw [one_mul, one_mul]; exact le_max_right _ _

variable {F}

lemma pt_zero_series {x : O} (hx : IsTopologicallyNilpotent x) :
    pt (fun _ : Unit => x) (0 : MvPowerSeries Unit O) = 0 := by
  rw [← PH_apply (x := fun _ : Unit => x) (fun _ => hx)]; exact map_zero _

/-- `[n+1] x = x +_F [n] x`. -/
lemma pt_nmul_succ {x : O} (hx : IsTopologicallyNilpotent x) (n : ℕ) :
    pt (fun _ : Unit => x) (FGL.nmul F (n + 1)) = padd F x (pt (fun _ : Unit => x) (FGL.nmul F n)) := by
  show pt _ (FGL.ev F FGL.T (FGL.nmul F n)) = _
  rw [← E2_eq_ev FGL.cc_T (FGL.cc_nmul F n), pt_E2 (fun _ => hx) (tn_X ()) (tn_nmul n), pt_X]

/-- **`[p]` is additive on points.** -/
lemma pt_nmul_padd [F.IsComm] (p : ℕ) {x y : O} (hx : IsTopologicallyNilpotent x)
    (hy : IsTopologicallyNilpotent y) :
    pt (fun _ : Unit => padd F x y) (FGL.nmul F p) =
      padd F (pt (fun _ : Unit => x) (FGL.nmul F p)) (pt (fun _ : Unit => y) (FGL.nmul F p)) := by
  have hv := admPt2 hx hy
  have h := congrArg (pt ![x, y]) (nmul_hom (F := F) p)
  rw [pt_E (fun _ => tn_E2X01) hv, pt_E2 hv (tn_nm p 0) (tn_nm p 1), pt_E (fun _ => tn_X 0) hv,
    pt_E (fun _ => tn_X 1) hv] at h
  simp only [pt_E2 hv (tn_X 0) (tn_X 1), pt_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

variable [CompleteSpace K]

/-- **`[p]` at a point through the Weierstrass factorization.** -/
theorem ι_pt_nmul (ι : O →+* K) (hιc : Continuous ι) (hι : ∀ r, ‖ι r‖ ≤ 1) (p : ℕ)
    (P : Polynomial K) (U : PowerSeries K) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : (P : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)))
    {z : O} (hz : IsTopologicallyNilpotent z) (hz1 : ‖ι z‖ < 1) :
    ι (pt (fun _ : Unit => z) (FGL.nmul F p)) = ι z * (P.eval (ι z) * evK U (ι z)) := by
  set h := PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))
  have hmap : (MvPowerSeries.map ι (FGL.nmul F p) : PowerSeries K) = PowerSeries.X * h := by
    ext n
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_X_mul]
      show MvPowerSeries.coeff _ _ = _
      rw [MvPowerSeries.coeff_map, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply,
        FGL.cc_nmul, map_zero]
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
      show MvPowerSeries.coeff _ _ = _
      rw [MvPowerSeries.coeff_map]
  have hX : (PowerSeries.X : PowerSeries K) = ((Polynomial.X : Polynomial K) : PowerSeries K) :=
    (Polynomial.coe_X).symm
  have hh : SN h (ι z) := sn_of_bdd 1 (fun k => by rw [PowerSeries.coeff_mk]; exact hι _) hz1
  rw [ι_pt ι hιc hz, hmap, hX, evK_mul (sn_poly _ _) hh, evK_poly, Polynomial.eval_X, ← hW,
    evK_mul (sn_poly _ _) (sn_of_bdd 1 hU hz1), evK_poly]

end CanonicalIsogeny
