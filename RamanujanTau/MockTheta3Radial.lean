/-
# Ramanujan's deathbed claim at `q → −1`

In his last letter to Hardy (12 January 1920) Ramanujan asserted that, as `q` tends radially to an even-order root
of unity, the mock theta function `f(q) = Σ q^{n²}/(−q;q)_n²` differs from the theta-type function
  `b(q) = (1−q)(1−q³)(1−q⁵)⋯(1 − 2q + 2q⁴ − 2q⁹ + ⋯)`
by a bounded amount (with sign `(−1)^k` at a root of order `2k`). At `q → −1` (`k = 1`):

  **`f(q) + b(q) → 4`  as `q → −1` radially** (so in particular it stays bounded),

although `f(q)` and `b(q)` each blow up there.

Proof: Watson's identity `f(q) + b(q) = 2φ(−q)` (`MockTheta3.Watson3.watson_W1`) holds as holomorphic functions on
the disc (`Taylor`), and `φ(t) = Σ t^{n²}/(−t²;t²)_n` has terms `≤ 2⁻ⁿ` on `[0,1]` with limit `2⁻ⁿ` at `t = 1`,
so `φ(t) → 2` by dominated convergence (Tannery).
-/
import RamanujanTau.MockTheta3Analytic
import RamanujanTau.MockTheta3Watson

set_option autoImplicit false

namespace MockTheta3.Radial
open Complex Filter Metric Finset Taylor
open scoped Topology

local notation "ψC" => MockTheta5.JTP.ψC

/-! ### the polynomials and the holomorphic functions -/

noncomputable def P1 (n : ℕ) : Polynomial ℤ := ∏ i ∈ range n, (1 + Polynomial.X ^ (i + 1))
noncomputable def P2 (n : ℕ) : Polynomial ℤ := ∏ i ∈ range n, (1 + Polynomial.X ^ (2 + 2 * i))
noncomputable def P0 (_ : ℕ) : Polynomial ℤ := 1

/-- `f(q) = Σ q^{n²}/(−q;q)_n²`. -/
noncomputable def fA (z : ℂ) : ℂ := ∑' n, ((1 : ℤ) : ℂ) * z ^ (n ^ 2) * (((P1 n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ 2
/-- `φ(−q) = Σ (−1)ⁿ q^{n²}/(−q²;q²)_n`. -/
noncomputable def gA (z : ℂ) : ℂ :=
  ∑' n, (((-1) ^ n : ℤ) : ℂ) * z ^ (n ^ 2) * (((P2 n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ 1
/-- `Σ_{n≥0} (−1)ⁿ q^{n²}`. -/
noncomputable def θA (z : ℂ) : ℂ :=
  ∑' n, (((-1) ^ n : ℤ) : ℂ) * z ^ (n ^ 2) * (((P0 n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ 0
/-- Ramanujan's `b(q) = (q;q²)_∞ (1 − 2q + 2q⁴ − ⋯)`. -/
noncomputable def bA (z : ℂ) : ℂ := Realize.Pfun 1 2 z * (2 * θA z - 1)

lemma fA_eq (z : ℂ) : fA z = ∑' n, z ^ (n ^ 2) / (∏ i ∈ range n, (1 + z ^ (i + 1))) ^ 2 := by
  simp [fA, P1, Polynomial.map_prod, Polynomial.eval_prod, div_eq_mul_inv]

lemma gA_eq (z : ℂ) : gA z = ∑' n, (-1) ^ n * z ^ (n ^ 2) / ∏ i ∈ range n, (1 + z ^ (2 + 2 * i)) := by
  simp [gA, P2, Polynomial.map_prod, Polynomial.eval_prod, div_eq_mul_inv]

lemma θA_eq (z : ℂ) : θA z = ∑' n, (-1) ^ n * z ^ (n ^ 2) := by simp [θA, P0]

/-! ### hypotheses of `T_series` -/

lemma norm_one_add_ge {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < 1) (e : ℕ) (he : 1 ≤ e) :
    1 - r ≤ ‖1 + z ^ e‖ := by
  have h1 : ‖z ^ e‖ ≤ r := by
    rw [norm_pow]
    calc ‖z‖ ^ e ≤ ‖z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hz.trans hr.le) he
      _ ≤ r := by simpa using hz
  have := norm_sub_norm_le (1 : ℂ) (-(z ^ e))
  rw [norm_one, norm_neg, sub_neg_eq_add] at this
  linarith

lemma prod_bound {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1) (e : ℕ → ℕ) (he : ∀ i, 1 ≤ e i) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ r) : (1 - r) ^ n ≤ ‖∏ i ∈ range n, (1 + z ^ e i)‖ := by
  rw [norm_prod]
  calc (1 - r) ^ n = ∏ _i ∈ range n, (1 - r) := by simp
    _ ≤ ∏ i ∈ range n, ‖1 + z ^ e i‖ :=
        Finset.prod_le_prod (fun _ _ => by linarith) (fun i _ => norm_one_add_ge hz hr _ (he i))

lemma eval_prod_one_add (e : ℕ → ℕ) (n : ℕ) (z : ℂ) :
    ((∏ i ∈ range n, (1 + Polynomial.X ^ e i) : Polynomial ℤ).map (Int.castRingHom ℂ)).eval z
      = ∏ i ∈ range n, (1 + z ^ e i) := by
  simp [Polynomial.map_prod, Polynomial.eval_prod]

lemma hyps (e : ℕ → ℕ) (he : ∀ i, 1 ≤ e i) :
    (∀ n, PowerSeries.constantCoeff (((∏ i ∈ range n, (1 + Polynomial.X ^ e i) : Polynomial ℤ)) : PowerSeries ℤ) = 1) ∧
    (∀ n z, z ∈ ball (0 : ℂ) 1 → ((∏ i ∈ range n, (1 + Polynomial.X ^ e i) : Polynomial ℤ).map
        (Int.castRingHom ℂ)).eval z ≠ 0) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 → ∃ c > (0 : ℝ), ∀ n z, ‖z‖ ≤ r →
        c ^ n ≤ ‖((∏ i ∈ range n, (1 + Polynomial.X ^ e i) : Polynomial ℤ).map (Int.castRingHom ℂ)).eval z‖) := by
  refine ⟨fun n => ?_, fun n z hz => ?_, fun r h0 h1 => ⟨1 - r, by linarith, fun n z hz => ?_⟩⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    simp [zero_pow (by have := he i; omega : e i ≠ 0)]
  · rw [eval_prod_one_add]
    have hz' : ‖z‖ < 1 := by simpa using hz
    have := prod_bound (norm_nonneg z) hz' e he n le_rfl
    intro h0; rw [h0, norm_zero] at this
    exact absurd this (not_le.mpr (pow_pos (by linarith) n))
  · rw [eval_prod_one_add]; exact prod_bound h0 h1 e he n hz

lemma hyps0 :
    (∀ n, PowerSeries.constantCoeff ((P0 n : Polynomial ℤ) : PowerSeries ℤ) = 1) ∧
    (∀ n z, z ∈ ball (0 : ℂ) 1 → ((P0 n).map (Int.castRingHom ℂ)).eval z ≠ 0) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 → ∃ c > (0 : ℝ), ∀ n z, ‖z‖ ≤ r → c ^ n ≤ ‖((P0 n).map (Int.castRingHom ℂ)).eval z‖) :=
  ⟨fun n => by simp [P0], fun n z _ => by simp [P0], fun r _ _ => ⟨1, one_pos, fun n z _ => by simp [P0]⟩⟩

lemma sgn_le (n : ℕ) : ‖((((-1) ^ n : ℤ)) : ℂ)‖ ≤ 1 := by simp

lemma one_le : ∀ _ : ℕ, ‖(((1 : ℤ)) : ℂ)‖ ≤ 1 := fun _ => by simp

lemma he1 : ∀ i : ℕ, 1 ≤ i + 1 := fun i => by omega
lemma he2 : ∀ i : ℕ, 1 ≤ 2 + 2 * i := fun i => by omega

theorem fA_T : Hol fA ∧ T fA = ψC (PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C (1 : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P1 n : Polynomial ℤ) : PowerSeries ℤ) ^ 2)) := by
  obtain ⟨h1, h2, h3⟩ := hyps (fun i => i + 1) he1
  exact T_series (fun _ => 1) 2 P1 h1 h2 h3 one_le

theorem gA_T : Hol gA ∧ T gA = ψC (PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P2 n : Polynomial ℤ) : PowerSeries ℤ) ^ 1)) := by
  obtain ⟨h1, h2, h3⟩ := hyps (fun i => 2 + 2 * i) he2
  exact T_series (fun n => (-1) ^ n) 1 P2 h1 h2 h3 sgn_le

theorem θA_T : Hol θA ∧ T θA = ψC (PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P0 n : Polynomial ℤ) : PowerSeries ℤ) ^ 0)) := by
  obtain ⟨h1, h2, h3⟩ := hyps0
  exact T_series (fun n => (-1) ^ n) 0 P0 h1 h2 h3 sgn_le

/-! ### matching the formal series of `MockTheta3Watson` -/

open Watson in
lemma coe_prod_one_add (e : ℕ → ℕ) (n : ℕ) :
    (((∏ i ∈ range n, (1 + Polynomial.X ^ e i) : Polynomial ℤ)) : PowerSeries ℤ)
      = ∏ i ∈ range n, (1 + PowerSeries.X ^ e i) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]; simp

lemma coe_P1 (n : ℕ) : ((P1 n : Polynomial ℤ) : PowerSeries ℤ) = Watson3.NP 1 1 n := by
  rw [P1, coe_prod_one_add (fun i => i + 1)]
  simp [Watson.FP]; refine Finset.prod_congr rfl fun i _ => by ring_nf

lemma coe_P2 (n : ℕ) : ((P2 n : Polynomial ℤ) : PowerSeries ℤ) = Watson3.NP 2 2 n := by
  rw [P2, coe_prod_one_add (fun i => 2 + 2 * i)]
  simp [Watson.FP]

lemma osum_eq_mk {f : ℕ → PowerSeries ℤ} (h : ∀ n k, k < n → PowerSeries.coeff k (f n) = 0) :
    Watson.osum f = PowerSeries.mk fun k => PowerSeries.coeff k (∑ n ∈ range (k + 1), f n) := by
  ext k
  rw [Watson.coeff_osum, PowerSeries.coeff_mk, map_sum]
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  simp only [Function.mem_support, coe_range, Set.mem_Iio] at hn ⊢
  by_contra hc; exact hn (h n k (by omega))

lemma F1_eq : Watson3.F 1 = PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C (1 : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P1 n : Polynomial ℤ) : PowerSeries ℤ) ^ 2) := by
  rw [Watson3.F, osum_eq_mk fun n k hk => by
    rw [Watson3.tF, mul_assoc]; exact Watson3.coeff_Xpow_mul_zero (by nlinarith [Nat.zero_le (n * (n - 1))]) _]
  congr 1; funext m; congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Watson3.tF, coe_P1, show 1 * n + n * (n - 1) = n ^ 2 by cases n <;> simp <;> ring]
  simp; ring

lemma A1_eq : Watson3.A 1 = PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P2 n : Polynomial ℤ) : PowerSeries ℤ) ^ 1) := by
  rw [Watson3.A, osum_eq_mk fun n k hk => by
    rw [Watson3.uA, mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc]
    exact Watson3.coeff_Xpow_mul_zero (by nlinarith) _]
  congr 1; funext m; congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Watson3.uA, coe_P2]; simp

lemma θ_eq : Watson.osum (fun n => (-1 : PowerSeries ℤ) ^ n * PowerSeries.X ^ (n ^ 2)) =
    PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
      PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P0 n : Polynomial ℤ) : PowerSeries ℤ) ^ 0) := by
  rw [osum_eq_mk fun n k hk => by rw [mul_comm]; exact Watson3.coeff_Xpow_mul_zero (by nlinarith) _]
  congr 1; funext m; congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

lemma IP_eq : Watson.IP 1 1 2 = RankProof.Pinf 1 2 := by
  ext k; simp [Watson.IP, RankProof.Pinf, Watson.FP, RankProof.Pfin]

lemma Pfun_T : T (Realize.Pfun 1 2) = ψC (RankProof.Pinf 1 2) := by
  ext n
  rw [coeff_T, (Realize.realizes_Pinf 1 2 le_rfl (by norm_num)).iteratedDeriv_zero n]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [show ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl, PowerSeries.coeff_map]
  field_simp; simp

lemma bA_hol : Hol bA :=
  (Realize.realizes_Pinf 1 2 le_rfl (by norm_num)).diff.mul
    (((differentiableOn_const _).mul θA_T.1).sub (differentiableOn_const _))

lemma bA_T : T bA = ψC Watson3.bR := by
  have hP : Hol (Realize.Pfun 1 2) := (Realize.realizes_Pinf 1 2 le_rfl (by norm_num)).diff
  have h2 : Hol (fun z => 2 * θA z) := (differentiableOn_const _).mul θA_T.1
  have h3 : Hol (fun z => 2 * θA z - 1) := h2.sub (differentiableOn_const _)
  unfold bA
  rw [T_mul hP h3, T_sub (f := fun z => 2 * θA z) (g := fun _ => (1 : ℂ)) h2 (differentiableOn_const _),
    T_mul (f := fun _ => (2 : ℂ)) (differentiableOn_const _) θA_T.1, T_const, T_const, θA_T.2, ← θ_eq, Pfun_T,
    Watson3.bR, Watson3.Θ, IP_eq]
  simp [map_mul, map_sub, map_ofNat]

/-- **Watson's identity on the disc**: `f(q) + b(q) = 2φ(−q)` for `|q| < 1`. -/
theorem watson_disc {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : fA z + bA z = 2 * gA z := by
  have hf := fA_T
  have hg := gA_T
  have hW := Watson3.watson_W1
  refine eq_of_T (f := fun z => fA z + bA z) (g := fun z => 2 * gA z) (hf.1.add bA_hol)
    ((differentiableOn_const _).mul hg.1) ?_ hz
  rw [T_add hf.1 bA_hol, T_mul (f := fun _ => (2 : ℂ)) (differentiableOn_const _) hg.1, T_const, hf.2, hg.2,
    bA_T, ← F1_eq, ← A1_eq, ← hW]
  simp [map_sub, map_mul, map_ofNat]

/-! ### the radial limit -/

/-- the real terms of `φ(t)`. -/
noncomputable def u (t : ℝ) (n : ℕ) : ℝ := t ^ (n ^ 2) / ∏ i ∈ range n, (1 + t ^ (2 + 2 * i))

lemma pow_sq_eq_prod (t : ℝ) (n : ℕ) : t ^ (n ^ 2) = ∏ i ∈ range n, t ^ (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ← ih, ← pow_add]; congr 1; ring

lemma factor_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (i : ℕ) : t ^ (2 * i + 1) / (1 + t ^ (2 + 2 * i)) ≤ 1 / 2 := by
  have hp : 0 < 1 + t ^ (2 + 2 * i) := by positivity
  rw [div_le_iff₀ hp]
  have ha : t ^ (2 * i + 1) ≤ t := by simpa using pow_le_pow_of_le_one h0 h1 (by omega : 1 ≤ 2 * i + 1)
  have hb : t ^ (2 + 2 * i) = t ^ (2 * i + 1) * t := by rw [← pow_succ]; ring_nf
  rw [hb]
  nlinarith [pow_nonneg h0 (2 * i + 1), sq_nonneg (1 - t)]

lemma u_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (n : ℕ) : u t n ≤ (1 / 2) ^ n := by
  rw [u, pow_sq_eq_prod, ← prod_div_distrib]
  calc ∏ i ∈ range n, t ^ (2 * i + 1) / (1 + t ^ (2 + 2 * i)) ≤ ∏ _i ∈ range n, (1 / 2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => factor_le h0 h1 i)
    _ = (1 / 2) ^ n := by simp

lemma u_nonneg {t : ℝ} (h0 : 0 ≤ t) (n : ℕ) : 0 ≤ u t n := by rw [u]; positivity

lemma gA_neg {t : ℝ} : gA (-(t : ℂ)) = ∑' n, ((u t n : ℝ) : ℂ) := by
  rw [gA_eq]
  congr 1; funext n
  rw [u]; push_cast
  have e1 : ∀ i : ℕ, (-(t : ℂ)) ^ (2 + 2 * i) = (t : ℂ) ^ (2 + 2 * i) := fun i =>
    Even.neg_pow ⟨1 + i, by ring⟩ _
  simp only [e1]
  have e2 : (-1 : ℂ) ^ n * (-(t : ℂ)) ^ (n ^ 2) = (t : ℂ) ^ (n ^ 2) := by
    rw [neg_pow (t : ℂ), ← mul_assoc, ← pow_add, Even.neg_one_pow (by
      rw [show n + n ^ 2 = n * (n + 1) by ring]; exact Nat.even_mul_succ_self n), one_mul]
  rw [e2]

lemma u_tendsto (n : ℕ) : Tendsto (fun t : ℝ => ((u t n : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) := by
  have hc : ContinuousAt (fun t : ℝ => u t n) 1 := by
    unfold u
    refine (continuous_pow _).continuousAt.div (continuous_finsetProd _ fun i _ => by fun_prop).continuousAt ?_
    exact (Finset.prod_pos fun i _ => by positivity).ne'
  have h1 : u 1 n = (1 / 2) ^ n := by simp [u]; norm_num
  rw [← h1]
  exact (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left nhdsWithin_le_nhds

/-- **Ramanujan's claim (last letter to Hardy, 1920), at `q → −1`**: as `q → −1` radially,
`f(q) + b(q) → 4`; in particular `f(q) − (−1)¹ b(q)` stays bounded although `f` and `b` each blow up. -/
theorem ramanujan_radial_limit :
    Tendsto (fun t : ℝ => fA (-(t : ℂ)) + bA (-(t : ℂ))) (𝓝[<] 1) (𝓝 4) := by
  have hev : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t ∧ t < 1 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)) fun t ht => ht
  have hT : Tendsto (fun t : ℝ => ∑' n, ((u t n : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 (∑' n, (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) u_tendsto ?_
    filter_upwards [hev] with t ht
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (u_nonneg ht.1.le n)]
    exact u_le ht.1.le ht.2.le n
  have hs : ∑' n, (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_tsum, tsum_geometric_two]; norm_num
  rw [hs] at hT
  have h4 : (4 : ℂ) = 2 * 2 := by norm_num
  rw [h4]
  refine (hT.const_mul 2).congr' ?_
  filter_upwards [hev] with t ht
  have hz : (-(t : ℂ)) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
  rw [watson_disc hz, gA_neg]

end MockTheta3.Radial
