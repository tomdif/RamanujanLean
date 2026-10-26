/-
# Realizing formal q-products as holomorphic functions on the unit disc

`Realizes f F` says that the holomorphic function `f` on the unit disc is the evaluation of the formal power series
`F ∈ ℤ⟦q⟧`: `f` is a locally uniform limit of integer polynomials `p_N` whose coefficients stabilize to those of
`F`. The class is closed under `+`, `−`, `·`, constants and `q`, and contains every product
`∏_{k≥0}(1 − q^{b+ak})` (`Pinf b a`). Two realizations of the same formal series agree on the disc
(`Realizes.eqOn`), by Weierstrass (`tlu_iteratedDeriv`) and Taylor's theorem: every formal identity among such
products is a numerical identity for `|q| < 1`.
-/
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.RankTheta
import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit false

namespace Realize
open Complex Filter Metric Function Set
open scoped Topology Nat

/-- evaluation of an integer polynomial at a complex point. -/
noncomputable def ev (p : Polynomial ℤ) (z : ℂ) : ℂ := (p.map (Int.castRingHom ℂ)).eval z

/-- `f` is the holomorphic evaluation of `F` on the unit disc. -/
structure Realizes (f : ℂ → ℂ) (F : PowerSeries ℤ) : Prop where
  diff : DifferentiableOn ℂ f (ball 0 1)
  approx : ∃ p : ℕ → Polynomial ℤ, TendstoLocallyUniformlyOn (fun N => ev (p N)) f atTop (ball 0 1) ∧
    ∀ K, ∀ᶠ N in atTop, (PowerSeries.X : PowerSeries ℤ) ^ K ∣ F - (p N : PowerSeries ℤ)

lemma Realizes.continuousOn {f : ℂ → ℂ} {F : PowerSeries ℤ} (h : Realizes f F) : ContinuousOn f (ball 0 1) :=
  h.diff.continuousOn

lemma realizes_const (c : ℤ) : Realizes (fun _ => (c : ℂ)) (PowerSeries.C c) :=
  ⟨differentiableOn_const _, fun _ => Polynomial.C c,
    by convert RamanujanTau.DiscriminantBridge.tlu_const (U := ball (0 : ℂ) 1) (fun _ => (c : ℂ)) using 1
       funext N z; simp [ev],
    fun K => Eventually.of_forall fun N => by rw [Polynomial.coe_C, sub_self]; exact dvd_zero _⟩

lemma realizes_X : Realizes (fun z => z) PowerSeries.X :=
  ⟨differentiableOn_id, fun _ => Polynomial.X,
    by convert RamanujanTau.DiscriminantBridge.tlu_const (U := ball (0 : ℂ) 1) (fun z => z) using 1
       funext N z; simp [ev],
    fun K => Eventually.of_forall fun N => by simp⟩

lemma Realizes.add {f g : ℂ → ℂ} {F G : PowerSeries ℤ} (hf : Realizes f F) (hg : Realizes g G) :
    Realizes (fun z => f z + g z) (F + G) := by
  obtain ⟨p, hp, hpc⟩ := hf.approx
  obtain ⟨r, hr, hrc⟩ := hg.approx
  refine ⟨hf.diff.add hg.diff, fun N => p N + r N, ?_, fun K => ?_⟩
  · convert hp.add hr using 1; funext N z; simp [ev]
  · filter_upwards [hpc K, hrc K] with N h1 h2
    rw [Polynomial.coe_add, show F + G - (↑(p N) + ↑(r N)) = (F - ↑(p N)) + (G - ↑(r N)) by ring]
    exact dvd_add h1 h2

lemma Realizes.neg {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) : Realizes (fun z => -f z) (-F) := by
  obtain ⟨p, hp, hpc⟩ := hf.approx
  refine ⟨hf.diff.neg, fun N => -p N, ?_, fun K => ?_⟩
  · convert hp.neg using 1; funext N z; simp [ev]
  · filter_upwards [hpc K] with N h1
    rw [Polynomial.coe_neg, show -F - -(p N : PowerSeries ℤ) = -(F - ↑(p N)) by ring]
    exact h1.neg_right

lemma Realizes.sub {f g : ℂ → ℂ} {F G : PowerSeries ℤ} (hf : Realizes f F) (hg : Realizes g G) :
    Realizes (fun z => f z - g z) (F - G) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Realizes.mul {f g : ℂ → ℂ} {F G : PowerSeries ℤ} (hf : Realizes f F) (hg : Realizes g G) :
    Realizes (fun z => f z * g z) (F * G) := by
  obtain ⟨p, hp, hpc⟩ := hf.approx
  obtain ⟨r, hr, hrc⟩ := hg.approx
  refine ⟨hf.diff.mul hg.diff, fun N => p N * r N, ?_, fun K => ?_⟩
  · convert hp.mul₀ hr hf.continuousOn hg.continuousOn using 1; funext N z; simp [ev]
  · filter_upwards [hpc K, hrc K] with N h1 h2
    rw [Polynomial.coe_mul, show F * G - ↑(p N) * ↑(r N) = (F - ↑(p N)) * G + ↑(p N) * (G - ↑(r N)) by ring]
    exact dvd_add (h1.mul_right _) (h2.mul_left _)

lemma Realizes.pow {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) (k : ℕ) :
    Realizes (fun z => f z ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using realizes_const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

lemma Realizes.congr {f g : ℂ → ℂ} {F G : PowerSeries ℤ} (hf : Realizes f F) (hfg : ∀ z, f z = g z)
    (hFG : F = G) : Realizes g G := by
  have : f = g := funext hfg
  subst this hFG; exact hf

/-! ### the products `∏_{k≥0}(1 − q^{b+ak})` -/

lemma one_le_add_mul {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (n : ℕ) : n + 1 ≤ b + a * n := by nlinarith

lemma multipliableLocallyUniformlyOn_P (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) :
    MultipliableLocallyUniformlyOn (fun n (q : ℂ) => 1 - q ^ (b + a * n)) (ball (0 : ℂ) 1) := by
  use fun q => ∏' n, (1 - q ^ (b + a * n))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
      (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
    have hq1 : ‖q₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hK hq₀
    refine ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq1)
      ).hasProdUniformlyOn_nat_one_add hcK (.of_forall fun n x hx ↦ ?_) (fun _ ↦ by fun_prop)
    rw [norm_neg, norm_pow]
    calc ‖x‖ ^ (b + a * n) ≤ ‖x‖ ^ (n + 1) :=
          pow_le_pow_of_le_one (norm_nonneg _) ((HB x hx).trans hq1.le) (one_le_add_mul hb ha n)
      _ ≤ ‖q₀‖ ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) (HB x hx) _

/-- `∏_{k≥0}(1 − q^{b+ak})` as a function. -/
noncomputable def Pfun (b a : ℕ) (q : ℂ) : ℂ := ∏' n, (1 - q ^ (b + a * n))

lemma realizes_Pinf (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : Realizes (Pfun b a) (RankProof.Pinf b a) := by
  have hM := multipliableLocallyUniformlyOn_P b a hb ha
  have hT := hM.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  refine ⟨hM.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ ↦ by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ ↦ by fun_prop)) isOpen_ball,
    fun N => ∏ i ∈ Finset.range N, (1 - Polynomial.X ^ (b + a * i)), ?_, fun K => ?_⟩
  · convert hT using 1
    funext N q
    simp [ev, Polynomial.map_prod, Polynomial.eval_prod]
  · filter_upwards [eventually_ge_atTop K] with N hN
    have h := RankProof.X_pow_dvd_Pinf_sub b a hb ha N
    have hc : ((∏ i ∈ Finset.range N, (1 - Polynomial.X ^ (b + a * i)) : Polynomial ℤ) : PowerSeries ℤ)
        = RankProof.Pfin b a N := by
      rw [RankProof.Pfin, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
      simp
    rw [hc]
    exact (pow_dvd_pow _ (by omega)).trans h

/-! ### uniqueness -/

lemma Realizes.iteratedDeriv_zero {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) (n : ℕ) :
    iteratedDeriv n f 0 = n ! * ((PowerSeries.coeff n F : ℤ) : ℂ) := by
  obtain ⟨p, hp, hpc⟩ := hf.approx
  have hlim := (RamanujanTau.DiscriminantBridge.tlu_iteratedDeriv isOpen_ball n hp
    (fun N => (Polynomial.differentiable _).differentiableOn)).tendsto_at (mem_ball_self one_pos)
  have hconst : ∀ᶠ N in atTop, iteratedDeriv n (ev (p N)) 0 = n ! * ((PowerSeries.coeff n F : ℤ) : ℂ) := by
    filter_upwards [hpc (n + 1)] with N hN
    have h0 := (PowerSeries.X_pow_dvd_iff.mp hN) n (by omega)
    rw [map_sub, sub_eq_zero, Polynomial.coeff_coe] at h0
    rw [show ev (p N) = fun q => ((p N).map (Int.castRingHom ℂ)).eval q from rfl,
      RamanujanTau.DiscriminantBridge.iteratedDeriv_poly_zero, Polynomial.coeff_map, ← h0, eq_intCast]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hconst))

/-- **the evaluation**: `f z = Σ_n [qⁿ]F · zⁿ` on the unit disc. -/
lemma Realizes.hasSum {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n => ((PowerSeries.coeff n F : ℤ) : ℂ) * z ^ n) (f z) := by
  have H := Complex.hasSum_taylorSeries_on_ball hf.diff hz
  convert H using 1
  funext n
  rw [hf.iteratedDeriv_zero n, sub_zero, smul_eq_mul, smul_eq_mul]
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **two realizations of the same formal series agree on the unit disc.** -/
theorem Realizes.eq {f g : ℂ → ℂ} {F G : PowerSeries ℤ} (hf : Realizes f F) (hg : Realizes g G) (hFG : F = G)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : f z = g z := by
  subst hFG
  exact (hf.hasSum hz).unique (hg.hasSum hz)

end Realize
