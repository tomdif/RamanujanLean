/-
# Height two passes to Lubin quotients (Weierstrass degrees multiply)

Reduce modulo `𝔪 = {‖x‖ < 1}` (a prime ideal of `𝒪`). Over the domain `𝒪/𝔪` the order of a power
series is multiplicative under composition (`lowOrd_subst`). For a finite subgroup `C` of order `p`,
`π = pis C ≡ T^p · unit`, `[p]_F ≡ T^{p²} · unit` (height two), and `[p]_G ∘ π = π ∘ [p]_F` for
`G = F/C` (`hom_nmul`). Comparing orders, `[p]_G ≡ T^{p²} · unit`, i.e.

  `‖coeff_{p²} [p]_G‖ = 1` and `‖coeff_p [p]_G‖ < 1` (`quot_height`).
-/
import RamanujanTau.QuotientHasse.Torsion

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotientHasse
open MvPowerSeries CanonicalIsogeny WeierstrassSupply Lubin

/-! ### order of a composite over a domain -/
section Order
variable {R : Type*} [CommRing R] [IsDomain R]

/-- `f` has order exactly `n`. -/
def LowOrd (f : PowerSeries R) (n : ℕ) : Prop :=
  (∀ k < n, PowerSeries.coeff k f = 0) ∧ PowerSeries.coeff n f ≠ 0

lemma LowOrd.unique {f : PowerSeries R} {a b : ℕ} (ha : LowOrd f a) (hb : LowOrd f b) : a = b := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact ha.2 (hb.1 a h)
  · exact hb.2 (ha.1 b h)

lemma LowOrd.factor {f : PowerSeries R} {n : ℕ} (hf : LowOrd f n) :
    ∃ u : PowerSeries R, f = PowerSeries.X ^ n * u ∧ PowerSeries.constantCoeff u ≠ 0 := by
  obtain ⟨u, hu⟩ := PowerSeries.X_pow_dvd_iff.mpr hf.1
  refine ⟨u, hu, ?_⟩
  have := hf.2
  rwa [hu, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at this

lemma lowOrd_X_pow_mul {V : PowerSeries R} (n : ℕ) (hV : PowerSeries.constantCoeff V ≠ 0) :
    LowOrd (PowerSeries.X ^ n * V) n := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · rwa [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma LowOrd.cc_zero {g : PowerSeries R} {n : ℕ} (hg : LowOrd g n) (hn : 1 ≤ n) :
    MvPowerSeries.constantCoeff g = 0 := by
  have := hg.1 0 (by omega)
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this

/-- **order is multiplicative under composition**. -/
theorem lowOrd_subst {f g : PowerSeries R} {m n : ℕ} (hf : LowOrd f m) (hg : LowOrd g n)
    (hn : 1 ≤ n) : LowOrd (subst (fun _ : Unit => g) f : PowerSeries R) (m * n) := by
  obtain ⟨u, rfl, hu⟩ := hf.factor
  obtain ⟨w, hgw, hw⟩ := hg.factor
  have h0 : ∀ s : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => g) s) = 0 :=
    fun _ => hg.cc_zero hn
  have hs := FGL.hs h0
  have hX : subst (fun _ : Unit => g) (PowerSeries.X : PowerSeries R) = g := FGL.sX _ h0 ()
  rw [subst_mul hs, subst_pow hs, hX]
  have hgm : g ^ m = PowerSeries.X ^ (m * n) * w ^ m := by
    rw [hgw, mul_pow, ← pow_mul, mul_comm n m]
  rw [hgm, mul_assoc]
  refine lowOrd_X_pow_mul _ ?_
  change MvPowerSeries.constantCoeff (w ^ m * subst (fun _ : Unit => g) u) ≠ 0
  rw [map_mul, map_pow, FGL.cc_subst _ h0 u]
  exact mul_ne_zero (pow_ne_zero _ hw) hu

end Order

/-! ### the generic homomorphism identity `f ∘ [n]_F = [n]_G ∘ f` -/
section Hom
variable {R : Type*} [CommRing R]

theorem hom_nmul (F G : FormalGroup R) (f : MvPowerSeries Unit R) (hf : constantCoeff f = 0)
    (hhom : subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
      FGL.ev G (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f)) (n : ℕ) :
    subst (fun _ : Unit => f) (FGL.nmul G n) = subst (fun _ : Unit => FGL.nmul F n) f := by
  have h0 : ∀ s : Unit, constantCoeff ((fun _ : Unit => f) s) = 0 := fun _ => hf
  induction n with
  | zero =>
    change subst (fun _ : Unit => f) (0 : MvPowerSeries Unit R) =
      subst (fun _ : Unit => (0 : MvPowerSeries Unit R)) f
    rw [FGL.s0 _ h0, FGL.subst_zeros, hf, map_zero]
  | succ n ih =>
    change subst (fun _ : Unit => f) (FGL.ev G FGL.T (FGL.nmul G n)) =
      subst (fun _ : Unit => FGL.ev F FGL.T (FGL.nmul F n)) f
    rw [FGL.subst_ev G _ _ _ FGL.cc_T (FGL.cc_nmul G n) h0, FGL.sX _ h0 (), ih]
    set v : Fin 2 → MvPowerSeries Unit R := ![FGL.T, FGL.nmul F n] with hv
    have hv0 : ∀ s, constantCoeff (v s) = 0 := FGL.cc_vec2 FGL.cc_T (FGL.cc_nmul F n)
    have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
    have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp
    have hE : ∀ s : Unit, constantCoeff ((fun _ : Unit =>
        FGL.ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) s) = 0 := fun _ => FGL.cc_ev F X0 X1
    have e1 : (fun _ : Unit => FGL.ev F FGL.T (FGL.nmul F n)) =
        fun _ : Unit => subst v (FGL.ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) := by
      funext s
      rw [FGL.subst_ev F _ _ _ X0 X1 hv0, FGL.sX _ hv0, FGL.sX _ hv0]
      rfl
    have hf0 : constantCoeff (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f) = 0 :=
      FGL.cc0 _ (fun _ => X0) hf
    have hf1 : constantCoeff (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f) = 0 :=
      FGL.cc0 _ (fun _ => X1) hf
    rw [e1, ← FGL.ss _ v hE hv0, hhom, FGL.subst_ev G _ _ _ hf0 hf1 hv0,
      FGL.ss _ v (fun _ => X0) hv0, FGL.ss _ v (fun _ => X1) hv0]
    have ev0 : (fun _ : Unit => subst v (X 0 : MvPowerSeries (Fin 2) R)) = X := by
      funext s; rw [FGL.sX _ hv0]; rfl
    have ev1 : (fun _ : Unit => subst v (X 1 : MvPowerSeries (Fin 2) R)) =
        fun _ : Unit => FGL.nmul F n := by
      funext s; rw [FGL.sX _ hv0]; rfl
    rw [ev0, ev1, subst_self]
    rfl

end Hom

/-! ### reduction modulo `𝔪` -/

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- the prime ideal `𝔪 = {‖x‖ < 1}` of `𝒪`. -/
noncomputable def mI : Ideal 𝒪 := ballIdeal (K := K) one_pos

lemma mem_mI {x : 𝒪} : x ∈ mI (K := K) ↔ ‖(x : K)‖ < 1 := Iff.rfl

instance mI_prime : (mI (K := K)).IsPrime where
  ne_top' h := by
    have : (1 : 𝒪) ∈ mI (K := K) := h ▸ Submodule.mem_top
    rw [mem_mI] at this; simp at this
  mem_or_mem' {x y} hxy := by
    rw [mem_mI, mem_mI]
    rw [mem_mI, Subring.coe_mul, norm_mul] at hxy
    by_contra h; push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
    linarith

/-- reduction `𝒪 → 𝒪/𝔪`. -/
noncomputable abbrev red : 𝒪 →+* 𝒪 ⧸ mI (K := K) := Ideal.Quotient.mk _

lemma red_eq_zero {x : 𝒪} : red x = 0 ↔ ‖(x : K)‖ < 1 :=
  Ideal.Quotient.eq_zero_iff_mem.trans mem_mI

lemma red_ne_zero {x : 𝒪} : red x ≠ 0 ↔ ‖(x : K)‖ = 1 := by
  rw [ne_eq, red_eq_zero, not_lt]
  exact ⟨fun h => le_antisymm x.2 h, fun h => h.ge⟩

/-- the reduction has order `n` iff the coefficients below `n` are small and the `n`-th is a unit. -/
lemma lowOrd_red_iff (f : MvPowerSeries Unit 𝒪) (n : ℕ) :
    LowOrd (PowerSeries.map (red (K := K)) f) n ↔
      (∀ k < n, ‖((coeff (Finsupp.single () k) f : 𝒪) : K)‖ < 1) ∧
        ‖((coeff (Finsupp.single () n) f : 𝒪) : K)‖ = 1 := by
  unfold LowOrd
  simp only [PowerSeries.coeff_map]
  exact and_congr (forall₂_congr fun k _ => red_eq_zero) red_ne_zero

lemma red_subst {f g : MvPowerSeries Unit 𝒪} (hg : constantCoeff g = 0) :
    PowerSeries.map (red (K := K)) (subst (fun _ : Unit => g) f) =
      subst (fun _ : Unit => PowerSeries.map (red (K := K)) g) (PowerSeries.map (red (K := K)) f) :=
  MvPowerSeries.map_subst (FGL.hs (fun _ => hg)) f

variable [CompleteSpace K]

/-- `[p]_F ≡ T^{p²} · unit` (height two). -/
lemma lowOrd_nmul (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hp1 : ‖(p : K)‖ < 1) :
    LowOrd (PowerSeries.map (red (K := K)) (FGL.nmul F p)) (p ^ 2) := by
  rw [lowOrd_red_iff]
  refine ⟨fun k hk => ?_, hu⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, FGL.cc_nmul]; simp
  have hnd : ¬ p ^ 2 ∣ k := Nat.not_dvd_of_pos_of_lt hk0 hk
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp (FGL.mem_ideal_coeff_nmul p F k hnd)
  rw [← hst, Subring.coe_add, Subring.coe_mul, Subring.coe_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) s.2) ?_
    simpa using hp1
  · rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) t.2) ha

/-- `π ≡ T^{|C|} · unit`. -/
lemma lowOrd_pis {F : FormalGroup 𝒪} [F.IsComm] (S : FinSub F) :
    LowOrd (PowerSeries.map (red (K := K)) (pis S)) S.H.card := by
  obtain ⟨U, hU, hpi⟩ := pis_factor S
  have hred : PowerSeries.map (red (K := K)) (pis S) =
      PowerSeries.X ^ S.H.card * PowerSeries.map (red (K := K)) U := by
    rw [hpi, map_mul]
    congr 1
    change MvPowerSeries.map (red (K := K)) (∏ h ∈ S.H, (X () - C h)) = _
    rw [map_prod]
    have : ∀ h ∈ S.H, MvPowerSeries.map (red (K := K)) (X () - C h : MvPowerSeries Unit 𝒪) =
        PowerSeries.X := by
      intro h hh
      rw [map_sub, MvPowerSeries.map_X, MvPowerSeries.map_C,
        red_eq_zero.mpr (norm_lt_one_of_tn (S.tn h hh)), map_zero, sub_zero]
      rfl
    rw [Finset.prod_congr rfl this, Finset.prod_const]
  rw [hred]
  refine lowOrd_X_pow_mul _ ?_
  have hu := (isUnit_iff_constantCoeff.mp hU).map (red (K := K))
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu.ne_zero

/-- **height two passes to `F/C`** for `|C| = p`. -/
theorem quot_height (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hp1 : ‖(p : K)‖ < 1)
    (C : FinSub F) (hcard : C.H.card = p) :
    ‖topc (quot C) p‖ = 1 ∧ ‖hasse (quot C) p‖ < 1 := by
  have hp0 := hp.out.pos
  have hpp : p < p ^ 2 := by nlinarith [hp.out.two_le]
  have hπ := lowOrd_pis (K := K) C
  rw [hcard] at hπ
  have hF := lowOrd_nmul F p hu ha hp1
  have hcomp := hom_nmul F (quot C) (pis C) (cc_pis C) (pis_hom C) p
  have hR : LowOrd (PowerSeries.map (red (K := K))
      (subst (fun _ : Unit => FGL.nmul F p) (pis C))) (p * p ^ 2) := by
    rw [red_subst (FGL.cc_nmul F p)]
    exact lowOrd_subst hπ hF (by omega)
  rw [← hcomp, red_subst (cc_pis C)] at hR
  set g := PowerSeries.map (red (K := K)) (FGL.nmul (quot C) p) with hg
  by_cases hg0 : g = 0
  · exfalso
    rw [hg0] at hR
    have h0 : ∀ s : Unit, MvPowerSeries.constantCoeff
        ((fun _ : Unit => PowerSeries.map (red (K := K)) (pis C)) s) = 0 :=
      fun _ => hπ.cc_zero hp0
    rw [FGL.s0 _ h0] at hR
    exact hR.2 (map_zero _)
  have hgo : LowOrd g g.order.toNat :=
    ⟨fun k hk => PowerSeries.coeff_of_lt_order_toNat k hk, PowerSeries.coeff_order hg0⟩
  have h2 := (lowOrd_subst hgo hπ hp0).unique hR
  have hn : g.order.toNat = p ^ 2 := by
    have : g.order.toNat * p = p ^ 2 * p := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  rw [hn, hg, lowOrd_red_iff] at hgo
  exact ⟨hgo.2, hgo.1 p hpp⟩

end QuotientHasse
