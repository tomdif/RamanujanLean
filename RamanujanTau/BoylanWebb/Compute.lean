import RamanujanTau.BoylanWebb.Series
import RamanujanTau.TauBridge
import RamanujanTau.MockTheta5PentagonalRecurrence

/-!
# Kernel-checkable truncated q-series arithmetic mod `ℓ`

`Cg ℓ d F G` means `F ≡ G (mod ℓ, q^{d+1})`. Coefficient lists (`RamanujanTau.toPS`) are related to
honest power series through `Cg`:
* `Cg_tmul`: truncated, reduced products of lists (`tmul`) represent products;
* `Cg_shift`: multiplication by `q^k`;
* `Cg_pent`: Euler's pentagonal theorem gives a list for `(q;q)_∞` (`pentBuild`);
* `Cg_of_formula`: a list agrees with a series whose coefficients have a computable formula;
* `Cg_coeff`: reading off coefficients.
All list identities are then checked by `decide +kernel` on literal lists (one product per check, so
the kernel never re-evaluates a shared subterm).
-/

set_option autoImplicit false

namespace BoylanWebb
open PowerSeries RamanujanTau MockTheta5.JTP

/-- reduce every coefficient mod `l`. -/
def red (l : ℤ) (L : List ℤ) : List ℤ := L.map (fun x => x % l)

/-- truncated product mod `l`, keeping degrees `≤ d`. -/
def tmul (l : ℤ) (d : ℕ) (a b : List ℤ) : List ℤ := red l (truncList d (mulList a b))

/-- the sign `(−1)^{m+1}` of the `m`-th pentagonal pair. -/
def pentSign (m : ℕ) : ℤ := if m % 2 = 0 then -1 else 1

/-- `1 + Σ_{m<M} (−1)^{m+1} (q^{(m+1)(3m+2)/2} + q^{(m+1)(3m+4)/2})`. -/
def pentBuild : ℕ → List ℤ
  | 0 => [1]
  | m + 1 => addList (pentBuild m)
      (addList (shiftList ((m + 1) * (3 * m + 2) / 2) [pentSign m])
        (shiftList ((m + 1) * (3 * m + 4) / 2) [pentSign m]))

variable (ℓ : ℕ) (d : ℕ)

/-- `F ≡ G (mod ℓ, q^{d+1})`. -/
def Cg (F G : PowerSeries ℤ) : Prop := (X : PowerSeries (ZMod ℓ)) ^ (d + 1) ∣ Ψ ℓ F - Ψ ℓ G

variable {ℓ d}

lemma Cg.refl (F : PowerSeries ℤ) : Cg ℓ d F F := by simp [Cg]

lemma Cg.symm {F G : PowerSeries ℤ} (h : Cg ℓ d F G) : Cg ℓ d G F := by
  rw [Cg, ← neg_sub]; exact (dvd_neg).mpr h

lemma Cg.trans {F G H : PowerSeries ℤ} (h1 : Cg ℓ d F G) (h2 : Cg ℓ d G H) : Cg ℓ d F H := by
  rw [Cg, show Ψ ℓ F - Ψ ℓ H = (Ψ ℓ F - Ψ ℓ G) + (Ψ ℓ G - Ψ ℓ H) by ring]; exact dvd_add h1 h2

lemma Cg.mul {F F' G G' : PowerSeries ℤ} (h1 : Cg ℓ d F F') (h2 : Cg ℓ d G G') :
    Cg ℓ d (F * G) (F' * G') := by
  rw [Cg, map_mul, map_mul,
    show Ψ ℓ F * Ψ ℓ G - Ψ ℓ F' * Ψ ℓ G' = Ψ ℓ F * (Ψ ℓ G - Ψ ℓ G') + Ψ ℓ G' * (Ψ ℓ F - Ψ ℓ F') by ring]
  exact dvd_add (Dvd.dvd.mul_left h2 _) (Dvd.dvd.mul_left h1 _)

lemma Cg.pow {F G : PowerSeries ℤ} (h : Cg ℓ d F G) (n : ℕ) : Cg ℓ d (F ^ n) (G ^ n) := by
  induction n with
  | zero => exact Cg.refl _
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

lemma Cg.of_eq {F G : PowerSeries ℤ} (h : F = G) : Cg ℓ d F G := h ▸ Cg.refl _

lemma coeffList_red (l : ℤ) : ∀ (L : List ℤ) (n : ℕ), coeffList (red l L) n = coeffList L n % l
  | [], n => by simp [red, coeffList]
  | a :: as, 0 => by simp [red, coeffList]
  | a :: as, n + 1 => by
    have := coeffList_red l as n
    simp only [red, List.map_cons, coeffList] at this ⊢
    exact this

lemma Ψ_toPS_red (L : List ℤ) : Ψ ℓ (toPS (red ℓ L)) = Ψ ℓ (toPS L) := by
  ext n
  rw [coeff_map, coeff_map, toPS, toPS, coeff_mk, coeff_mk, coeffList_red]
  simp

lemma Cg_red (L : List ℤ) : Cg ℓ d (toPS (red ℓ L)) (toPS L) := by
  rw [Cg, Ψ_toPS_red, sub_self]; exact dvd_zero _

lemma Cg_trunc (L : List ℤ) : Cg ℓ d (toPS (truncList d L)) (toPS L) := by
  rw [Cg, PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, coeff_map, coeff_map, toPS, toPS, coeff_mk, coeff_mk, coeffList_truncList,
    if_pos (by omega), sub_self]

/-- products of lists. -/
lemma Cg_tmul {F G : PowerSeries ℤ} {a b : List ℤ} (hF : Cg ℓ d F (toPS a)) (hG : Cg ℓ d G (toPS b)) :
    Cg ℓ d (F * G) (toPS (tmul ℓ d a b)) := by
  refine (hF.mul hG).trans ?_
  rw [← toPS_mulList]
  exact ((Cg_red _).trans (Cg_trunc _)).symm

lemma toPS_replicate_append (k : ℕ) (L : List ℤ) : toPS (List.replicate k 0 ++ L) = X ^ k * toPS L := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, toPS_cons, ih, map_zero, zero_add]; ring

lemma toPS_shiftList : ∀ (k : ℕ) (L : List ℤ), toPS (shiftList k L) = X ^ k * toPS L
  | 0, L => by simp [shiftList]
  | k + 1, L => by rw [shiftList, toPS_cons, toPS_shiftList k L, map_zero, zero_add]; ring

/-- multiplication by `q^k`. -/
lemma Cg_shift {F : PowerSeries ℤ} {a : List ℤ} (k : ℕ) (hF : Cg ℓ d F (toPS a)) :
    Cg ℓ d (X ^ k * F) (toPS (truncList d (shiftList k a))) := by
  refine ((Cg.refl (X ^ k)).mul hF).trans ?_
  rw [← toPS_shiftList]
  exact (Cg_trunc _).symm

/-- reading off coefficients. -/
lemma Cg_coeff {F : PowerSeries ℤ} {L : List ℤ} (h : Cg ℓ d F (toPS L)) {n : ℕ} (hn : n ≤ d) :
    coeff n (Ψ ℓ F) = ((coeffList L n : ℤ) : ZMod ℓ) := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) n (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [this, coeff_map, toPS, coeff_mk]; rfl

/-- a list agrees with a series given by a coefficient formula. -/
lemma Cg_of_formula {F : PowerSeries ℤ} (g : ℕ → ℤ) (hg : ∀ n, coeff n F = g n) (L : List ℤ)
    (hchk : ∀ n, n < d + 1 → (coeffList L n - g n) % (ℓ : ℤ) = 0) : Cg ℓ d F (toPS L) := by
  rw [Cg, PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, coeff_map, coeff_map, hg, toPS, coeff_mk, sub_eq_zero]
  have h := Int.dvd_of_emod_eq_zero (hchk n hn)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero] at h
  exact h.symm

/-! ## Euler's pentagonal theorem as a list -/

lemma sgn_pent_pos (m : ℕ) : sgn ((m : ℤ) + 1) = pentSign m := by
  rw [sgn_succ, sgn_natCast, pentSign]
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff] at h; omega)]; norm_num

lemma sgn_pent_neg (m : ℕ) : sgn (-((m : ℤ) + 1)) = pentSign m := by rw [sgn_neg, sgn_pent_pos]

lemma toPS_pentBuild (M : ℕ) : toPS (pentBuild M) = PowerSeries.map evm1 (pentFiniteP M) := by
  induction M with
  | zero =>
    rw [map_evm1_pentFiniteP, Finset.sum_range_zero, add_zero, pentBuild, toPS_cons, toPS_nil]; simp
  | succ m ih =>
    rw [pentBuild, toPS_addList, toPS_addList, toPS_shiftList, toPS_shiftList, ih,
      map_evm1_pentFiniteP, map_evm1_pentFiniteP, Finset.sum_range_succ, sgn_pent_pos, sgn_pent_neg,
      toPS_cons, toPS_nil]
    ring

lemma pent_exp_mono {m M : ℕ} (h : M ≤ m) : (M + 1) * (3 * M + 2) / 2 ≤ (m + 1) * (3 * m + 2) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

/-- **Euler's pentagonal theorem, truncated**: `M` pentagonal pairs give `(q;q)_∞` through degree `d`
when `d < (M+1)(3M+2)/2`. -/
lemma Cg_pent (M : ℕ) (hM : d < (M + 1) * (3 * M + 2) / 2) : Cg ℓ d qfacInf (toPS (pentBuild M)) := by
  have hZ : (X : PowerSeries ℤ) ^ (d + 1) ∣ qfacInf - toPS (pentBuild M) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro a ha
    rw [map_sub, euler_pentagonal, coeff_pentSeries_lt (M := M + (d + 1)) (by omega),
      toPS_pentBuild, map_evm1_pentFiniteP, map_evm1_pentFiniteP, Finset.sum_range_add, ← add_assoc,
      map_add, add_sub_cancel_left, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 := pent_exp_mono (show M ≤ M + i by omega)
    have h2 : (M + i + 1) * (3 * (M + i) + 2) / 2 ≤ (M + i + 1) * (3 * (M + i) + 4) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul le_rfl (by omega))
    rw [map_add, coeff_X_pow_mul', coeff_X_pow_mul', if_neg (by omega), if_neg (by omega), add_zero]
  obtain ⟨g, hg⟩ := hZ
  exact ⟨Ψ ℓ g, by rw [← map_sub, hg, map_mul, map_pow, PowerSeries.map_X]⟩

end BoylanWebb
