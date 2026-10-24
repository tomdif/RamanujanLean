/-
# A product calculus for `(q^b; q^a)_∞`

`Pinf_splitk`: `(q^b;q^a)_∞ = Π_{j<k} (q^{b+aj}; q^{ka})_∞`. Splitting every factor to a common modulus turns identities
between theta products `J_{b,a} = (q^b;q^a)(q^{a−b};q^a)(q^a;q^a)` into commutative-ring identities between the
factors `(q^r; q^M)_∞`, which `ring` decides.
-/
import RamanujanTau.RankTheta

set_option autoImplicit false

namespace MTC
open PowerSeries Finset RankProof

lemma dvd_sub_prodZ {K : ℕ} (s : Finset ℕ) (F G : ℕ → PowerSeries ℤ)
    (h : ∀ j, (X : PowerSeries ℤ) ^ K ∣ F j - G j) :
    (X : PowerSeries ℤ) ^ K ∣ ∏ j ∈ s, F j - ∏ j ∈ s, G j := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [prod_insert ha, prod_insert ha,
    show F a * ∏ j ∈ s, F j - G a * ∏ j ∈ s, G j = (F a - G a) * ∏ j ∈ s, F j + G a * (∏ j ∈ s, F j - ∏ j ∈ s, G j)
      by ring]
  exact dvd_add (dvd_mul_of_dvd_left (h a) _) (dvd_mul_of_dvd_right ih _)

lemma Pfin_add (b a M K : ℕ) : Pfin b a (M + K) = Pfin b a M * ∏ i ∈ range K, (1 - X ^ (b + a * (M + i))) := by
  rw [Pfin, Pfin, prod_range_add]

lemma Pfin_splitk (b a k : ℕ) : ∀ M, Pfin b a (k * M) = ∏ j ∈ range k, Pfin (b + a * j) (k * a) M
  | 0 => by simp [Pfin]
  | M + 1 => by
    rw [show k * (M + 1) = k * M + k by ring, Pfin_add, Pfin_splitk b a k M]
    rw [show (∏ j ∈ range k, Pfin (b + a * j) (k * a) (M + 1)) =
        ∏ j ∈ range k, (Pfin (b + a * j) (k * a) M * (1 - X ^ (b + a * j + k * a * M))) from
      prod_congr rfl fun j _ => Pfin_succ _ _ _, prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    congr 2; ring

/-- **`(q^b;q^a)_∞ = Π_{j<k} (q^{b+aj};q^{ka})_∞`**. -/
theorem Pinf_splitk (b a k : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    Pinf b a = ∏ j ∈ range k, Pinf (b + a * j) (k * a) := by
  symm
  refine Pinf_ext hb ha fun N => ?_
  have h1 : (X : PowerSeries ℤ) ^ (N + 1) ∣ ∏ j ∈ range k, Pinf (b + a * j) (k * a) -
      ∏ j ∈ range k, Pfin (b + a * j) (k * a) N :=
    dvd_sub_prodZ _ _ _ fun j => X_pow_dvd_Pinf_sub _ _ (by omega) (by nlinarith) N
  have h2 := X_pow_dvd_Pfin_sub b a N hb ha (k * N) (by nlinarith)
  rw [Pfin_splitk] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- `J_{b,a}` as a product. -/
noncomputable def Jp (b a : ℕ) : PowerSeries ℤ := Pinf b a * Pinf (a - b) a * Pinf a a

end MTC
