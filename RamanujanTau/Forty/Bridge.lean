/-
# From theta sums in `ℂ((t))` to products in `ℤ⟦q⟧` (with `q = t`)

* `ι = ιN 1 : ℤ⟦X⟧ → ℂ((t))`, `X ↦ t`; injective (`ι_inj`), `ι X = t` (`ι_X`).
* `θ_unb`: `θ_N(e, 1) = ι((q^e;q^N)(q^{N−e};q^N)(q^N;q^N))` for `0 < e < N` (Jacobi triple product).
* `θ_bar`: `θ_N(e, −1) · ι(J_{e,N}) = ι(J_{2e,2N} J_{N,2N})` for `0 < e < N`.
* `θ_bar0`: `θ_N(0, −1) · ι((q^N;q^{2N})) = 2 ι((q^{2N};q^{2N}))`  (`f(1,q) = 2ψ(q)`).
* `atom`: `(q^b;q^a)_∞ = ∏_{j < M/a} (q^{b+aj};q^M)_∞` for `a ∣ M`, `a < M` — splits all products to a common
  modulus, after which product identities are closed by `ring`.
-/
import RamanujanTau.MTC.ProdId
import RamanujanTau.Forty.Lattice
import RamanujanTau.Forty.Defs

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

lemma one_le_one' : 1 ≤ 1 := le_rfl

/-- `ι : ℤ⟦q⟧ → ℂ((t))`, `q ↦ t`. -/
noncomputable abbrev ι : PowerSeries ℤ →+* L := ιN one_le_one'

lemma ι_inj : Function.Injective ι := fun f g h => by
  ext k
  have := congrArg (fun F : L => F.coeff ((1 * k : ℕ) : ℤ)) h
  simp only [ιN_coeff_nat, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (show 0 < 1 by omega)] at this
  exact_mod_cast this

lemma ι_X : ι PowerSeries.X = mono 1 1 := by
  simp only [ιN, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    PowerSeries.expand_X, map_pow, PowerSeries.map_X]
  rw [HahnSeries.ofPowerSeries_X, mono, single_pow]
  simp

lemma ι_Xpow (k : ℕ) : ι (PowerSeries.X ^ k) = mono k 1 := by
  rw [map_pow, ι_X, mono, single_pow]; simp

/-- the triple product `J_{e,N} = (q^e;q^N)(q^{N−e};q^N)(q^N;q^N)`. -/
noncomputable def J (e N : ℕ) : PowerSeries ℤ := Pinf e N * Pinf (N - e) N * Pinf N N

lemma θ_unb {N : ℕ} (h : 1 ≤ N) (e : ℕ) (he : 1 ≤ e) (heN : e < N) : θ h (e : ℤ) 1 = ι (J e N) := by
  have := θ_eq_ιN_prod (d := 1) (a := N) (b := e) one_le_one' he heN (by simpa using h)
  simp only [one_mul] at this
  exact this

/-- `θ_N(e,1) θ_N(e,−1) = θ_{2N}(2e,1) θ_{2N}(N,1)` (HM (1.4b) at `y = −x`). -/
lemma θ_bar {N : ℕ} (h : 1 ≤ N) (e : ℕ) (he : 1 ≤ e) (heN : e < N) :
    θ h (e : ℤ) (-1) * ι (J e N) = ι (J (2 * e) (2 * N) * J N (2 * N)) := by
  have hm := θ_mul h e e one_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)
  have hq : θ (h2N h) (2 * N + e - e) 1 = 0 := by
    rw [show (2 * N + e - e : ℤ) = ((2 * N : ℕ) : ℤ) * 1 by push_cast; ring]
    exact θ_qpow (h2N h) 1
  simp only [mul_neg, mul_one, neg_neg, div_neg, div_one] at hm
  rw [show ((N : ℤ) + e - e) = ((N : ℕ) : ℤ) by ring, hq, mul_zero, mul_zero, sub_zero] at hm
  rw [← θ_unb h e he heN, map_mul, ← θ_unb (h2N h) (2 * e) (by omega) (by omega),
    ← θ_unb (h2N h) N (by omega) (by omega), mul_comm]
  rw [show ((2 * e : ℕ) : ℤ) = e + e by push_cast; ring]
  exact hm

lemma θbar0' {N : ℕ} (h : 1 ≤ N) : θ h 0 (-1) = 2 * θ (hN' h 2 two_pos) N (-1) := by
  have hdis := dissect2 h 0 (by norm_num : (-1 : ℂ) ≠ 0)
  simp only [mul_zero, add_zero, zero_sub, sub_zero, show ((-1 : ℂ)) ^ 2 = 1 by norm_num,
    show -((-1 : ℂ))⁻¹ = 1 by norm_num] at hdis
  rw [inv_m'] at hdis
  have hmm : (mono N 1 : L) * -mono (-(N : ℤ)) (-1) = 1 := by
    rw [show -(mono (-(N : ℤ)) (-1) : L) = mono (-(N : ℤ)) 1 by simp [mono], mono_mul,
      show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  rw [show (mono 0 1 : L) = 1 from rfl, one_mul] at hdis
  rw [hdis]
  linear_combination θ (hN' h 2 two_pos) N (-1) * hmm

/-- splitting a product to a common modulus. -/
theorem atom (b a M : ℕ) (hb : 1 ≤ b) (ha : a < M) (hd : a ∣ M) (ha1 : 1 ≤ a) :
    Pinf b a = ∏ j ∈ range (M / a), Pinf (b + a * j) M := by
  have hk : 1 ≤ M / a := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.div_eq_zero_iff] at h0; omega)
  rw [Pinf_splitk b a (M / a) hb ha1 hk, Nat.div_mul_cancel hd]

/-- `J_{2,8} J_{4,8} (q;q²) = J_{1,4} (q²;q²)` (Gauss: `ψ(q) = (q²;q²)/(q;q²)`). -/
lemma psi_prod1 : J 2 8 * J 4 8 * Pinf 1 2 = J 1 4 * Pinf 2 2 := by
  simp only [J]
  rw [atom 1 2 8 le_rfl (by norm_num) (by norm_num) (by norm_num), atom 2 2 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atom 1 4 8 le_rfl (by norm_num) (by norm_num) (by norm_num), atom 3 4 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atom 4 4 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

lemma psi_prod (N : ℕ) [NeZero N] :
    J (2 * N) (8 * N) * J (4 * N) (8 * N) * Pinf N (2 * N) = J N (4 * N) * Pinf (2 * N) (2 * N) := by
  have h := congrArg (S N) psi_prod1
  simp only [J, map_mul] at h
  rw [S_Pinf N 2 8 (by norm_num) (by norm_num), S_Pinf N 6 8 (by norm_num) (by norm_num),
    S_Pinf N 8 8 (by norm_num) (by norm_num), S_Pinf N 4 8 (by norm_num) (by norm_num),
    S_Pinf N 1 2 (by norm_num) (by norm_num), S_Pinf N 1 4 (by norm_num) (by norm_num),
    S_Pinf N 3 4 (by norm_num) (by norm_num), S_Pinf N 4 4 (by norm_num) (by norm_num),
    S_Pinf N 2 2 (by norm_num) (by norm_num)] at h
  simp only [J]
  rw [show 8 * N - 2 * N = N * 6 by omega, show 8 * N - 4 * N = N * 4 by omega, show 4 * N - N = N * 3 by omega,
    mul_comm 2 N, mul_comm 8 N, mul_comm 4 N]
  simpa [mul_comm] using h

/-- `f(1, q^N) = 2ψ(q^N)`: `θ_N(0,−1) (q^N;q^{2N}) = 2 (q^{2N};q^{2N})`. -/
theorem θ_bar0 {N : ℕ} [NeZero N] (h : 1 ≤ N) : θ h 0 (-1) * ι (Pinf N (2 * N)) = 2 * ι (Pinf (2 * N) (2 * N)) := by
  have h4 : 1 ≤ 4 * N := by omega
  have hb := θ_bar h4 N h (by omega)
  rw [θbar0' h, θ_N' (by ring) (hN' h 2 two_pos) h4 (N : ℤ) (-1)]
  have hp := congrArg ι (psi_prod N)
  simp only [map_mul] at hp hb
  have hne : ι (J N (4 * N)) ≠ 0 := by
    intro h0
    have := ι_inj (h0.trans (map_zero ι).symm)
    simp only [J] at this
    exact ((((isUnit_Pinf N (4 * N) h h4).mul (isUnit_Pinf (4 * N - N) (4 * N) (by omega) h4)).mul
      (isUnit_Pinf (4 * N) (4 * N) h4 h4)).ne_zero) this
  apply mul_right_cancel₀ hne
  rw [show 2 * (4 * N) = 8 * N by ring] at hb
  linear_combination (2 * ι (Pinf N (2 * N))) * hb + 2 * hp

end Forty
