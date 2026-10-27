exec(open('branches.py').read().replace("print(","(lambda *a: None)("))
src=open('../../RamanujanTau/Atkin11Dissect.lean').read()
head=src[:src.index('section Terms')]
head=head.replace('ALz11','ALz13').replace('ALThetaCore11','ALThetaCore13')
head=head.replace('# The 11-dissection of Euler\'s product','# The 13-dissection of Euler\'s product')
head=head.replace("""With `q = t^{d'}`, `Q = q¹¹`, `J_a = θ(Q^a; Q¹¹)` and `E(q) = Σ (−1)^k q^{k(3k−1)/2}`:

  `E(q) = E(q¹²¹)·(J₄/J₂ − q·J₂/J₁ − q²·J₅/J₃ + q⁵ + q⁷·J₃/J₄ − q¹⁵·J₁/J₅)`.""","""With `q = t^{d'}`, `Q = q¹³`, `J_a = θ(Q^a; Q¹³)` and `E(q) = Σ (−1)^k q^{k(3k−1)/2}`:

  `E(q) = E(q¹⁶⁹)·(J₄/J₂ − q·J₆/J₃ − q²·J₂/J₁ + q⁵·J₅/J₄ + q⁷ − q¹²·J₃/J₅ + q²²·J₁/J₆)`.""")
head=head.replace("thirteen","thirteen").replace("eleven `k mod 11` branches","thirteen `k mod 13` branches")
head=head.replace("(hd : N = 11 * d)","(hd : N = 13 * d)").replace("(hd' : d = 11 * d')","(hd' : d = 13 * d')")
head=head.replace("θ(Q^x; Q³³)","θ(Q^x; Q³⁹)").replace("θ(Q^{16−3ρ}; Q³³)","θ(Q^{19−3ρ}; Q³⁹)").replace("Pt h3 d (16 - 3 * ρ)","Pt h3 d (19 - 3 * ρ)")
head=head.replace("Pt h3 d (33 - x)","Pt h3 d (39 - x)").replace("Pt h3 d (x + 33)","Pt h3 d (x + 39)").replace("d * (x + 33)","d * (x + 39)")
head=head.replace("hN' hE 11","hN' hE 13").replace("((11 : ℕ) : ℤ)","((13 : ℕ) : ℤ)").replace("(-1) ^ (11 + 1) * (1 : ℂ) ^ 11","(-1) ^ (13 + 1) * (1 : ℂ) ^ 13").replace("((-1 : ℂ) ^ (11 + 1) * (1 : ℂ) ^ 11)","((-1 : ℂ) ^ (13 + 1) * (1 : ℂ) ^ 13)")
head=head.replace("3 * d' * 11 * 11 = 3 * N","3 * d' * 13 * 13 = 3 * N").replace("c2 ((11 : ℕ) : ℤ) = 55","c2 ((13 : ℕ) : ℤ) = 78").replace("c2 ((13 : ℕ) : ℤ) = 55","c2 ((13 : ℕ) : ℤ) = 78")
out=[head,"section Terms\nvariable {N : ℕ} {d : ℕ} (hd : N = 13 * d) {d' : ℕ} (hd' : d = 13 * d') (h3 : 1 ≤ 3 * N)\ninclude hd hd'\n"]
for rho,e,sign,x,tg,ops in res:
    e0=3*c2(-rho)-rho; x0=19-3*rho
    C='1' if sign==1 else '(-1)'
    L=[f"lemma dTerm_{rho} : dTerm h3 d d' {rho} = C {C} * (mono d' 1) ^ {e} * Pt h3 d {x} := by",
       "  unfold dTerm",
       f"  rw [show (3 * c2 (-(({rho} : ℕ) : ℤ)) - (({rho} : ℕ) : ℤ)) = {e0} by decide,",
       f"    show (19 : ℤ) - 3 * (({rho} : ℕ) : ℤ) = {x0} by norm_num]"]
    if not ops:
        L.append(f"  rw [mono_to_pow d' _ {e} (by push_cast; ring)]")
    elif ops[0][0]=='refl':
        L.append(f"  rw [show ({x0} : ℤ) = 39 - {x} by norm_num, Pt_refl hd h3 {x}, mono_to_pow d' _ {e} (by push_cast; ring)]")
    else:
        L.append(f"  rw [Pt_shift hd h3 ({x0}), show ({x0} : ℤ) + 39 = {x} by norm_num]")
        L.append(f"  rw [← mul_assoc, mono_mul, mono_to_pow d' _ {e} (by rw [hd']; push_cast; ring)]")
    L.append("  norm_num\n")
    out.append("\n".join(L))
out.append("end Terms\n")
main='''section Main
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 13 * d) {d' : ℕ} (hd' : d = 13 * d') (h3 : 1 ≤ 3 * N)
  (hE : 1 ≤ 3 * d')

include hd in
/-- the quintuple product at `z = Q^a`. -/
lemma quint_J (a : ℤ) :
    (Pt h3 d (13 + 3 * a) + mono (d * a) 1 * Pt h3 d (26 + 3 * a)) * Jt hN hd a = Pt h3 d 13 * Jt hN hd (2 * a) := by
  have h := quint_theta hN h3 ((d : ℤ) * a) (one_ne_zero (α := ℂ))
  simp only [one_pow] at h
  rw [show (N : ℤ) + 3 * (d * a) = d * (13 + 3 * a) by rw [hd]; push_cast; ring,
    show 2 * (N : ℤ) + 3 * (d * a) = d * (26 + 3 * a) by rw [hd]; push_cast; ring,
    show (N : ℤ) = d * 13 by rw [hd]; push_cast; ring, show 2 * ((d : ℤ) * a) = d * (2 * a) by ring] at h
  exact h

include hd hd' in
lemma quint_J' (a : ℤ) (k : ℕ) (hk : (13 : ℤ) * a = k) (ha0 : 0 < a) (ha1 : a < 13) :
    Pt h3 d (13 + 3 * a) + (mono d' 1) ^ k * Pt h3 d (26 + 3 * a) = Pt h3 d 13 * Jt hN hd (2 * a) / Jt hN hd a := by
  rw [eq_div_iff (Jt_ne hN hd ha0 ha1), ← quint_J hN hd h3 a,
    mono_to_pow d' (A := (d : ℤ) * a) 1 k (by rw [hd']; push_cast; rw [← hk]; ring), map_one, one_mul]

include hd hd' in
/-- **The 13-dissection of Euler's product.** -/
theorem E_dissect :
    θ hE d' 1 = Pt h3 d 13 * (Jt hN hd 4 / Jt hN hd 2 - mono d' 1 * (Jt hN hd 6 / Jt hN hd 3)
      - (mono d' 1) ^ 2 * (Jt hN hd 2 / Jt hN hd 1) + (mono d' 1) ^ 5 * (Jt hN hd 5 / Jt hN hd 4) + (mono d' 1) ^ 7
      - (mono d' 1) ^ 12 * (Jt hN hd 3 / Jt hN hd 5) + (mono d' 1) ^ 22 * (Jt hN hd 1 / Jt hN hd 6)) := by
  rw [θ_dissect hE 13 (by norm_num) (d' : ℤ) one_ne_zero,
    Finset.sum_congr rfl fun (ρ : Fin 13) _ => dis_term hd hd' h3 hE (ρ : ℕ), Fin.sum_univ_eq_sum_range (dTerm h3 d d') 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [DTERMS]
  have e1 := quint_J' hN hd hd' h3 1 13 (by norm_num) (by norm_num) (by norm_num)
  have e2 := quint_J' hN hd hd' h3 2 26 (by norm_num) (by norm_num) (by norm_num)
  have e3 := quint_J' hN hd hd' h3 3 39 (by norm_num) (by norm_num) (by norm_num)
  have e4 := quint_J' hN hd hd' h3 4 52 (by norm_num) (by norm_num) (by norm_num)
  have e5 := quint_J' hN hd hd' h3 5 65 (by norm_num) (by norm_num) (by norm_num)
  have e6 := quint_J' hN hd hd' h3 6 78 (by norm_num) (by norm_num) (by norm_num)
  have j8 : Jt hN hd (2 * 4) = Jt hN hd 5 := by rw [← Jt_refl hN hd 5]; norm_num [Jt]
  have j10 : Jt hN hd (2 * 5) = Jt hN hd 3 := by rw [← Jt_refl hN hd 3]; norm_num [Jt]
  have j12 : Jt hN hd (2 * 6) = Jt hN hd 1 := by rw [← Jt_refl hN hd 1]; norm_num [Jt]
  rw [j8] at e4; rw [j10] at e5; rw [j12] at e6
  rw [show (13 : ℤ) + 3 * 1 = 16 by norm_num, show (26 : ℤ) + 3 * 1 = 29 by norm_num, show (2 : ℤ) * 1 = 2 by norm_num] at e1
  rw [show (13 : ℤ) + 3 * 2 = 19 by norm_num, show (26 : ℤ) + 3 * 2 = 32 by norm_num, show (2 : ℤ) * 2 = 4 by norm_num] at e2
  rw [show (13 : ℤ) + 3 * 3 = 22 by norm_num, show (26 : ℤ) + 3 * 3 = 35 by norm_num, show (2 : ℤ) * 3 = 6 by norm_num] at e3
  rw [show (13 : ℤ) + 3 * 4 = 25 by norm_num, show (26 : ℤ) + 3 * 4 = 38 by norm_num] at e4
  rw [show (13 : ℤ) + 3 * 5 = 28 by norm_num, show (26 : ℤ) + 3 * 5 = 41 by norm_num] at e5
  rw [show (13 : ℤ) + 3 * 6 = 31 by norm_num, show (26 : ℤ) + 3 * 6 = 44 by norm_num] at e6
  simp only [map_one, map_neg, one_mul, neg_mul, pow_zero, mul_one]
  linear_combination e2 - (mono d' 1) ^ 2 * e1 - (mono d' 1) * e3 + (mono d' 1) ^ 5 * e4 - (mono d' 1) ^ 12 * e5
    + (mono d' 1) ^ 22 * e6

end Main

end ALz13
'''
main=main.replace("DTERMS",", ".join(f"dTerm_{r} hd hd' h3" for r in range(13)))
out.append(main)
open('../../RamanujanTau/Atkin13Dissect.lean','w').write("\n".join(out))
