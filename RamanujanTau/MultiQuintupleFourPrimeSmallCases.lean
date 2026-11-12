import RamanujanTau.MultiQuintupleFourPrimeConverseLarge

/-! The canonical prime reflection family has exactly ten cases below the cutoff. -/
namespace Ramanujan.MultiQuintuple

private theorem fourPrime_small_cases_finite : ∀ m n : Fin 10,
    (m.val^2+n.val^2).Prime → m.val^2+n.val^2 ≤ 100 →
    0<n.val → n.val<m.val → 2*(m.val+n.val)<m.val^2+n.val^2 →
    (m.val=3 ∧ n.val=2) ∨ (m.val=4 ∧ n.val=1) ∨
    (m.val=5 ∧ n.val=2) ∨ (m.val=5 ∧ n.val=4) ∨
    (m.val=6 ∧ n.val=1) ∨ (m.val=6 ∧ n.val=5) ∨
    (m.val=7 ∧ n.val=2) ∨ (m.val=8 ∧ n.val=3) ∨
    (m.val=8 ∧ n.val=5) ∨ (m.val=9 ∧ n.val=4) := by
  decide +kernel

theorem fourPrime_small_cases {p m n : ℕ} (hprime : p.Prime)
    (hp : p=m^2+n^2) (hp100 : p≤100) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) :
    (m=3 ∧ n=2) ∨ (m=4 ∧ n=1) ∨ (m=5 ∧ n=2) ∨ (m=5 ∧ n=4) ∨
    (m=6 ∧ n=1) ∨ (m=6 ∧ n=5) ∨ (m=7 ∧ n=2) ∨ (m=8 ∧ n=3) ∨
    (m=8 ∧ n=5) ∨ (m=9 ∧ n=4) := by
  have hm : m<10 := by nlinarith
  have hn : n<10 := by omega
  exact fourPrime_small_cases_finite ⟨m,hm⟩ ⟨n,hn⟩ (hp ▸ hprime) (hp ▸ hp100)
    hnpos hnm (hp ▸ hbound)

end Ramanujan.MultiQuintuple
