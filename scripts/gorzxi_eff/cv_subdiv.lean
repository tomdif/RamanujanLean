import RamanujanTau.GORZXiEff.CVRegionB
open GORZXiEff.CV JensenThreshold.Tail JensenThreshold.Tail.Iv
partial def subdivP (P : ℤ → ℤ → Bool) (p q : ℤ) : List ℤ :=
  if P p q then [p] else let m := (p + q) / 2; if m = p then [] else subdivP P p m ++ subdivP P m q
#eval IO.println (toString (subdivP cellM 0 737 ++ [737]))
#eval IO.println (toString (subdivP cellB 0 737 ++ [737]))
#eval IO.println (toString (subdivP cellA 737 49152 ++ [49152]))
