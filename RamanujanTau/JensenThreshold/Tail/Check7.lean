/-
Kernel checks of the degree-7 tail certificate (light imports: no real analysis is loaded here).
-/
import RamanujanTau.JensenThreshold.Tail.Data7

namespace JensenThreshold.Tail

theorem boxes7_ok : boxes7.all (checkBox 7 10 60) = true := by decide +kernel

theorem cover7_ok : coverOK boxes7 tmax7 = true := by decide +kernel

end JensenThreshold.Tail
