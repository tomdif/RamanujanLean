/-
Kernel checks of the degree-6 tail certificate (light imports: no real analysis is loaded here).
-/
import RamanujanTau.JensenThreshold.Tail.Data6

namespace JensenThreshold.Tail

theorem boxes6_ok : boxes6.all (checkBox 6 9 60) = true := by decide +kernel

theorem cover6_ok : coverOK boxes6 tmax6 = true := by decide +kernel

end JensenThreshold.Tail
