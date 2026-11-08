import E13Lrat.Cnf
import E13Lrat.Store4

/-! # NT-E13.1, m = 4, unsplit: the store `S4` begins with `cnf 4 164` and ends with the empty clause -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem cnf4_length : (cnf 4 164).length = 25287 := by decide +kernel

theorem store4_cnf : chkF S4 (cnf 4 164) 1 = true := by decide +kernel

theorem store4_last : lastEmpty S4 298598 = true := by decide +kernel

end E13Lrat
