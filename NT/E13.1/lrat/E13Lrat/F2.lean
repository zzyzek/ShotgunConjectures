import E13Lrat.Cnf
import E13Lrat.Store2

/-! # NT-E13.1, m = 2: the store begins with `cnf 2 84` and ends with the empty clause -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem cnf2_length : (cnf 2 84).length = 6891 := by decide +kernel

theorem store2_cnf : chkF S2 (cnf 2 84) 1 = true := by decide +kernel

theorem store2_last : lastEmpty S2 241503 = true := by decide +kernel

end E13Lrat
