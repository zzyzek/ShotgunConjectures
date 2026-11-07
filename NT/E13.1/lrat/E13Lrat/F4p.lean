import E13Lrat.Cnf
import E13Lrat.Store4p

/-! # NT-E13.1, m = 4: the store `S4p` begins with `cnf 4 164 ++ [[70]]` and ends with the empty clause -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem cnf4p_length : (cnf 4 164 ++ [[70]]).length = 25288 := by decide +kernel

theorem store4p_cnf : chkF S4p (cnf 4 164 ++ [[70]]) 1 = true := by decide +kernel

theorem store4p_last : lastEmpty S4p 86509 = true := by decide +kernel

end E13Lrat
