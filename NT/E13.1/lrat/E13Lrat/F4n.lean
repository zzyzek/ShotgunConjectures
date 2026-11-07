import E13Lrat.Cnf
import E13Lrat.Store4n

/-! # NT-E13.1, m = 4: the store `S4n` begins with `cnf 4 164 ++ [[71]]` and ends with the empty clause -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem cnf4n_length : (cnf 4 164 ++ [[71]]).length = 25288 := by decide +kernel

theorem store4n_cnf : chkF S4n (cnf 4 164 ++ [[71]]) 1 = true := by decide +kernel

theorem store4n_last : lastEmpty S4n 225990 = true := by decide +kernel

end E13Lrat
