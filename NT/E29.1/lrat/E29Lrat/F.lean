import E29Lrat.Cnf
import E29Lrat.Store

/-! # NT-E29.1: the store begins with `cnf 3150` (kernel check) -/

namespace E29Lrat

open OpenProblemsLib.LRAT

theorem cnf_length : (cnf 3150).length = 16378 := by decide +kernel

theorem store_cnf : chkF S (cnf 3150) 1 = true := by decide +kernel

theorem store_last : lastEmpty S 143080 = true := by decide +kernel

end E29Lrat
