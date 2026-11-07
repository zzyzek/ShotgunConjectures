import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 98057..103823 (143644 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_98057 : steps S 98057 327 = true := by decide +kernel
theorem Q_98384 : steps S 98384 342 = true := by decide +kernel
theorem Q_98726 : steps S 98726 352 = true := by decide +kernel
theorem Q_99078 : steps S 99078 339 = true := by decide +kernel
theorem Q_99417 : steps S 99417 312 = true := by decide +kernel
theorem Q_99729 : steps S 99729 312 = true := by decide +kernel
theorem Q_100041 : steps S 100041 305 = true := by decide +kernel
theorem Q_100346 : steps S 100346 300 = true := by decide +kernel
theorem Q_100646 : steps S 100646 293 = true := by decide +kernel
theorem Q_100939 : steps S 100939 299 = true := by decide +kernel
theorem Q_101238 : steps S 101238 344 = true := by decide +kernel
theorem Q_101582 : steps S 101582 339 = true := by decide +kernel
theorem Q_101921 : steps S 101921 343 = true := by decide +kernel
theorem Q_102264 : steps S 102264 347 = true := by decide +kernel
theorem Q_102611 : steps S 102611 322 = true := by decide +kernel
theorem Q_102933 : steps S 102933 280 = true := by decide +kernel
theorem Q_103213 : steps S 103213 302 = true := by decide +kernel
theorem Q_103515 : steps S 103515 309 = true := by decide +kernel

end E11Lrat
