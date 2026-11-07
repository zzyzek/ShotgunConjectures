import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 68442..74938 (143781 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_68442 : steps S 68442 366 = true := by decide +kernel
theorem Q_68808 : steps S 68808 310 = true := by decide +kernel
theorem Q_69118 : steps S 69118 367 = true := by decide +kernel
theorem Q_69485 : steps S 69485 334 = true := by decide +kernel
theorem Q_69819 : steps S 69819 375 = true := by decide +kernel
theorem Q_70194 : steps S 70194 383 = true := by decide +kernel
theorem Q_70577 : steps S 70577 364 = true := by decide +kernel
theorem Q_70941 : steps S 70941 368 = true := by decide +kernel
theorem Q_71309 : steps S 71309 461 = true := by decide +kernel
theorem Q_71770 : steps S 71770 440 = true := by decide +kernel
theorem Q_72210 : steps S 72210 349 = true := by decide +kernel
theorem Q_72559 : steps S 72559 345 = true := by decide +kernel
theorem Q_72904 : steps S 72904 394 = true := by decide +kernel
theorem Q_73298 : steps S 73298 424 = true := by decide +kernel
theorem Q_73722 : steps S 73722 302 = true := by decide +kernel
theorem Q_74024 : steps S 74024 308 = true := by decide +kernel
theorem Q_74332 : steps S 74332 295 = true := by decide +kernel
theorem Q_74627 : steps S 74627 312 = true := by decide +kernel

end E11Lrat
