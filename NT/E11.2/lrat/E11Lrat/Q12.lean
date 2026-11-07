import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 121241..127427 (143634 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_121241 : steps S 121241 324 = true := by decide +kernel
theorem Q_121565 : steps S 121565 334 = true := by decide +kernel
theorem Q_121899 : steps S 121899 331 = true := by decide +kernel
theorem Q_122230 : steps S 122230 317 = true := by decide +kernel
theorem Q_122547 : steps S 122547 365 = true := by decide +kernel
theorem Q_122912 : steps S 122912 347 = true := by decide +kernel
theorem Q_123259 : steps S 123259 348 = true := by decide +kernel
theorem Q_123607 : steps S 123607 329 = true := by decide +kernel
theorem Q_123936 : steps S 123936 332 = true := by decide +kernel
theorem Q_124268 : steps S 124268 372 = true := by decide +kernel
theorem Q_124640 : steps S 124640 371 = true := by decide +kernel
theorem Q_125011 : steps S 125011 344 = true := by decide +kernel
theorem Q_125355 : steps S 125355 347 = true := by decide +kernel
theorem Q_125702 : steps S 125702 388 = true := by decide +kernel
theorem Q_126090 : steps S 126090 352 = true := by decide +kernel
theorem Q_126442 : steps S 126442 395 = true := by decide +kernel
theorem Q_126837 : steps S 126837 299 = true := by decide +kernel
theorem Q_127136 : steps S 127136 292 = true := by decide +kernel

end E11Lrat
