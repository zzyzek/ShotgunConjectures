import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 86061..92296 (143654 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_86061 : steps S 86061 316 = true := by decide +kernel
theorem Q_86377 : steps S 86377 386 = true := by decide +kernel
theorem Q_86763 : steps S 86763 387 = true := by decide +kernel
theorem Q_87150 : steps S 87150 353 = true := by decide +kernel
theorem Q_87503 : steps S 87503 348 = true := by decide +kernel
theorem Q_87851 : steps S 87851 339 = true := by decide +kernel
theorem Q_88190 : steps S 88190 338 = true := by decide +kernel
theorem Q_88528 : steps S 88528 335 = true := by decide +kernel
theorem Q_88863 : steps S 88863 337 = true := by decide +kernel
theorem Q_89200 : steps S 89200 319 = true := by decide +kernel
theorem Q_89519 : steps S 89519 379 = true := by decide +kernel
theorem Q_89898 : steps S 89898 327 = true := by decide +kernel
theorem Q_90225 : steps S 90225 336 = true := by decide +kernel
theorem Q_90561 : steps S 90561 342 = true := by decide +kernel
theorem Q_90903 : steps S 90903 346 = true := by decide +kernel
theorem Q_91249 : steps S 91249 393 = true := by decide +kernel
theorem Q_91642 : steps S 91642 346 = true := by decide +kernel
theorem Q_91988 : steps S 91988 309 = true := by decide +kernel

end E11Lrat
