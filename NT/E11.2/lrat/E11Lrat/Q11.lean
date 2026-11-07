import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 115019..121240 (143699 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_115019 : steps S 115019 340 = true := by decide +kernel
theorem Q_115359 : steps S 115359 328 = true := by decide +kernel
theorem Q_115687 : steps S 115687 309 = true := by decide +kernel
theorem Q_115996 : steps S 115996 342 = true := by decide +kernel
theorem Q_116338 : steps S 116338 342 = true := by decide +kernel
theorem Q_116680 : steps S 116680 399 = true := by decide +kernel
theorem Q_117079 : steps S 117079 350 = true := by decide +kernel
theorem Q_117429 : steps S 117429 315 = true := by decide +kernel
theorem Q_117744 : steps S 117744 416 = true := by decide +kernel
theorem Q_118160 : steps S 118160 355 = true := by decide +kernel
theorem Q_118515 : steps S 118515 358 = true := by decide +kernel
theorem Q_118873 : steps S 118873 351 = true := by decide +kernel
theorem Q_119224 : steps S 119224 324 = true := by decide +kernel
theorem Q_119548 : steps S 119548 315 = true := by decide +kernel
theorem Q_119863 : steps S 119863 345 = true := by decide +kernel
theorem Q_120208 : steps S 120208 361 = true := by decide +kernel
theorem Q_120569 : steps S 120569 331 = true := by decide +kernel
theorem Q_120900 : steps S 120900 341 = true := by decide +kernel

end E11Lrat
