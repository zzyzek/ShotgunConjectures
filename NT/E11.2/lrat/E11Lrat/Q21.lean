import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 176580..183201 (143681 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_176580 : steps S 176580 372 = true := by decide +kernel
theorem Q_176952 : steps S 176952 357 = true := by decide +kernel
theorem Q_177309 : steps S 177309 389 = true := by decide +kernel
theorem Q_177698 : steps S 177698 375 = true := by decide +kernel
theorem Q_178073 : steps S 178073 369 = true := by decide +kernel
theorem Q_178442 : steps S 178442 362 = true := by decide +kernel
theorem Q_178804 : steps S 178804 326 = true := by decide +kernel
theorem Q_179130 : steps S 179130 332 = true := by decide +kernel
theorem Q_179462 : steps S 179462 362 = true := by decide +kernel
theorem Q_179824 : steps S 179824 360 = true := by decide +kernel
theorem Q_180184 : steps S 180184 382 = true := by decide +kernel
theorem Q_180566 : steps S 180566 380 = true := by decide +kernel
theorem Q_180946 : steps S 180946 387 = true := by decide +kernel
theorem Q_181333 : steps S 181333 400 = true := by decide +kernel
theorem Q_181733 : steps S 181733 353 = true := by decide +kernel
theorem Q_182086 : steps S 182086 378 = true := by decide +kernel
theorem Q_182464 : steps S 182464 368 = true := by decide +kernel
theorem Q_182832 : steps S 182832 370 = true := by decide +kernel

end E11Lrat
