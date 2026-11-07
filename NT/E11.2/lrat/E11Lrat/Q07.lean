import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 92297..98056 (143596 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_92297 : steps S 92297 299 = true := by decide +kernel
theorem Q_92596 : steps S 92596 379 = true := by decide +kernel
theorem Q_92975 : steps S 92975 343 = true := by decide +kernel
theorem Q_93318 : steps S 93318 304 = true := by decide +kernel
theorem Q_93622 : steps S 93622 282 = true := by decide +kernel
theorem Q_93904 : steps S 93904 321 = true := by decide +kernel
theorem Q_94225 : steps S 94225 290 = true := by decide +kernel
theorem Q_94515 : steps S 94515 290 = true := by decide +kernel
theorem Q_94805 : steps S 94805 270 = true := by decide +kernel
theorem Q_95075 : steps S 95075 279 = true := by decide +kernel
theorem Q_95354 : steps S 95354 279 = true := by decide +kernel
theorem Q_95633 : steps S 95633 338 = true := by decide +kernel
theorem Q_95971 : steps S 95971 338 = true := by decide +kernel
theorem Q_96309 : steps S 96309 359 = true := by decide +kernel
theorem Q_96668 : steps S 96668 357 = true := by decide +kernel
theorem Q_97025 : steps S 97025 370 = true := by decide +kernel
theorem Q_97395 : steps S 97395 345 = true := by decide +kernel
theorem Q_97740 : steps S 97740 317 = true := by decide +kernel

end E11Lrat
