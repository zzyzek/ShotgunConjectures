import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 145768..152302 (143719 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_145768 : steps S 145768 343 = true := by decide +kernel
theorem Q_146111 : steps S 146111 347 = true := by decide +kernel
theorem Q_146458 : steps S 146458 352 = true := by decide +kernel
theorem Q_146810 : steps S 146810 395 = true := by decide +kernel
theorem Q_147205 : steps S 147205 354 = true := by decide +kernel
theorem Q_147559 : steps S 147559 377 = true := by decide +kernel
theorem Q_147936 : steps S 147936 328 = true := by decide +kernel
theorem Q_148264 : steps S 148264 336 = true := by decide +kernel
theorem Q_148600 : steps S 148600 361 = true := by decide +kernel
theorem Q_148961 : steps S 148961 393 = true := by decide +kernel
theorem Q_149354 : steps S 149354 361 = true := by decide +kernel
theorem Q_149715 : steps S 149715 376 = true := by decide +kernel
theorem Q_150091 : steps S 150091 382 = true := by decide +kernel
theorem Q_150473 : steps S 150473 381 = true := by decide +kernel
theorem Q_150854 : steps S 150854 378 = true := by decide +kernel
theorem Q_151232 : steps S 151232 372 = true := by decide +kernel
theorem Q_151604 : steps S 151604 355 = true := by decide +kernel
theorem Q_151959 : steps S 151959 344 = true := by decide +kernel

end E11Lrat
