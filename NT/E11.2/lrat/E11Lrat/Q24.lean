import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 197421..203408 (143606 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_197421 : steps S 197421 370 = true := by decide +kernel
theorem Q_197791 : steps S 197791 297 = true := by decide +kernel
theorem Q_198088 : steps S 198088 371 = true := by decide +kernel
theorem Q_198459 : steps S 198459 319 = true := by decide +kernel
theorem Q_198778 : steps S 198778 313 = true := by decide +kernel
theorem Q_199091 : steps S 199091 308 = true := by decide +kernel
theorem Q_199399 : steps S 199399 306 = true := by decide +kernel
theorem Q_199705 : steps S 199705 327 = true := by decide +kernel
theorem Q_200032 : steps S 200032 350 = true := by decide +kernel
theorem Q_200382 : steps S 200382 352 = true := by decide +kernel
theorem Q_200734 : steps S 200734 326 = true := by decide +kernel
theorem Q_201060 : steps S 201060 338 = true := by decide +kernel
theorem Q_201398 : steps S 201398 357 = true := by decide +kernel
theorem Q_201755 : steps S 201755 310 = true := by decide +kernel
theorem Q_202065 : steps S 202065 308 = true := by decide +kernel
theorem Q_202373 : steps S 202373 343 = true := by decide +kernel
theorem Q_202716 : steps S 202716 338 = true := by decide +kernel
theorem Q_203054 : steps S 203054 355 = true := by decide +kernel

end E11Lrat
