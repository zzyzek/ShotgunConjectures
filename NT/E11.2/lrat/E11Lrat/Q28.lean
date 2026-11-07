import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 222360..228064 (143664 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_222360 : steps S 222360 359 = true := by decide +kernel
theorem Q_222719 : steps S 222719 329 = true := by decide +kernel
theorem Q_223048 : steps S 223048 324 = true := by decide +kernel
theorem Q_223372 : steps S 223372 325 = true := by decide +kernel
theorem Q_223697 : steps S 223697 291 = true := by decide +kernel
theorem Q_223988 : steps S 223988 282 = true := by decide +kernel
theorem Q_224270 : steps S 224270 290 = true := by decide +kernel
theorem Q_224560 : steps S 224560 326 = true := by decide +kernel
theorem Q_224886 : steps S 224886 297 = true := by decide +kernel
theorem Q_225183 : steps S 225183 305 = true := by decide +kernel
theorem Q_225488 : steps S 225488 269 = true := by decide +kernel
theorem Q_225757 : steps S 225757 275 = true := by decide +kernel
theorem Q_226032 : steps S 226032 361 = true := by decide +kernel
theorem Q_226393 : steps S 226393 338 = true := by decide +kernel
theorem Q_226731 : steps S 226731 367 = true := by decide +kernel
theorem Q_227098 : steps S 227098 325 = true := by decide +kernel
theorem Q_227423 : steps S 227423 337 = true := by decide +kernel
theorem Q_227760 : steps S 227760 305 = true := by decide +kernel

end E11Lrat
