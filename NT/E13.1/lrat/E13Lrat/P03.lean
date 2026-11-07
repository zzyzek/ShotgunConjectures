import E13Lrat.Store4p

/-! # NT-E13.1, m = 4, 12 has colour 2: LRAT steps 81702..86509 (108532 hints), kernel-checked RUP -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem P_81702 : steps S4p 81702 327 = true := by decide +kernel
theorem P_82029 : steps S4p 82029 361 = true := by decide +kernel
theorem P_82390 : steps S4p 82390 390 = true := by decide +kernel
theorem P_82780 : steps S4p 82780 373 = true := by decide +kernel
theorem P_83153 : steps S4p 83153 355 = true := by decide +kernel
theorem P_83508 : steps S4p 83508 373 = true := by decide +kernel
theorem P_83881 : steps S4p 83881 381 = true := by decide +kernel
theorem P_84262 : steps S4p 84262 340 = true := by decide +kernel
theorem P_84602 : steps S4p 84602 293 = true := by decide +kernel
theorem P_84895 : steps S4p 84895 317 = true := by decide +kernel
theorem P_85212 : steps S4p 85212 280 = true := by decide +kernel
theorem P_85492 : steps S4p 85492 318 = true := by decide +kernel
theorem P_85810 : steps S4p 85810 294 = true := by decide +kernel
theorem P_86104 : steps S4p 86104 406 = true := by decide +kernel

end E13Lrat
