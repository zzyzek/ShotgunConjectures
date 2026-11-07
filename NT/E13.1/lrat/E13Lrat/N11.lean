import E13Lrat.Store4n

/-! # NT-E13.1, m = 4, 12 has not colour 2: LRAT steps 224682..225990 (31946 hints), kernel-checked RUP -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem N_224682 : steps S4n 224682 287 = true := by decide +kernel
theorem N_224969 : steps S4n 224969 250 = true := by decide +kernel
theorem N_225219 : steps S4n 225219 370 = true := by decide +kernel
theorem N_225589 : steps S4n 225589 402 = true := by decide +kernel

end E13Lrat
