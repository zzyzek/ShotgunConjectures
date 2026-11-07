import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 54888..62348 (143690 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_54888 : steps S 54888 352 = true := by decide +kernel
theorem Q_55240 : steps S 55240 361 = true := by decide +kernel
theorem Q_55601 : steps S 55601 367 = true := by decide +kernel
theorem Q_55968 : steps S 55968 1775 = true := by decide +kernel
theorem Q_57743 : steps S 57743 340 = true := by decide +kernel
theorem Q_58083 : steps S 58083 417 = true := by decide +kernel
theorem Q_58500 : steps S 58500 296 = true := by decide +kernel
theorem Q_58796 : steps S 58796 329 = true := by decide +kernel
theorem Q_59125 : steps S 59125 316 = true := by decide +kernel
theorem Q_59441 : steps S 59441 294 = true := by decide +kernel
theorem Q_59735 : steps S 59735 286 = true := by decide +kernel
theorem Q_60021 : steps S 60021 296 = true := by decide +kernel
theorem Q_60317 : steps S 60317 378 = true := by decide +kernel
theorem Q_60695 : steps S 60695 339 = true := by decide +kernel
theorem Q_61034 : steps S 61034 313 = true := by decide +kernel
theorem Q_61347 : steps S 61347 323 = true := by decide +kernel
theorem Q_61670 : steps S 61670 311 = true := by decide +kernel
theorem Q_61981 : steps S 61981 368 = true := by decide +kernel

end E11Lrat
