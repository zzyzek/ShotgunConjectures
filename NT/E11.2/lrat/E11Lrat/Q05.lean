import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 80789..86060 (143567 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_80789 : steps S 80789 293 = true := by decide +kernel
theorem Q_81082 : steps S 81082 300 = true := by decide +kernel
theorem Q_81382 : steps S 81382 316 = true := by decide +kernel
theorem Q_81698 : steps S 81698 301 = true := by decide +kernel
theorem Q_81999 : steps S 81999 344 = true := by decide +kernel
theorem Q_82343 : steps S 82343 327 = true := by decide +kernel
theorem Q_82670 : steps S 82670 305 = true := by decide +kernel
theorem Q_82975 : steps S 82975 303 = true := by decide +kernel
theorem Q_83278 : steps S 83278 290 = true := by decide +kernel
theorem Q_83568 : steps S 83568 285 = true := by decide +kernel
theorem Q_83853 : steps S 83853 257 = true := by decide +kernel
theorem Q_84110 : steps S 84110 300 = true := by decide +kernel
theorem Q_84410 : steps S 84410 273 = true := by decide +kernel
theorem Q_84683 : steps S 84683 294 = true := by decide +kernel
theorem Q_84977 : steps S 84977 263 = true := by decide +kernel
theorem Q_85240 : steps S 85240 252 = true := by decide +kernel
theorem Q_85492 : steps S 85492 275 = true := by decide +kernel
theorem Q_85767 : steps S 85767 294 = true := by decide +kernel

end E11Lrat
