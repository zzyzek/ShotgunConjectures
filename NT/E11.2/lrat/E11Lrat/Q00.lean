import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 45896..54887 (143728 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_45896 : steps S 45896 3280 = true := by decide +kernel
theorem Q_49176 : steps S 49176 345 = true := by decide +kernel
theorem Q_49521 : steps S 49521 351 = true := by decide +kernel
theorem Q_49872 : steps S 49872 321 = true := by decide +kernel
theorem Q_50193 : steps S 50193 387 = true := by decide +kernel
theorem Q_50580 : steps S 50580 349 = true := by decide +kernel
theorem Q_50929 : steps S 50929 396 = true := by decide +kernel
theorem Q_51325 : steps S 51325 325 = true := by decide +kernel
theorem Q_51650 : steps S 51650 319 = true := by decide +kernel
theorem Q_51969 : steps S 51969 338 = true := by decide +kernel
theorem Q_52307 : steps S 52307 332 = true := by decide +kernel
theorem Q_52639 : steps S 52639 326 = true := by decide +kernel
theorem Q_52965 : steps S 52965 369 = true := by decide +kernel
theorem Q_53334 : steps S 53334 308 = true := by decide +kernel
theorem Q_53642 : steps S 53642 283 = true := by decide +kernel
theorem Q_53925 : steps S 53925 288 = true := by decide +kernel
theorem Q_54213 : steps S 54213 330 = true := by decide +kernel
theorem Q_54543 : steps S 54543 345 = true := by decide +kernel

end E11Lrat
