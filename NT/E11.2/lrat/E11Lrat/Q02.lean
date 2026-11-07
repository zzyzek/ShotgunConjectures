import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 62349..68441 (143721 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_62349 : steps S 62349 331 = true := by decide +kernel
theorem Q_62680 : steps S 62680 321 = true := by decide +kernel
theorem Q_63001 : steps S 63001 296 = true := by decide +kernel
theorem Q_63297 : steps S 63297 404 = true := by decide +kernel
theorem Q_63701 : steps S 63701 395 = true := by decide +kernel
theorem Q_64096 : steps S 64096 396 = true := by decide +kernel
theorem Q_64492 : steps S 64492 380 = true := by decide +kernel
theorem Q_64872 : steps S 64872 317 = true := by decide +kernel
theorem Q_65189 : steps S 65189 336 = true := by decide +kernel
theorem Q_65525 : steps S 65525 408 = true := by decide +kernel
theorem Q_65933 : steps S 65933 334 = true := by decide +kernel
theorem Q_66267 : steps S 66267 285 = true := by decide +kernel
theorem Q_66552 : steps S 66552 307 = true := by decide +kernel
theorem Q_66859 : steps S 66859 329 = true := by decide +kernel
theorem Q_67188 : steps S 67188 344 = true := by decide +kernel
theorem Q_67532 : steps S 67532 274 = true := by decide +kernel
theorem Q_67806 : steps S 67806 293 = true := by decide +kernel
theorem Q_68099 : steps S 68099 343 = true := by decide +kernel

end E11Lrat
