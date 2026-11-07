import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 158307..164291 (143689 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_158307 : steps S 158307 340 = true := by decide +kernel
theorem Q_158647 : steps S 158647 331 = true := by decide +kernel
theorem Q_158978 : steps S 158978 310 = true := by decide +kernel
theorem Q_159288 : steps S 159288 301 = true := by decide +kernel
theorem Q_159589 : steps S 159589 326 = true := by decide +kernel
theorem Q_159915 : steps S 159915 339 = true := by decide +kernel
theorem Q_160254 : steps S 160254 331 = true := by decide +kernel
theorem Q_160585 : steps S 160585 371 = true := by decide +kernel
theorem Q_160956 : steps S 160956 378 = true := by decide +kernel
theorem Q_161334 : steps S 161334 336 = true := by decide +kernel
theorem Q_161670 : steps S 161670 356 = true := by decide +kernel
theorem Q_162026 : steps S 162026 391 = true := by decide +kernel
theorem Q_162417 : steps S 162417 289 = true := by decide +kernel
theorem Q_162706 : steps S 162706 273 = true := by decide +kernel
theorem Q_162979 : steps S 162979 306 = true := by decide +kernel
theorem Q_163285 : steps S 163285 339 = true := by decide +kernel
theorem Q_163624 : steps S 163624 330 = true := by decide +kernel
theorem Q_163954 : steps S 163954 338 = true := by decide +kernel

end E11Lrat
