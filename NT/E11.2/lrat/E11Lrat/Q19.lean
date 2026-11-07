import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 164292..170558 (143730 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_164292 : steps S 164292 402 = true := by decide +kernel
theorem Q_164694 : steps S 164694 350 = true := by decide +kernel
theorem Q_165044 : steps S 165044 325 = true := by decide +kernel
theorem Q_165369 : steps S 165369 303 = true := by decide +kernel
theorem Q_165672 : steps S 165672 347 = true := by decide +kernel
theorem Q_166019 : steps S 166019 349 = true := by decide +kernel
theorem Q_166368 : steps S 166368 367 = true := by decide +kernel
theorem Q_166735 : steps S 166735 338 = true := by decide +kernel
theorem Q_167073 : steps S 167073 371 = true := by decide +kernel
theorem Q_167444 : steps S 167444 382 = true := by decide +kernel
theorem Q_167826 : steps S 167826 364 = true := by decide +kernel
theorem Q_168190 : steps S 168190 334 = true := by decide +kernel
theorem Q_168524 : steps S 168524 362 = true := by decide +kernel
theorem Q_168886 : steps S 168886 352 = true := by decide +kernel
theorem Q_169238 : steps S 169238 333 = true := by decide +kernel
theorem Q_169571 : steps S 169571 337 = true := by decide +kernel
theorem Q_169908 : steps S 169908 356 = true := by decide +kernel
theorem Q_170264 : steps S 170264 295 = true := by decide +kernel

end E11Lrat
