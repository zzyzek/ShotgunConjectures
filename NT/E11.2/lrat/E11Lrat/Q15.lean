import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 139322..145767 (143682 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_139322 : steps S 139322 348 = true := by decide +kernel
theorem Q_139670 : steps S 139670 359 = true := by decide +kernel
theorem Q_140029 : steps S 140029 364 = true := by decide +kernel
theorem Q_140393 : steps S 140393 347 = true := by decide +kernel
theorem Q_140740 : steps S 140740 349 = true := by decide +kernel
theorem Q_141089 : steps S 141089 348 = true := by decide +kernel
theorem Q_141437 : steps S 141437 361 = true := by decide +kernel
theorem Q_141798 : steps S 141798 348 = true := by decide +kernel
theorem Q_142146 : steps S 142146 341 = true := by decide +kernel
theorem Q_142487 : steps S 142487 376 = true := by decide +kernel
theorem Q_142863 : steps S 142863 357 = true := by decide +kernel
theorem Q_143220 : steps S 143220 397 = true := by decide +kernel
theorem Q_143617 : steps S 143617 315 = true := by decide +kernel
theorem Q_143932 : steps S 143932 386 = true := by decide +kernel
theorem Q_144318 : steps S 144318 350 = true := by decide +kernel
theorem Q_144668 : steps S 144668 395 = true := by decide +kernel
theorem Q_145063 : steps S 145063 350 = true := by decide +kernel
theorem Q_145413 : steps S 145413 355 = true := by decide +kernel

end E11Lrat
