import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 190953..197420 (143754 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_190953 : steps S 190953 333 = true := by decide +kernel
theorem Q_191286 : steps S 191286 315 = true := by decide +kernel
theorem Q_191601 : steps S 191601 337 = true := by decide +kernel
theorem Q_191938 : steps S 191938 398 = true := by decide +kernel
theorem Q_192336 : steps S 192336 367 = true := by decide +kernel
theorem Q_192703 : steps S 192703 385 = true := by decide +kernel
theorem Q_193088 : steps S 193088 355 = true := by decide +kernel
theorem Q_193443 : steps S 193443 351 = true := by decide +kernel
theorem Q_193794 : steps S 193794 352 = true := by decide +kernel
theorem Q_194146 : steps S 194146 376 = true := by decide +kernel
theorem Q_194522 : steps S 194522 376 = true := by decide +kernel
theorem Q_194898 : steps S 194898 382 = true := by decide +kernel
theorem Q_195280 : steps S 195280 361 = true := by decide +kernel
theorem Q_195641 : steps S 195641 348 = true := by decide +kernel
theorem Q_195989 : steps S 195989 367 = true := by decide +kernel
theorem Q_196356 : steps S 196356 351 = true := by decide +kernel
theorem Q_196707 : steps S 196707 350 = true := by decide +kernel
theorem Q_197057 : steps S 197057 364 = true := by decide +kernel

end E11Lrat
