import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 103824..109164 (143755 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_103824 : steps S 103824 270 = true := by decide +kernel
theorem Q_104094 : steps S 104094 321 = true := by decide +kernel
theorem Q_104415 : steps S 104415 340 = true := by decide +kernel
theorem Q_104755 : steps S 104755 325 = true := by decide +kernel
theorem Q_105080 : steps S 105080 312 = true := by decide +kernel
theorem Q_105392 : steps S 105392 349 = true := by decide +kernel
theorem Q_105741 : steps S 105741 318 = true := by decide +kernel
theorem Q_106059 : steps S 106059 298 = true := by decide +kernel
theorem Q_106357 : steps S 106357 313 = true := by decide +kernel
theorem Q_106670 : steps S 106670 285 = true := by decide +kernel
theorem Q_106955 : steps S 106955 225 = true := by decide +kernel
theorem Q_107180 : steps S 107180 227 = true := by decide +kernel
theorem Q_107407 : steps S 107407 271 = true := by decide +kernel
theorem Q_107678 : steps S 107678 326 = true := by decide +kernel
theorem Q_108004 : steps S 108004 323 = true := by decide +kernel
theorem Q_108327 : steps S 108327 264 = true := by decide +kernel
theorem Q_108591 : steps S 108591 288 = true := by decide +kernel
theorem Q_108879 : steps S 108879 286 = true := by decide +kernel

end E11Lrat
