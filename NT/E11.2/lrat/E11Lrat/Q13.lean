import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 127428..133287 (143706 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_127428 : steps S 127428 315 = true := by decide +kernel
theorem Q_127743 : steps S 127743 278 = true := by decide +kernel
theorem Q_128021 : steps S 128021 317 = true := by decide +kernel
theorem Q_128338 : steps S 128338 346 = true := by decide +kernel
theorem Q_128684 : steps S 128684 343 = true := by decide +kernel
theorem Q_129027 : steps S 129027 337 = true := by decide +kernel
theorem Q_129364 : steps S 129364 336 = true := by decide +kernel
theorem Q_129700 : steps S 129700 312 = true := by decide +kernel
theorem Q_130012 : steps S 130012 308 = true := by decide +kernel
theorem Q_130320 : steps S 130320 312 = true := by decide +kernel
theorem Q_130632 : steps S 130632 302 = true := by decide +kernel
theorem Q_130934 : steps S 130934 372 = true := by decide +kernel
theorem Q_131306 : steps S 131306 414 = true := by decide +kernel
theorem Q_131720 : steps S 131720 326 = true := by decide +kernel
theorem Q_132046 : steps S 132046 312 = true := by decide +kernel
theorem Q_132358 : steps S 132358 332 = true := by decide +kernel
theorem Q_132690 : steps S 132690 322 = true := by decide +kernel
theorem Q_133012 : steps S 133012 276 = true := by decide +kernel

end E11Lrat
