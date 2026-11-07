import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 203409..209575 (143724 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_203409 : steps S 203409 358 = true := by decide +kernel
theorem Q_203767 : steps S 203767 336 = true := by decide +kernel
theorem Q_204103 : steps S 204103 366 = true := by decide +kernel
theorem Q_204469 : steps S 204469 326 = true := by decide +kernel
theorem Q_204795 : steps S 204795 367 = true := by decide +kernel
theorem Q_205162 : steps S 205162 343 = true := by decide +kernel
theorem Q_205505 : steps S 205505 332 = true := by decide +kernel
theorem Q_205837 : steps S 205837 336 = true := by decide +kernel
theorem Q_206173 : steps S 206173 322 = true := by decide +kernel
theorem Q_206495 : steps S 206495 322 = true := by decide +kernel
theorem Q_206817 : steps S 206817 336 = true := by decide +kernel
theorem Q_207153 : steps S 207153 367 = true := by decide +kernel
theorem Q_207520 : steps S 207520 325 = true := by decide +kernel
theorem Q_207845 : steps S 207845 358 = true := by decide +kernel
theorem Q_208203 : steps S 208203 382 = true := by decide +kernel
theorem Q_208585 : steps S 208585 357 = true := by decide +kernel
theorem Q_208942 : steps S 208942 322 = true := by decide +kernel
theorem Q_209264 : steps S 209264 312 = true := by decide +kernel

end E11Lrat
