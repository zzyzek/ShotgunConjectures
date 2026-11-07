import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 228065..233407 (92846 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_228065 : steps S 228065 772 = true := by decide +kernel
theorem Q_228837 : steps S 228837 361 = true := by decide +kernel
theorem Q_229198 : steps S 229198 335 = true := by decide +kernel
theorem Q_229533 : steps S 229533 322 = true := by decide +kernel
theorem Q_229855 : steps S 229855 317 = true := by decide +kernel
theorem Q_230172 : steps S 230172 364 = true := by decide +kernel
theorem Q_230536 : steps S 230536 351 = true := by decide +kernel
theorem Q_230887 : steps S 230887 892 = true := by decide +kernel
theorem Q_231779 : steps S 231779 710 = true := by decide +kernel
theorem Q_232489 : steps S 232489 345 = true := by decide +kernel
theorem Q_232834 : steps S 232834 353 = true := by decide +kernel
theorem Q_233187 : steps S 233187 221 = true := by decide +kernel

end E11Lrat
