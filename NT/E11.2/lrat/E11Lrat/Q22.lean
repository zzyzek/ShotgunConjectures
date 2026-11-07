import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 183202..190952 (143727 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_183202 : steps S 183202 360 = true := by decide +kernel
theorem Q_183562 : steps S 183562 359 = true := by decide +kernel
theorem Q_183921 : steps S 183921 345 = true := by decide +kernel
theorem Q_184266 : steps S 184266 322 = true := by decide +kernel
theorem Q_184588 : steps S 184588 373 = true := by decide +kernel
theorem Q_184961 : steps S 184961 1538 = true := by decide +kernel
theorem Q_186499 : steps S 186499 494 = true := by decide +kernel
theorem Q_186993 : steps S 186993 370 = true := by decide +kernel
theorem Q_187363 : steps S 187363 368 = true := by decide +kernel
theorem Q_187731 : steps S 187731 375 = true := by decide +kernel
theorem Q_188106 : steps S 188106 373 = true := by decide +kernel
theorem Q_188479 : steps S 188479 341 = true := by decide +kernel
theorem Q_188820 : steps S 188820 344 = true := by decide +kernel
theorem Q_189164 : steps S 189164 341 = true := by decide +kernel
theorem Q_189505 : steps S 189505 356 = true := by decide +kernel
theorem Q_189861 : steps S 189861 346 = true := by decide +kernel
theorem Q_190207 : steps S 190207 386 = true := by decide +kernel
theorem Q_190593 : steps S 190593 360 = true := by decide +kernel

end E11Lrat
