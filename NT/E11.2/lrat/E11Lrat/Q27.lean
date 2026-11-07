import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 215176..222359 (143686 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_215176 : steps S 215176 261 = true := by decide +kernel
theorem Q_215437 : steps S 215437 282 = true := by decide +kernel
theorem Q_215719 : steps S 215719 261 = true := by decide +kernel
theorem Q_215980 : steps S 215980 1437 = true := by decide +kernel
theorem Q_217417 : steps S 217417 365 = true := by decide +kernel
theorem Q_217782 : steps S 217782 362 = true := by decide +kernel
theorem Q_218144 : steps S 218144 339 = true := by decide +kernel
theorem Q_218483 : steps S 218483 328 = true := by decide +kernel
theorem Q_218811 : steps S 218811 324 = true := by decide +kernel
theorem Q_219135 : steps S 219135 392 = true := by decide +kernel
theorem Q_219527 : steps S 219527 365 = true := by decide +kernel
theorem Q_219892 : steps S 219892 373 = true := by decide +kernel
theorem Q_220265 : steps S 220265 360 = true := by decide +kernel
theorem Q_220625 : steps S 220625 331 = true := by decide +kernel
theorem Q_220956 : steps S 220956 365 = true := by decide +kernel
theorem Q_221321 : steps S 221321 358 = true := by decide +kernel
theorem Q_221679 : steps S 221679 358 = true := by decide +kernel
theorem Q_222037 : steps S 222037 323 = true := by decide +kernel

end E11Lrat
