import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 209576..215175 (143585 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_209576 : steps S 209576 331 = true := by decide +kernel
theorem Q_209907 : steps S 209907 319 = true := by decide +kernel
theorem Q_210226 : steps S 210226 368 = true := by decide +kernel
theorem Q_210594 : steps S 210594 332 = true := by decide +kernel
theorem Q_210926 : steps S 210926 322 = true := by decide +kernel
theorem Q_211248 : steps S 211248 301 = true := by decide +kernel
theorem Q_211549 : steps S 211549 355 = true := by decide +kernel
theorem Q_211904 : steps S 211904 315 = true := by decide +kernel
theorem Q_212219 : steps S 212219 318 = true := by decide +kernel
theorem Q_212537 : steps S 212537 295 = true := by decide +kernel
theorem Q_212832 : steps S 212832 286 = true := by decide +kernel
theorem Q_213118 : steps S 213118 277 = true := by decide +kernel
theorem Q_213395 : steps S 213395 302 = true := by decide +kernel
theorem Q_213697 : steps S 213697 299 = true := by decide +kernel
theorem Q_213996 : steps S 213996 281 = true := by decide +kernel
theorem Q_214277 : steps S 214277 325 = true := by decide +kernel
theorem Q_214602 : steps S 214602 300 = true := by decide +kernel
theorem Q_214902 : steps S 214902 274 = true := by decide +kernel

end E11Lrat
