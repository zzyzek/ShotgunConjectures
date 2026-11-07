import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 109165..115018 (143693 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_109165 : steps S 109165 377 = true := by decide +kernel
theorem Q_109542 : steps S 109542 340 = true := by decide +kernel
theorem Q_109882 : steps S 109882 295 = true := by decide +kernel
theorem Q_110177 : steps S 110177 311 = true := by decide +kernel
theorem Q_110488 : steps S 110488 333 = true := by decide +kernel
theorem Q_110821 : steps S 110821 293 = true := by decide +kernel
theorem Q_111114 : steps S 111114 289 = true := by decide +kernel
theorem Q_111403 : steps S 111403 291 = true := by decide +kernel
theorem Q_111694 : steps S 111694 335 = true := by decide +kernel
theorem Q_112029 : steps S 112029 315 = true := by decide +kernel
theorem Q_112344 : steps S 112344 303 = true := by decide +kernel
theorem Q_112647 : steps S 112647 374 = true := by decide +kernel
theorem Q_113021 : steps S 113021 341 = true := by decide +kernel
theorem Q_113362 : steps S 113362 332 = true := by decide +kernel
theorem Q_113694 : steps S 113694 350 = true := by decide +kernel
theorem Q_114044 : steps S 114044 317 = true := by decide +kernel
theorem Q_114361 : steps S 114361 333 = true := by decide +kernel
theorem Q_114694 : steps S 114694 325 = true := by decide +kernel

end E11Lrat
