import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 152303..158306 (143669 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_152303 : steps S 152303 376 = true := by decide +kernel
theorem Q_152679 : steps S 152679 356 = true := by decide +kernel
theorem Q_153035 : steps S 153035 356 = true := by decide +kernel
theorem Q_153391 : steps S 153391 349 = true := by decide +kernel
theorem Q_153740 : steps S 153740 352 = true := by decide +kernel
theorem Q_154092 : steps S 154092 337 = true := by decide +kernel
theorem Q_154429 : steps S 154429 339 = true := by decide +kernel
theorem Q_154768 : steps S 154768 349 = true := by decide +kernel
theorem Q_155117 : steps S 155117 330 = true := by decide +kernel
theorem Q_155447 : steps S 155447 314 = true := by decide +kernel
theorem Q_155761 : steps S 155761 294 = true := by decide +kernel
theorem Q_156055 : steps S 156055 282 = true := by decide +kernel
theorem Q_156337 : steps S 156337 320 = true := by decide +kernel
theorem Q_156657 : steps S 156657 328 = true := by decide +kernel
theorem Q_156985 : steps S 156985 325 = true := by decide +kernel
theorem Q_157310 : steps S 157310 323 = true := by decide +kernel
theorem Q_157633 : steps S 157633 323 = true := by decide +kernel
theorem Q_157956 : steps S 157956 351 = true := by decide +kernel

end E11Lrat
