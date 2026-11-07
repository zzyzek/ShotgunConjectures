import E11Lrat.Store

/-! # NT-E11.2, sigma(4, 4): 4 colours of [1, 171]: LRAT steps 170559..176579 (143690 hints), kernel-checked RUP -/

namespace E11Lrat

open OpenProblemsLib.LRAT

theorem Q_170559 : steps S 170559 318 = true := by decide +kernel
theorem Q_170877 : steps S 170877 299 = true := by decide +kernel
theorem Q_171176 : steps S 171176 309 = true := by decide +kernel
theorem Q_171485 : steps S 171485 292 = true := by decide +kernel
theorem Q_171777 : steps S 171777 330 = true := by decide +kernel
theorem Q_172107 : steps S 172107 330 = true := by decide +kernel
theorem Q_172437 : steps S 172437 328 = true := by decide +kernel
theorem Q_172765 : steps S 172765 503 = true := by decide +kernel
theorem Q_173268 : steps S 173268 341 = true := by decide +kernel
theorem Q_173609 : steps S 173609 302 = true := by decide +kernel
theorem Q_173911 : steps S 173911 295 = true := by decide +kernel
theorem Q_174206 : steps S 174206 293 = true := by decide +kernel
theorem Q_174499 : steps S 174499 336 = true := by decide +kernel
theorem Q_174835 : steps S 174835 338 = true := by decide +kernel
theorem Q_175173 : steps S 175173 347 = true := by decide +kernel
theorem Q_175520 : steps S 175520 347 = true := by decide +kernel
theorem Q_175867 : steps S 175867 366 = true := by decide +kernel
theorem Q_176233 : steps S 176233 347 = true := by decide +kernel

end E11Lrat
