import OpenProblemsLib
import Mathlib.NumberTheory.Pell

/-
NT-B16.6 (Mathlib). Guy B16 (Myerson): the Ankeny–Artin–Chowla property p ∤ u, (t, u) the
least positive solution of t² - p u² = 1, fails for non-prime d; are 46 and 430 the two
smallest counterexamples? README reading: d ranges over non-square, non-prime integers > 1,
(t, u) the least positive solution of t² - d u² = 1. README result: true; among
non-square non-prime d ≤ 430, d ∣ u only for d = 46 ((t, u) = (24335, 3588)) and
d = 430 ((t, u) = (2862251, 138030)).

Main theorem `B16_6_main`: for every natural d with 2 ≤ d ≤ 430, d not a square, d not prime,
and every fundamental solution a of the Pell equation x² - d y² = 1 (Mathlib
`Pell.Solution₁`, `Pell.IsFundamental`: x > 1, y > 0, least x): d ∣ a.y ↔ d = 46 ∨ d = 430.
`B16_6_values`: the fundamental solutions for 46 and 430 are (24335, 3588), (2862251, 138030).

Proof. d = 46, 430: the given solutions are fundamental, by a kernel check that 1 + d y² is
not a perfect square for 0 < y < u (self-certifying integer square roots s with
s² < 1 + d y² < (s+1)²); Mathlib's uniqueness `IsFundamental.subsingleton`.
Other d: a table gives one solution (t, u) with d ∤ u (from continued fractions, computed
outside and checked by the kernel); by Mathlib `IsFundamental.eq_pow_of_nonneg` it is a
power aⁿ of the fundamental solution, and a.y ∣ (aⁿ).y, so d ∤ a.y. A kernel check shows every
d ≤ 430 is a square (root < 22), prime (trial division), 46, 430, or in the table.

Outside Lean: nothing.
-/

open Pell OpenProblemsLib.ArithFactor

theorem y_dvd_pow {d : ℤ} (a : Solution₁ d) : ∀ n : ℕ, a.y ∣ (a ^ n).y
  | 0 => by simp [Solution₁.y_one]
  | n + 1 => by
    rw [pow_succ, Solution₁.y_mul]
    exact dvd_add (dvd_mul_left _ _) (Dvd.dvd.mul_right (y_dvd_pow a n) _)

theorem not_dvd_of_sol (d : ℕ) (a : Solution₁ (d : ℤ)) (ha : IsFundamental a) (t u : ℕ)
    (h : t * t = d * u * u + 1) (hu : u % d ≠ 0) : ¬ (d : ℤ) ∣ a.y := by
  have hprop : (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 1 := by
    have : ((t * t : ℕ) : ℤ) = ((d * u * u + 1 : ℕ) : ℤ) := by rw [h]
    push_cast at this; linear_combination this
  set b := Solution₁.mk (t : ℤ) (u : ℤ) hprop
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at h
    · exact h0
  have hbx : 0 < b.x := by simp [b, Solution₁.x_mk]; exact ht
  have hby : 0 ≤ b.y := by simp [b, Solution₁.y_mk]
  obtain ⟨n, hn⟩ := ha.eq_pow_of_nonneg hbx hby
  intro hd
  have h1 : (d : ℤ) ∣ (u : ℤ) := by
    have : b.y = (u : ℤ) := Solution₁.y_mk _ _ _
    rw [← this, hn]
    exact hd.trans (y_dvd_pow a n)
  exact hu (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp h1))

/-- Newton iteration for ⌊√n⌋ from guess g, with fuel (result is checked, not trusted). -/
def isqrtF : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, n, g => if (g + n / g) / 2 < g then isqrtF f n ((g + n / g) / 2) else g

/-- `P (lo + i)` for all i < len, by binary splitting (kernel-friendly depth). -/
def rangeAll (P : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, len => (List.range len).all (fun i => P (lo + i))
  | f + 1, lo, len => if len ≤ 1 then (len == 0 || P lo) else
      rangeAll P f lo (len / 2) && rangeAll P f (lo + len / 2) (len - len / 2)

theorem rangeAll_spec (P : ℕ → Bool) : ∀ f lo len, rangeAll P f lo len = true →
    ∀ i < len, P (lo + i) = true
  | 0, lo, len, h, i, hi => by
    simp only [rangeAll, List.all_eq_true, List.mem_range] at h; exact h i hi
  | f + 1, lo, len, h, i, hi => by
    unfold rangeAll at h
    split_ifs at h with h1
    · simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · omega
      · have : i = 0 := by omega
        subst this; simpa using h
    · simp only [Bool.and_eq_true] at h
      rcases Nat.lt_or_ge i (len / 2) with h2 | h2
      · exact rangeAll_spec P f lo (len / 2) h.1 i h2
      · have := rangeAll_spec P f (lo + len / 2) (len - len / 2) h.2 (i - len / 2) (by omega)
        rw [show lo + len / 2 + (i - len / 2) = lo + i by omega] at this
        exact this

/-- 1 + d y² is not a perfect square (guess c·y with c² > d), checked via s² < m < (s+1)². -/
def noSqAt (d c y : ℕ) : Bool :=
  let m := d * y * y + 1
  let s := isqrtF 30 m (c * y)
  s * s < m && m < (s + 1) * (s + 1)

theorem fund_of_check (d T U c : ℕ) (hT : T * T = d * U * U + 1) (hU : 0 < U) (hT1 : 1 < T)
    (hchk : ∀ y, 1 ≤ y → y < U → noSqAt d c y = true) (a : Solution₁ (d : ℤ)) (ha : IsFundamental a) :
    a.x = T ∧ a.y = U := by
  have hprop : (T : ℤ) ^ 2 - d * (U : ℤ) ^ 2 = 1 := by
    have : ((T * T : ℕ) : ℤ) = ((d * U * U + 1 : ℕ) : ℤ) := by rw [hT]
    push_cast at this; linear_combination this
  set b := Solution₁.mk (T : ℤ) (U : ℤ) hprop
  have hbx : b.x = T := Solution₁.x_mk _ _ _
  have hby : b.y = U := Solution₁.y_mk _ _ _
  have hb : IsFundamental b := by
    refine ⟨by rw [hbx]; exact_mod_cast hT1, by rw [hby]; exact_mod_cast hU, ?_⟩
    intro e he
    rw [hbx]
    by_contra hlt
    push Not at hlt
    set x := e.x.toNat
    set y := e.y.natAbs
    have hx : (x : ℤ) = e.x := Int.toNat_of_nonneg (by omega)
    have hy : (y : ℤ) ^ 2 = e.y ^ 2 := Int.natAbs_sq e.y
    have hxy : x * x = d * y * y + 1 := by
      have := e.prop_x
      have : ((x * x : ℕ) : ℤ) = ((d * y * y + 1 : ℕ) : ℤ) := by
        push_cast; rw [hx]; nlinarith [hy]
      exact_mod_cast this
    have hx1 : 1 < x := by omega
    have hxT : x < T := by omega
    have hyU : y < U := by
      by_contra hc
      push Not at hc
      have : d * U * U ≤ d * y * y := Nat.mul_le_mul (Nat.mul_le_mul_left _ hc) hc
      have : T * T ≤ x * x := by omega
      exact absurd (Nat.mul_self_le_mul_self_iff.mp this) (by omega)
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at hxy; simp at hxy
      have : x ≤ 1 := by nlinarith
      omega
    have := hchk y (by omega) hyU
    simp only [noSqAt, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨h1, h2⟩ := this
    rw [← hxy] at h1 h2
    have := Nat.mul_self_lt_mul_self_iff.mp h1
    have := Nat.mul_self_lt_mul_self_iff.mp h2
    omega
  have := hb.subsingleton ha
  rw [← this]
  exact ⟨hbx, hby⟩

def table : List (ℕ × ℕ × ℕ) :=
  [(6, 5, 2),
   (8, 3, 1),
   (10, 19, 6),
   (12, 7, 2),
   (14, 15, 4),
   (15, 4, 1),
   (18, 17, 4),
   (20, 9, 2),
   (21, 55, 12),
   (22, 197, 42),
   (24, 5, 1),
   (26, 51, 10),
   (27, 26, 5),
   (28, 127, 24),
   (30, 11, 2),
   (32, 17, 3),
   (33, 23, 4),
   (34, 35, 6),
   (35, 6, 1),
   (38, 37, 6),
   (39, 25, 4),
   (40, 19, 3),
   (42, 13, 2),
   (44, 199, 30),
   (45, 161, 24),
   (48, 7, 1),
   (50, 99, 14),
   (51, 50, 7),
   (52, 649, 90),
   (54, 485, 66),
   (55, 89, 12),
   (56, 15, 2),
   (57, 151, 20),
   (58, 19603, 2574),
   (60, 31, 4),
   (62, 63, 8),
   (63, 8, 1),
   (65, 129, 16),
   (66, 65, 8),
   (68, 33, 4),
   (69, 7775, 936),
   (70, 251, 30),
   (72, 17, 2),
   (74, 3699, 430),
   (75, 26, 3),
   (76, 57799, 6630),
   (77, 351, 40),
   (78, 53, 6),
   (80, 9, 1),
   (82, 163, 18),
   (84, 55, 6),
   (85, 285769, 30996),
   (86, 10405, 1122),
   (87, 28, 3),
   (88, 197, 21),
   (90, 19, 2),
   (91, 1574, 165),
   (92, 1151, 120),
   (93, 12151, 1260),
   (94, 2143295, 221064),
   (95, 39, 4),
   (96, 49, 5),
   (98, 99, 10),
   (99, 10, 1),
   (102, 101, 10),
   (104, 51, 5),
   (105, 41, 4),
   (106, 32080051, 3115890),
   (108, 1351, 130),
   (110, 21, 2),
   (111, 295, 28),
   (112, 127, 12),
   (114, 1025, 96),
   (115, 1126, 105),
   (116, 9801, 910),
   (117, 649, 60),
   (118, 306917, 28254),
   (119, 120, 11),
   (120, 11, 1),
   (122, 243, 22),
   (123, 122, 11),
   (124, 4620799, 414960),
   (125, 930249, 83204),
   (126, 449, 40),
   (128, 577, 51),
   (129, 16855, 1484),
   (130, 6499, 570),
   (132, 23, 2),
   (133, 2588599, 224460),
   (134, 145925, 12606),
   (135, 244, 21),
   (136, 35, 3),
   (138, 47, 4),
   (140, 71, 6),
   (141, 95, 8),
   (142, 143, 12),
   (143, 12, 1),
   (145, 289, 24),
   (146, 145, 12),
   (147, 97, 8),
   (148, 73, 6),
   (150, 49, 4),
   (152, 37, 3),
   (153, 2177, 176),
   (154, 21295, 1716),
   (155, 249, 20),
   (156, 25, 2),
   (158, 7743, 616),
   (159, 1324, 105),
   (160, 721, 57),
   (161, 11775, 928),
   (162, 19601, 1540),
   (164, 2049, 160),
   (165, 1079, 84),
   (166, 1700902565, 132015642),
   (168, 13, 1),
   (170, 339, 26),
   (171, 170, 13),
   (172, 24248647, 1848942),
   (174, 1451, 110),
   (175, 2024, 153),
   (176, 199, 15),
   (177, 62423, 4692),
   (178, 1601, 120),
   (180, 161, 12),
   (182, 27, 2),
   (183, 487, 36),
   (184, 24335, 1794),
   (185, 9249, 680),
   (186, 7501, 550),
   (187, 1682, 123),
   (188, 4607, 336),
   (189, 55, 4),
   (190, 52021, 3774),
   (192, 97, 7),
   (194, 195, 14),
   (195, 14, 1),
   (198, 197, 14),
   (200, 99, 7),
   (201, 515095, 36332),
   (202, 19731763, 1388322),
   (203, 57, 4),
   (204, 4999, 350),
   (205, 39689, 2772),
   (206, 59535, 4148),
   (207, 1151, 80),
   (208, 649, 45),
   (209, 46551, 3220),
   (210, 29, 2),
   (212, 66249, 4550),
   (213, 194399, 13320),
   (214, 695359189925, 47533775646),
   (215, 44, 3),
   (216, 485, 33),
   (217, 3844063, 260952),
   (218, 126003, 8534),
   (219, 74, 5),
   (220, 89, 6),
   (221, 1665, 112),
   (222, 149, 10),
   (224, 15, 1),
   (226, 451, 30),
   (228, 151, 10),
   (230, 91, 6),
   (231, 76, 5),
   (232, 19603, 1287),
   (234, 5201, 340),
   (235, 46, 3),
   (236, 561799, 36570),
   (237, 228151, 14820),
   (238, 11663, 756),
   (240, 31, 2),
   (242, 19601, 1260),
   (243, 70226, 4505),
   (244, 1766319049, 113076990),
   (245, 51841, 3312),
   (246, 88805, 5662),
   (247, 85292, 5427),
   (248, 63, 4),
   (249, 8553815, 542076),
   (250, 39480499, 2496966),
   (252, 127, 8),
   (253, 3222617399, 202604220),
   (254, 255, 16),
   (255, 16, 1),
   (258, 257, 16),
   (259, 847225, 52644),
   (260, 129, 8),
   (261, 192119201, 11891880),
   (262, 104980517, 6485718),
   (264, 65, 4),
   (265, 73738369, 4529712),
   (266, 685, 42),
   (267, 2402, 147),
   (268, 4771081927, 291440214),
   (270, 5291, 322),
   (272, 33, 2),
   (273, 727, 44),
   (274, 3959299, 239190),
   (275, 199, 12),
   (276, 7775, 468),
   (278, 2501, 150),
   (279, 1520, 91),
   (280, 251, 15),
   (282, 2351, 140),
   (284, 24220799, 1437240),
   (285, 2431, 144),
   (286, 561835, 33222),
   (287, 288, 17),
   (288, 17, 1),
   (290, 579, 34),
   (291, 290, 17),
   (292, 2281249, 133500),
   (294, 4801, 280),
   (295, 2024999, 117900),
   (296, 3699, 215),
   (297, 48599, 2820),
   (298, 335473872499, 19433479650),
   (299, 415, 24),
   (300, 1351, 78),
   (301, 5883392537695, 339113108232),
   (302, 4276623, 246092),
   (303, 2524, 145),
   (304, 57799, 3315),
   (305, 489, 28),
   (306, 35, 2),
   (308, 351, 20),
   (309, 64202725495, 3652365444),
   (310, 848719, 48204),
   (312, 53, 3),
   (314, 392499, 22150),
   (315, 71, 4),
   (316, 12799, 720),
   (318, 107, 6),
   (319, 12901780, 722361),
   (320, 161, 9),
   (321, 215, 12),
   (322, 323, 18),
   (323, 18, 1),
   (325, 649, 36),
   (326, 325, 18),
   (327, 217, 12),
   (328, 163, 9),
   (329, 2376415, 131016),
   (330, 109, 6),
   (332, 13447, 738),
   (333, 73, 4),
   (334, 63804373719695, 3491219999244),
   (335, 604, 33),
   (336, 55, 3),
   (338, 114243, 6214),
   (339, 97970, 5321),
   (340, 285769, 15498),
   (341, 10626551, 575460),
   (342, 37, 2),
   (343, 130576328, 7050459),
   (344, 10405, 561),
   (345, 6761, 364),
   (346, 17299, 930),
   (348, 1567, 84),
   (350, 449, 24),
   (351, 62425, 3332),
   (352, 77617, 4137),
   (354, 258065, 13716),
   (355, 954809, 50676),
   (356, 500001, 26500),
   (357, 3401, 180),
   (358, 176579805797, 9332532726),
   (360, 19, 1),
   (362, 723, 38),
   (363, 362, 19),
   (364, 4954951, 259710),
   (365, 23915529, 1251796),
   (366, 907925, 47458),
   (368, 1151, 60),
   (369, 8396801, 437120),
   (370, 213859, 11118),
   (371, 1695, 88),
   (372, 12151, 630),
   (374, 3365, 174),
   (375, 15124, 781),
   (376, 2143295, 110532),
   (377, 233, 12),
   (378, 8749, 450),
   (380, 39, 2),
   (381, 1015, 52),
   (382, 164998439999, 8442054600),
   (384, 4801, 245),
   (385, 95831, 4884),
   (386, 111555, 5678),
   (387, 3482, 177),
   (388, 62809633, 3188676),
   (390, 79, 4),
   (391, 7338680, 371133),
   (392, 99, 5),
   (393, 46437143, 2342444),
   (394, 312086396361222451, 15722685507826110),
   (395, 159, 8),
   (396, 199, 10),
   (398, 399, 20),
   (399, 20, 1),
   (402, 401, 20),
   (403, 669878, 33369),
   (404, 201, 10),
   (405, 161, 8),
   (406, 59468095, 2951352),
   (407, 2663, 132),
   (408, 101, 5),
   (410, 81, 4),
   (411, 49730, 2453),
   (412, 103537981567, 5100950232),
   (413, 113399, 5580),
   (414, 24335, 1196),
   (415, 18412804, 903849),
   (416, 5201, 255),
   (417, 85322647, 4178268),
   (418, 33857, 1656),
   (420, 41, 2),
   (422, 7022501, 341850),
   (423, 4607, 224),
   (424, 32080051, 1557945),
   (425, 143649, 6968),
   (426, 88751, 4300),
   (427, 62, 3),
   (428, 1850887, 89466),
   (429, 1524095, 73584)]

def sqCheck (d : ℕ) : Bool := (List.range 22).any (fun r => r * r == d)

def covers (d : ℕ) : Bool :=
  sqCheck d || primeTD d || d == 46 || d == 430 ||
    table.any (fun e => e.1 == d && e.2.1 * e.2.1 == d * e.2.2 * e.2.2 + 1 && e.2.2 % d != 0)

theorem covers_all : (List.range 431).all (fun d => d < 2 || covers d) = true := by
  decide +kernel

theorem chunks (d c U : ℕ) (cs : List (ℕ × ℕ))
    (hcov : (List.range U).all (fun y => y == 0 || cs.any (fun e => e.1 ≤ y && y < e.1 + e.2)) = true)
    (hcs : ∀ e ∈ cs, rangeAll (noSqAt d c) 40 e.1 e.2 = true) :
    ∀ y, 1 ≤ y → y < U → noSqAt d c y = true := by
  intro y hy1 hyU
  have := List.all_eq_true.mp hcov y (List.mem_range.mpr hyU)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at this
  rcases this with h | ⟨e, he, h1, h2⟩
  · omega
  · have := rangeAll_spec _ 40 e.1 e.2 (hcs e he) (y - e.1) (by omega)
    rwa [show e.1 + (y - e.1) = y by omega] at this

theorem c46 : rangeAll (noSqAt 46 7) 40 1 3587 = true := by decide +kernel
theorem c430a : rangeAll (noSqAt 430 21) 40 1 30000 = true := by decide +kernel
theorem c430b : rangeAll (noSqAt 430 21) 40 30001 30000 = true := by decide +kernel
theorem c430c : rangeAll (noSqAt 430 21) 40 60001 30000 = true := by decide +kernel
theorem c430d : rangeAll (noSqAt 430 21) 40 90001 30000 = true := by decide +kernel
theorem c430e : rangeAll (noSqAt 430 21) 40 120001 18029 = true := by decide +kernel

theorem fund_46 (a : Solution₁ ((46 : ℕ) : ℤ)) (ha : IsFundamental a) :
    a.x = 24335 ∧ a.y = 3588 :=
  fund_of_check 46 24335 3588 7 (by norm_num) (by norm_num) (by norm_num)
    (chunks 46 7 3588 [(1, 3587)] (by decide +kernel) (by simpa using c46)) a ha

theorem fund_430 (a : Solution₁ ((430 : ℕ) : ℤ)) (ha : IsFundamental a) :
    a.x = 2862251 ∧ a.y = 138030 :=
  fund_of_check 430 2862251 138030 21 (by norm_num) (by norm_num) (by norm_num)
    (chunks 430 21 138030 [(1, 30000), (30001, 30000), (60001, 30000), (90001, 30000),
      (120001, 18029)] (by decide +kernel)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro e (rfl | rfl | rfl | rfl | rfl)
          exacts [c430a, c430b, c430c, c430d, c430e])) a ha

theorem B16_6_values :
    (∀ a : Solution₁ ((46 : ℕ) : ℤ), IsFundamental a → a.x = 24335 ∧ a.y = 3588) ∧
    (∀ a : Solution₁ ((430 : ℕ) : ℤ), IsFundamental a → a.x = 2862251 ∧ a.y = 138030) :=
  ⟨fund_46, fund_430⟩

theorem B16_6_main : ∀ d : ℕ, 2 ≤ d → d ≤ 430 → ¬ IsSquare (d : ℤ) → ¬ d.Prime →
    ∀ a : Solution₁ (d : ℤ), IsFundamental a → ((d : ℤ) ∣ a.y ↔ d = 46 ∨ d = 430) := by
  intro d h2 h430 hsq hp a ha
  by_cases h46 : d = 46
  · subst h46
    rw [(fund_46 a ha).2]
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨78, by norm_num⟩⟩
  by_cases h430' : d = 430
  · subst h430'
    rw [(fund_430 a ha).2]
    exact ⟨fun _ => Or.inr rfl, fun _ => ⟨321, by norm_num⟩⟩
  have hc := List.all_eq_true.mp covers_all d (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, covers, beq_iff_eq] at hc
  rcases hc with hc | (((hc | hc) | hc) | hc) | hc
  · omega
  · exfalso; apply hsq
    simp only [sqCheck, List.any_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨r, _, hr⟩ := hc
    exact ⟨r, by rw [← hr]; push_cast; ring⟩
  · exact absurd (prime_of_primeTD d hc) hp
  · exact absurd hc h46
  · exact absurd hc h430'
  · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨e1, t, u⟩, _, ⟨he, ht⟩, hu⟩ := hc
    simp only at he ht hu
    subst he
    have := not_dvd_of_sol e1 a ha t u ht hu
    exact ⟨fun h => absurd h this, fun h => by omega⟩
