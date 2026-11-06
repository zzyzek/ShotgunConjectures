/-
Guy, Unsolved Problems in Number Theory (3rd ed.), D16: least common product of
m distinct triples a <= b <= c of positive integers with one common sum.

Checked here (core Lean, kernel `decide`):
  * witnesses: for each listed m, m distinct triples (a, b, c), 1 <= a <= b <= c,
    with product P_m and common sum S_m (`wit_m`);
  * minimality for m = 2: no P < 36 has two distinct triples with a common sum
    (`no_two_lt_36`).
Not checked here: minimality for m >= 3 (exhaustive C search
certificate/prodsearch.c over P <= 1.5e9, outside Lean).
-/


/-- 1 <= a <= b <= c and a * b * c = P. -/
def IsTriple (P : Nat) (t : Nat × Nat × Nat) : Prop :=
  1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 = P

def isTripleB (P : Nat) (t : Nat × Nat × Nat) : Bool :=
  decide (1 ≤ t.1) && decide (t.1 ≤ t.2.1) && decide (t.2.1 ≤ t.2.2) && decide (t.1 * t.2.1 * t.2.2 = P)

def sum3 (t : Nat × Nat × Nat) : Nat := t.1 + t.2.1 + t.2.2

/-- m distinct triples, all with product P and sum S. -/
def witOk (m P S : Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  decide (l.length = m) && decide l.Nodup && l.all (isTripleB P) && l.all (fun t => sum3 t == S)

def W2 : List (Nat × Nat × Nat) :=
  [(1, 6, 6), (2, 2, 9)]
theorem wit_2 : witOk 2 36 13 W2 = true := by decide +kernel

def W3 : List (Nat × Nat × Nat) :=
  [(4, 15, 20), (5, 10, 24), (6, 8, 25)]
theorem wit_3 : witOk 3 1200 39 W3 = true := by decide +kernel

def W4 : List (Nat × Nat × Nat) :=
  [(6, 56, 75), (7, 40, 90), (9, 28, 100), (12, 20, 105)]
theorem wit_4 : witOk 4 25200 137 W4 = true := by decide +kernel

def W5 : List (Nat × Nat × Nat) :=
  [(11, 84, 90), (12, 63, 110), (15, 44, 126), (18, 35, 132), (22, 28, 135)]
theorem wit_5 : witOk 5 83160 185 W5 = true := by decide +kernel

def W6 : List (Nat × Nat × Nat) :=
  [(14, 231, 240), (15, 176, 294), (16, 154, 315), (28, 72, 385), (33, 60, 392), (40, 49, 396)]
theorem wit_6 : witOk 6 776160 485 W6 = true := by decide +kernel

def W7 : List (Nat × Nat × Nat) :=
  [(35, 216, 260), (36, 195, 280), (40, 156, 315), (42, 144, 325), (45, 130, 336), (60, 91, 360), (72, 75, 364)]
theorem wit_7 : witOk 7 1965600 511 W7 = true := by decide +kernel

def W8 : List (Nat × Nat × Nat) :=
  [(70, 432, 520), (72, 390, 560), (80, 312, 630), (84, 288, 650), (90, 260, 672), (91, 256, 675), (120, 182, 720), (144, 150, 728)]
theorem wit_8 : witOk 8 15724800 1022 W8 = true := by decide +kernel

def W9 : List (Nat × Nat × Nat) :=
  [(99, 588, 600), (100, 539, 648), (105, 462, 720), (112, 405, 770), (126, 336, 825), (132, 315, 840), (162, 245, 880), (165, 240, 882), (196, 200, 891)]
theorem wit_9 : witOk 9 34927200 1287 W9 = true := by decide +kernel

def W10 : List (Nat × Nat × Nat) :=
  [(198, 1176, 1200), (200, 1078, 1296), (210, 924, 1440), (224, 810, 1540), (231, 768, 1575), (252, 672, 1650), (264, 630, 1680), (324, 490, 1760), (330, 480, 1764), (392, 400, 1782)]
theorem wit_10 : witOk 10 279417600 2574 W10 = true := by decide +kernel

def W11 : List (Nat × Nat × Nat) :=
  [(378, 1925, 1976), (380, 1820, 2079), (385, 1710, 2184), (399, 1540, 2340), (429, 1330, 2520), (440, 1274, 2565), (504, 1045, 2730), (532, 975, 2772), (550, 936, 2793), (637, 792, 2850), (684, 735, 2860)]
theorem wit_11 : witOk 11 1437836400 4279 W11 = true := by decide +kernel

/-- All (a, b) with 1 <= a <= b and a * b * b < 1200. -/
def pl : List (Nat × Nat) := [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 19), (1, 20), (1, 21), (1, 22), (1, 23), (1, 24), (1, 25), (1, 26), (1, 27), (1, 28), (1, 29), (1, 30), (1, 31), (1, 32), (1, 33), (1, 34), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (2, 17), (2, 18), (2, 19), (2, 20), (2, 21), (2, 22), (2, 23), (2, 24), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (3, 18), (3, 19), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (4, 16), (4, 17), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, 9), (9, 10), (9, 11), (10, 10)]

def plOk : Bool :=
  (List.range 11).all fun a => (List.range 35).all fun b =>
    !(decide (1 ≤ a) && decide (a ≤ b) && decide (a * b * b < 1200)) || pl.contains (a, b)

theorem plOk_true : plOk = true := by decide +kernel

theorem pl_complete {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) (hA : a < 11) (hB : b < 35)
    (h : a * b * b < 1200) : (a, b) ∈ pl := by
  have := plOk_true
  simp only [plOk, List.all_eq_true, List.mem_range] at this
  have h2 := this a hA b hB
  simp [ha, hab, h] at h2
  exact h2

/-- The triples (a, b, P / (a b)) with (a, b) in ps. -/
def trip (ps : List (Nat × Nat)) (P : Nat) : List (Nat × Nat × Nat) :=
  ps.filterMap fun ab =>
    if P % (ab.1 * ab.2) = 0 ∧ ab.2 ≤ P / (ab.1 * ab.2) then some (ab.1, ab.2, P / (ab.1 * ab.2)) else none

def noTwo (P : Nat) : Bool :=
  let l := trip pl P
  l.all fun t => l.all fun u => t == u || sum3 t != sum3 u

def chunk (f : Nat → Bool) (lo n : Nat) : Bool := (List.range n).all fun i => f (lo + i)

theorem chunk_spec {f : Nat → Bool} {lo n i : Nat} (h : chunk f lo n = true) (hi : i < n) :
    f (lo + i) = true := by
  simp only [chunk, List.all_eq_true, List.mem_range] at h
  exact h i hi

theorem two_0 : chunk noTwo 0 36 = true := by decide +kernel


theorem a_small {a b c N : Nat} (hab : a ≤ b) (hbc : b ≤ c) (h : a * b * c < N * N * N) : a < N := by
  apply Nat.lt_of_not_le
  intro hN
  have h1 : N * N ≤ a * b := Nat.mul_le_mul hN (Nat.le_trans hN hab)
  have h2 : N * N * N ≤ a * b * c := Nat.mul_le_mul h1 (Nat.le_trans hN (Nat.le_trans hab hbc))
  omega

theorem b_small {a b c N : Nat} (ha : 1 ≤ a) (hbc : b ≤ c) (h : a * b * c < N * N) : b < N := by
  apply Nat.lt_of_not_le
  intro hN
  have h1 : N * N ≤ b * c := Nat.mul_le_mul hN (Nat.le_trans hN hbc)
  have h2 : b * c ≤ a * (b * c) := Nat.le_mul_of_pos_left (b * c) ha
  rw [← Nat.mul_assoc] at h2
  omega

/-- Every triple with product P < 1200 is listed by `trip pl P`. -/
theorem mem_trip {P : Nat} {t : Nat × Nat × Nat} (hP : P < 1200) (ht : IsTriple P t) :
    t ∈ trip pl P := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hab, hbc, hp⟩ := ht
  simp only at ha hab hbc hp
  have hb : 1 ≤ b := Nat.le_trans ha hab
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  have hdiv : a * b * c / (a * b) = c := Nat.mul_div_cancel_left c hab0
  have hA : a < 11 := a_small (N := 11) hab hbc (by omega)
  have hB : b < 35 := b_small (N := 35) ha hbc (by omega)
  have hbb : a * b * b ≤ a * b * c := Nat.mul_le_mul_left (a * b) hbc
  have hmem : (a, b) ∈ pl := pl_complete ha hab hA hB (by omega)
  simp only [trip, List.mem_filterMap]
  refine ⟨(a, b), hmem, ?_⟩
  subst hp
  simp [hdiv, hbc, Nat.mul_mod_right]


/-- No P < 36 has two distinct triples with one common sum. -/
theorem no_two_lt_36 {P : Nat} (hP : P < 36) {t u : Nat × Nat × Nat}
    (ht : IsTriple P t) (hu : IsTriple P u) (hs : sum3 t = sum3 u) : t = u := by
  have h := chunk_spec (lo := 0) two_0 hP
  simp only [Nat.zero_add, noTwo, List.all_eq_true] at h
  have := h t (mem_trip (by omega) ht) u (mem_trip (by omega) hu)
  simp [hs] at this
  exact this


