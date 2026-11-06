# Writes D16_1.lean from the record lines (EXACT ...) of prodsearch output.
# usage: python3 make_lean.py records.txt > D16_1.lean
#
import sys

recs = {}
for line in open(sys.argv[1]):
  if not line.startswith("EXACT"):
    continue
  head, tr = line.split(":", 1)
  f = dict(x.split("=") for x in head.split()[1:])
  s, P, S = int(f["s"]), int(f["P"]), int(f["S"])
  ts = sorted(tuple(map(int, t.split(","))) for t in tr.split())
  if s >= 2 and (s not in recs or P < recs[s][0]):
    recs[s] = (P, S, ts)

pl = [(a, b) for a in range(1, 11) for b in range(a, 35) if a * b * b < 1200]

out = []
w = out.append
w("""/-
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
""")
for s in sorted(recs):
  P, S, ts = recs[s]
  w("def W%d : List (Nat × Nat × Nat) :=\n  [%s]" % (s, ", ".join("(%d, %d, %d)" % t for t in ts)))
  w("theorem wit_%d : witOk %d %d %d W%d = true := by decide +kernel\n" % (s, s, P, S, s))

w("/-- All (a, b) with 1 <= a <= b and a * b * b < 1200. -/")
w("def pl : List (Nat × Nat) := [" + ", ".join("(%d, %d)" % p for p in pl) + "]\n")
w("""def plOk : Bool :=
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
""")
w("""
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

""")
w("""/-- No P < 36 has two distinct triples with one common sum. -/
theorem no_two_lt_36 {P : Nat} (hP : P < 36) {t u : Nat × Nat × Nat}
    (ht : IsTriple P t) (hu : IsTriple P u) (hs : sum3 t = sum3 u) : t = u := by
  have h := chunk_spec (lo := 0) two_0 hP
  simp only [Nat.zero_add, noTwo, List.all_eq_true] at h
  have := h t (mem_trip (by omega) ht) u (mem_trip (by omega) hu)
  simp [hs] at this
  exact this

""")
print("\n".join(out))
