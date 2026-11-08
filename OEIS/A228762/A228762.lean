/-
OEIS A228762 (Z.-W. Sun): number of undirected circular permutations of the
nonzero residues mod n with pairwise distinct successive differences mod n.
Conjecture: a(n) > 0 for odd n > 1, and every abelian group of odd order > 1
has a cyclic ordering of its nonzero elements with distinct successive
differences.  This is R-sequenceability; the conjecture is a special case of
the Friedlander-Gordon-Miller conjecture, proved by Alspach, Kreher and
Pastine (Australas. J. Combin. 67 (2017) 11-24).  That proof is NOT checked
here.

Checked here (core Lean, kernel evaluation by `rfl`): explicit witnesses for Z_9, Z_15, Z_21
(from the entry) and for the non-cyclic groups Z_3 x Z_3, Z_3 x Z_9,
Z_5 x Z_5 (found by certificate/search.py).  `ok m1 m2 l` says: l has
m1*m2 - 1 entries, all distinct, all in Z_m1 x Z_m2 and nonzero (so l lists
every nonzero element once), and the cyclic successive differences are
pairwise distinct.
-/

def nodupB : List (Nat × Nat) → Bool
  | [] => true
  | a :: t => !(t.contains a) && nodupB t

def diffs (m1 m2 : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  (l.zip (l.drop 1 ++ l.take 1)).map (fun p => ((p.1.1 + m1 - p.2.1) % m1, (p.1.2 + m2 - p.2.2) % m2))

def ok (m1 m2 : Nat) (l : List (Nat × Nat)) : Bool :=
  l.length == m1 * m2 - 1 && nodupB l &&
  l.all (fun a => a.1 < m1 && a.2 < m2 && a != (0, 0)) &&
  nodupB (diffs m1 m2 l)

theorem A228762_Z9 : ok 1 9 [(0, 1), (0, 2), (0, 5), (0, 3), (0, 7), (0, 6), (0, 8), (0, 4)] = true := by rfl

theorem A228762_Z15 : ok 1 15 [(0, 1), (0, 3), (0, 14), (0, 7), (0, 4), (0, 11), (0, 5), (0, 10), (0, 9), (0, 12), (0, 13), (0, 2), (0, 8), (0, 6)] = true := by rfl

theorem A228762_Z21 : ok 1 21 [(0, 1), (0, 2), (0, 11), (0, 8), (0, 19), (0, 15), (0, 9), (0, 4), (0, 10), (0, 3), (0, 6), (0, 13), (0, 18), (0, 7), (0, 5), (0, 17), (0, 16), (0, 20), (0, 12), (0, 14)] = true := by rfl

theorem A228762_Z3xZ3 : ok 3 3 [(0, 1), (1, 0), (1, 1), (2, 1), (0, 2), (2, 0), (2, 2), (1, 2)] = true := by rfl

theorem A228762_Z3xZ9 : ok 3 9 [(0, 1), (0, 2), (0, 4), (0, 3), (0, 6), (1, 0), (0, 5), (1, 1), (0, 7), (1, 2), (1, 6), (0, 8), (2, 0), (1, 3), (2, 1), (1, 8), (2, 8), (2, 6), (1, 5), (2, 7), (2, 3), (1, 7), (2, 4), (1, 4), (2, 5), (2, 2)] = true := by rfl

theorem A228762_Z5xZ5 : ok 5 5 [(0, 1), (0, 2), (0, 4), (0, 3), (1, 0), (1, 3), (2, 1), (1, 1), (2, 0), (3, 0), (1, 2), (3, 1), (1, 4), (4, 3), (2, 3), (4, 1), (2, 2), (4, 2), (3, 3), (4, 4), (3, 2), (2, 4), (4, 0), (3, 4)] = true := by rfl
