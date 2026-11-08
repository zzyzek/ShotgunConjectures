/-
OEIS A216196 (Jon Perry, 2013): a 9 x 9 Sudoku with 27 "diagonals"; comment:
"Conjecture: This is the maximum for a Xoox-free grid."

Reading (reproduces both counts in the entry: 27 for the sequence's grid, 45
for its second grid, and the "36 Xoox's" of the second grid).  A diagonal is a
pair of cells (r, c), (r + 1, c +- 1) holding the same digit, indices mod 9
(the grid is a torus).  A Xoox is rows i < j and columns k < l with
g i k = g j l and g i l = g j k (not necessarily adjacent).

Checked here (core Lean, `decide`, `decide +kernel`): the grid `G` below is a Sudoku (rows,
columns, 3 x 3 boxes are permutations of 1..9), has no Xoox, and has 45
diagonals.  So the conjecture (maximum 27) is false.  Not checked here: that
45 is the maximum (CaDiCaL UNSAT for 46, see README; not in Lean).
-/

def G : List (List Nat) :=
  [[1, 2, 3, 4, 5, 6, 7, 8, 9],
   [9, 4, 8, 3, 7, 2, 6, 1, 5],
   [5, 6, 7, 8, 9, 1, 2, 3, 4],
   [4, 5, 6, 7, 8, 9, 1, 2, 3],
   [3, 7, 2, 6, 1, 5, 9, 4, 8],
   [8, 9, 1, 2, 3, 4, 5, 6, 7],
   [7, 8, 9, 1, 2, 3, 4, 5, 6],
   [6, 1, 5, 9, 4, 8, 3, 7, 2],
   [2, 3, 4, 5, 6, 7, 8, 9, 1]]

def cellOf (g : List (List Nat)) (r c : Nat) : Nat := (g.getD r []).getD c 0

def cell (r c : Nat) : Nat := cellOf G r c

def perm9 (l : List Nat) : Bool := (List.range 9).all (fun d => l.contains (d + 1))

def sudoku : Bool :=
  (List.range 9).all (fun r => perm9 ((List.range 9).map (fun c => cell r c))) &&
  (List.range 9).all (fun c => perm9 ((List.range 9).map (fun r => cell r c))) &&
  (List.range 9).all (fun b => perm9 ((List.range 9).map
    (fun i => cell (3 * (b / 3) + i / 3) (3 * (b % 3) + i % 3))))

def noXoox : Bool :=
  (List.range 9).all (fun i => (List.range 9).all (fun j => (List.range 9).all (fun k =>
    (List.range 9).all (fun l => !(i < j && k < l &&
      cell i k == cell j l && cell i l == cell j k)))))

def diagCount : Nat :=
  ((List.range 9).map (fun r => (List.range 9).map (fun c =>
    (if cell r c == cell ((r + 1) % 9) ((c + 1) % 9) then 1 else 0) +
    (if cell r c == cell ((r + 1) % 9) ((c + 8) % 9) then 1 else 0)))).flatten.sum

theorem A216196_sudoku : sudoku = true := by decide
theorem A216196_no_xoox : noXoox = true := by decide +kernel
theorem A216196_diag45 : diagCount = 45 := by decide

/-- The reading reproduces the entry: its sequence grid has 27 diagonals, its
second grid 45 diagonals and 36 Xoox's. -/
def E1 : List (List Nat) :=
  [[1,2,3,4,5,6,7,8,9],[6,5,4,9,8,7,3,2,1],[7,8,9,1,2,3,4,5,6],[2,3,1,5,6,4,8,9,7],
   [4,6,5,7,9,8,1,3,2],[8,9,7,2,3,1,5,6,4],[3,1,2,6,4,5,9,7,8],[5,4,6,8,7,9,2,1,3],
   [9,7,8,3,1,2,6,4,5]]
def E2 : List (List Nat) :=
  [[1,8,3,4,2,6,7,5,9],[6,5,4,9,8,7,3,2,1],[7,2,9,1,5,3,4,8,6],[2,9,1,5,3,4,8,6,7],
   [4,6,5,7,9,8,1,3,2],[8,3,7,2,6,1,5,9,4],[3,7,2,6,1,5,9,4,8],[5,4,6,8,7,9,2,1,3],
   [9,1,8,3,4,2,6,7,5]]
def diagOf (g : List (List Nat)) : Nat :=
  ((List.range 9).map (fun r => (List.range 9).map (fun c =>
    (if cellOf g r c == cellOf g ((r + 1) % 9) ((c + 1) % 9) then 1 else 0) +
    (if cellOf g r c == cellOf g ((r + 1) % 9) ((c + 8) % 9) then 1 else 0)))).flatten.sum
def xooxOf (g : List (List Nat)) : Nat :=
  ((List.range 9).map (fun i => (List.range 9).map (fun j => (List.range 9).map (fun k =>
    ((List.range 9).filter (fun l => i < j && k < l &&
      cellOf g i k == cellOf g j l && cellOf g i l == cellOf g j k)).length)))).flatten.flatten.sum
theorem entry_counts : diagOf E1 = 27 ∧ diagOf E2 = 45 ∧ xooxOf E2 = 36 ∧ xooxOf E1 = 0 := by
  decide +kernel
