# OEIS A216196: Xoox-free Sudoku with more than 27 diagonals

**Source.** [A216196](https://oeis.org/A216196), Jon Perry, Mar 12 2013: "A diagonalized Sudoku torus", a 9 x 9
Sudoku read by rows, said to contain 27 (internal and external) diagonals. Comment: "Conjecture: This is the
maximum for a Xoox-free grid." A second grid is said to have 45 diagonals and 36 Xoox's. (OEIS text, CC BY-SA 4.0,
cached entry read 2026-11-08.)

**Reading.** The entry does not define "diagonal". We tested several readings (`certificate/readings.py`); the
only one that reproduces all three counts in the entry (27 and 45 diagonals, 36 Xoox's) is: a diagonal is a pair
of cells (r, c), (r + 1, c ± 1), indices mod 9 (the torus), holding the same digit; a Xoox is two rows i < j and
two columns k < l with g(i,k) = g(j,l) and g(i,l) = g(j,k) (the entry's example: 14 over 41, not necessarily
adjacent).

**Result.** False. The Xoox-free Sudoku

    1 2 3 4 5 6 7 8 9
    9 4 8 3 7 2 6 1 5
    5 6 7 8 9 1 2 3 4
    4 5 6 7 8 9 1 2 3
    3 7 2 6 1 5 9 4 8
    8 9 1 2 3 4 5 6 7
    7 8 9 1 2 3 4 5 6
    6 1 5 9 4 8 3 7 2
    2 3 4 5 6 7 8 9 1

has 45 diagonals. By SAT, 45 is the maximum over Xoox-free Sudokus and also over all Sudokus (the entry's
Xoox-containing example already attains it).

**Argument.** SAT encoding (`certificate/enc.py`): one-hot cells, Sudoku constraints, first row 1..9 (digit
relabelling preserves Sudokus, Xoox's and diagonals), one 4-literal clause per Xoox pattern, an indicator per
torus-diagonal pair implying equality, and a sequential counter forcing at least T indicators. CaDiCaL 2.1.3:
SAT for T = 28, 31, 34, 40, 45 (solutions decoded and re-verified by `certificate/decode.py`); UNSAT for T = 46
(with and without the Xoox clauses), 47, 48, 54, 60, 81.

**Evidence.**
- Core Lean: [`A216196.lean`](A216196.lean). `A216196_sudoku`, `A216196_no_xoox`, `A216196_diag45` check the grid
  above; `entry_counts` checks that the reading gives the entry's numbers (27, 45, 36 Xoox's, 0 for the first grid).
  Axioms: propext only.
- Outside Lean: the maximality of 45 (CaDiCaL UNSAT for T = 46; an LRAT proof of 30 MB was produced but not
  checked) and the correctness of the encoding. The disproof itself (a grid beyond 27) has nothing outside Lean
  except the choice of reading.

**Review level.** lean-witness for the disproof; solver result for the exact maximum.

**Prior art.** Checked 2026-11-08: OEIS entry, google-deepmind/formal-conjectures (no OEIS/216196 file), web
search for the term "Xoox" (no hits beyond OEIS). Not found elsewhere.
