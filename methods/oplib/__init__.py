"""
oplib: reusable methods from the open-problems scan.

Each module states the pattern it captures, when to reach for it, and which
records it settled. The catalogue with recognition cues is docs/METHODS.md.

  covering    covering congruences for "A*b^n + C is never prime" (fixed or free parameter)
  sat         incremental SAT thresholds with witness re-check and cross-solver UNSAT
  seqtools    finite verification of sequence identities (C-finite, quasi-polynomial, holonomic guess)
  carmichael  Korselt reductions, Chernick families, Larsen progressions, psp/Carmichael data
  modular     residue-set obstructions for Diophantine claims
  exact       integer-only evaluation of floors of roots and m^m comparisons
  tiling      squared-rectangle checks (tiling, perfect, surrounded squares)
  oeis        batched, cached, paced OEIS fetches and parsing
  lean        emit and check core-Lean `decide` certificates under a memory cap

Run with the project venv: .venv/bin/python -I -m pytest tests  (or tests/run.py).
"""
