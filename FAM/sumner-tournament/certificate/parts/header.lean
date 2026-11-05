import Mathlib

/-!
# Sumner's universal tournament conjecture for trees on at most @N@ vertices

Checked here (Mathlib, no `sorry`, no `native_decide`; the finite checks run in the
kernel through `decide +kernel`):

* `SumnerSmall.sumner_le_*`: for `2 ≤ n ≤ @N@`, every tournament on `2n - 2` vertices
  contains every oriented tree on `n` vertices. The statement and the definitions
  `IsTournament`, `IsOrientation`, `IsOrientedTree`, `Hom`, `Embeds` are copied from
  formal-conjectures `Wikipedia/SumnerUniversalTournamentConjecture.lean`.

How: (1) `tree_parent_code` (general): a finite tree listed by distance from a root
has every edge between a vertex and its parent, which comes earlier. (2) Every
parent code with directions on `n` vertices maps injectively, arc to arc, into one
of the listed oriented-tree representatives (`codesOK`, certificates in `codeData`).
(3) `Classified k`: every tournament on `Fin k` is isomorphic to a listed
representative, by one-vertex extension with an explicit isomorphism for every
(representative, in-set) pair (`stepBody`, tables `tabData`), for `k ≤ @M@`.
(4) Every tree representative embeds into every tournament representative on
`2n - 2` vertices (`embBody`, embeddings in `embData`).

Not checked here: that the representative lists are free of repeats (not needed),
the Python generator `scripts/gen_lean.py` (its output is checked), and any case
`n > @N@`.
-/
