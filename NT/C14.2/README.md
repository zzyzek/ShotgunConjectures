# Guy UPINT C14: strongly sum-free triples in groups (partial, by others)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section C14 (paraphrased): is there, for
every l, an n₀(l) such that whenever n > n₀ and a₁, …, aₙ are elements of a group with no product a_i a_j equal to
the identity (i = j allowed, so no element of order 1 or 2 and no element together with its inverse), there are l
of the a's whose pairwise products (in index order) are not among a₁, …, aₙ? Guy: "this has not even been proved
for l = 3".

**Result (known partial result; the question stays open).** For l = 3 and abelian groups the answer is yes:
T. Łuczak and T. Schoen, *On strongly sum-free subsets of abelian groups*, Colloq. Math. 71 (1996) 149–151
(DOI 10.4064/cm-71-1-149-151). Their abstract states exactly this: an affirmative answer in the first non-trivial
case l = 3 when the group is abelian. Open: l = 3 for non-abelian groups, and every l ≥ 4 (abelian or not).

**Argument.** Not re-derived here (the paper was not available; only its abstract was read). Guy's C14 reference
list already contains this paper, so the third edition's remark "not even proved for l = 3" is best read as
referring to general (non-abelian) groups.

**Evidence.** Citation only; no Lean file. Outside Lean: the Łuczak–Schoen theorem (published proof).

**Review level.** `agent` (abstract read 2026-11-07 on impan.pl; proof not checked).

**Prior art.** Checked 2026-11-07: impan.pl abstract of Łuczak–Schoen (1996); web search for later work found
nothing on l ≥ 4 or non-abelian l = 3; not in google-deepmind/formal-conjectures (clone of 2026-11-06).
