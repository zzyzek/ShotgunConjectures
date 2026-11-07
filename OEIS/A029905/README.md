# OEIS A029905: r(n) and h(n) are not complementary (row 120 of 3-row Chomp is in neither)

**Source.** OEIS [A029905](https://oeis.org/A029905), "r(n), where exists one-parameter family of
strategic partitions (k+p(n)+q(n), k+q(n), r(n)) for k = 0,1,2,... in Chomp", comment
"Conjectured to be complementary to h(n), see A029902", and A. E. Brouwer (May 31 2002):
"Maybe the conjecture is false - see the Brouwer link." h(n) is [A029902](https://oeis.org/A029902):
the strategic move on the g(n) X 3 rectangle is (h(n),2) (OEIS text, CC BY-SA 4.0).
Origin: Berlekamp-Conway-Guy, Winning Ways vol. 2, 598-600.

**Reading.** Positions of 3-row Chomp are (p,q,r), p >= q >= r >= 0 row lengths, the player
who must take the poisoned square loses ((1,0,0) is a P-position). The move (h,2) on the
g X 3 rectangle (g,g,g) leads to (g,g,h). So h ranges over the rows r for which some
(q,q,r), q > r, is a P-position. r(n) ranges over the rows r for which (k+P+Q, k+Q, r) is a
P-position for every k >= 0.

**Result.** False. Row r = 120 lies in neither set. For q >= 170 the P-positions in row 120
are (q+72, q, 120) for even q and (q+70, q, 120) for odd q (q - 170 even / odd), forever, and
no (q,q,120) is a P-position. Rows 0..119 and 121..125 each lie in exactly one of the two
sets, and the computed sets agree with the OEIS data of A029902 and A029905.

**Argument.** For q >= r let f(q,r) be the unique p with (p, min(p,q), min(p,q,r)) a
P-position (the positions with fixed q, r and varying p form a chain, each can move to every
lower one, so there is at most one P-position; there is at least one by the rule below).
Re-derived from the move rules: if some p' < q has (p',p',min(p',r)) a P-position then
f(q,r) = p'; otherwise f(q,r) is the least p >= max(q,1) that is not among
f(a, min(r,a)) (a < q, moves in row 1) and f(q,b) (b < r, moves in row 2). This rule is
checked against a brute-force game solver on all boards with p <= 14 (`chomp_cert.py`).
A row with a diagonal P-position is constant from then on (the finite case, giving h).
Otherwise, for q beyond the starting points of all lower rows, f(q,r) = q + t with t the
least t >= 1 outside S_q ∪ D_q, where S_q = {v - q : v already used in row r, v >= q} and
D_q = {f(q,b) - q : b < r infinite rows}. Each lower infinite row is certified eventually
periodic, so D_q is periodic in q, and (q mod L, S_q) evolves by a deterministic finite rule
S_{q+1} = {s-1 : s ∈ S_q ∪ {t}, s >= 1}. A repeated state proves the row periodic forever.
`chomp_rows.py` does this row by row for r <= 125 (rows 0..119 have period 1); for row 120
the state repeats with period 2 and offsets (72, 70), t >= 1 throughout, and f(q,120) != q
for 120 < q < 170 is checked directly. Hence (q,q,120) is never a P-position (120 not in h)
and f(q,120) - q is not eventually constant (no one-parameter family, 120 not in r).

**Evidence.** `certificate/chomp_cert.py` (recurrence versus brute force, boards p <= 14),
`certificate/chomp_rows.py` (row certificates, run as `python3 chomp_rows.py 125 700`,
output `certificate/rows.out`). No Lean: the certificate tabulates about 85 000 values of f
and is beyond kernel `decide`. Outside Lean: everything (the recurrence derivation is by
hand and brute-force tested; the row certificates are Python).

**Review level.** `rechecked` (recurrence re-derived from the rules and tested by brute force;
the periodicity of row 120 is a finite-state certificate, consistent with Brouwer's table).

**Prior art.** A. E. Brouwer, [Chomp](https://aeb.win.tue.nl/games/chomp.html) (checked
2026-11-06): lists row 120 as the first row whose pattern is p = q + constant + (-1)^q (start
170, period 2), computed up to q = 130000, and remarks in OEIS "maybe false". S. Byrnes,
Poset game periodicity, Integers 3 (2003) G3, proves eventual periodicity of every row but not
the specific pattern. The certificate above turns Brouwer's observation into a proof.
google-deepmind/formal-conjectures: no Chomp entry found (2026-11-06).
