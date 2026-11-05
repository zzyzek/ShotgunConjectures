# Literature check: Sloane's "Challenge Problems: Independent Sets in Graphs"

Checked 2026-11-04. Source page: https://oeis.org/A265032/a265032.html
(last updated Dec 05 2015). Web, arXiv, Crossref, OEIS, Brouwer's tables.
Read-only, nothing posted.

## Summary table

| Instance | Code meaning | Sloane page (2015) | Current lower | Current upper | Status |
|---|---|---|---|---|---|
| 1dc.2048 | binary 1-deletion code, n=11 | 172-174 | 172 (VT_0(11)) | 172 (Nakasho et al. 2024, ILP) | Solved, = 172 (computer proof, Gurobi, no certificate) |
| 1zc.1024 | binary 1-asymmetric-error code, n=10 | 112-117 | 112 | 117 | Open |
| 1zc.2048 | same, n=11 | 198-210 | 198 | 210 | Open |
| 1zc.4096 | same, n=12 | 379-410 | 379 (Butenko et al.) | 410 | Open |
| A_4(6,3) | quaternary, n=6, d=3 (4096-vertex graph) | 164-179 | 164 | 176 (Litjens-Polak-Schrijver 2017, SDP) | Open, upper bound improved |

Open items ranked by closeness of bounds:

1. 1zc.1024: 112-117, gap 5 (4.5 % of lower bound).
2. 1zc.2048: 198-210, gap 12 (6.1 %).
3. A_4(6,3): 164-176, gap 12 (7.3 %).
4. 1zc.4096: 379-410, gap 31 (8.2 %).

## 1. 1dc.2048 (single-deletion-correcting codes, length 11)

- Lower bound 172: Varshamov-Tenengolts code VT_0(11). Listed on Sloane's page.
- Upper bound history.
  - 174: Borchers 2005, Lovasz theta (174.729), Sloane's page.
  - 173: Albert No, "Nonasymptotic Upper Bounds on Binary Single Deletion
    Codes via Mixed Integer Linear Programming", Entropy 21(12):1202, 2019,
    https://doi.org/10.3390/e21121202 . MILP. Also gives n=12 upper bound 320.
  - 172: K. Nakasho, M. Hagiwara, A. Anderson, J. B. Nation, "The Tight Upper
    Bound for the Size of Single Deletion Error Correcting Codes of Length 11",
    ISITA 2024 (IEEE), https://doi.org/10.23919/ISITA60732.2024.10858234 ;
    preprint arXiv:2309.14736 (Sep 2023, "in Dimension 11"). Code:
    https://github.com/aabaa/deletion_code
- Method of the 172 proof (read from the arXiv PDF). Binary variable per word,
  clique constraints from shared deletion images ("Constraint 0"), plus a
  lower-bound row sum >= |VT_0(n)| and several WLOG/redundant constraints:
  dominated-word removal (Constraint 2), fixing 0^n and 1^n in the code
  (Constraint 3), complement symmetry breaking on weight halves
  (Constraint 4), run-count counting inequalities (Constraint 5), and
  sub-cube bounds |D(C,u,v)| <= M(r) using known M(r) for r <= 10
  (Constraint 6). Solver Gurobi 10.0.0 on one Ryzen 9 5900X, best
  configuration ~36 000 s for n=11. The authors say themselves that the
  result rests on trusting an ILP solver and suggest a theorem-prover
  check as future work. No independent re-verification found.
- Status: solved, M(11) = 172 = |VT_0(11)|, modulo the solver-trust caveat.
  n=12 remains open: 316 <= M(12) <= 320 (No 2019; Nakasho et al. could not
  improve 320).
- Corroboration elsewhere: Marino, Buffoni, Zavalnij, "A short review on the
  maximum clique problem algorithms ...", Commun. Phys. 9 (2026),
  arXiv:2403.09742 v2, Table 4 lists 1dc.2048 as 172 and marks it optimal.
- OEIS. There is no OEIS sequence for "maximal size of a binary
  single-deletion-correcting code" (OEIS text search for
  deletion-correcting returns A000016, A054200, A057591, A057608, A057657,
  etc., but no 1-deletion maximum sequence). A000016 (which gives |VT_0(n-1)|)
  carries the VT comment and links Sloane's page but has no comment that
  M(n) = A000016(n+1) is now known through n = 11. Sloane's page text
  ("whether they agree with this sequence for larger graphs is an open
  problem") is outdated for 2048 nodes. A265032 does cite No 2019.

## 2. 1zc.1024 (Z-channel / single asymmetric error, length 10)

- Lower bound 112 (Etzion 1991 / Etzion-Ostergard 1998 constructions as cited
  on Sloane's page). Heuristic MIS solvers reach exactly 112 and no more,
  e.g. Jin & Hao, "General swap-based multiple neighborhood tabu search for
  the maximum independent set problem", Eng. Appl. AI 37 (2015) 20-33,
  results table https://leria-info.univ-angers.fr/~jinkao.hao/mis.html .
- Upper bound 117: from the asymmetric-code bound tables cited as
  [EO98] T. Etzion, P. R. J. Ostergard, IEEE Trans. IT 44 (1998) 382-388
  (the upper bounds there trace back to LP/constant-weight-code methods of
  Weber-de Vroedt-Boekee 1988 and Weber's 1989 thesis; which paper first
  proved 117 not checked). Lovasz theta is weaker: 128.67.
- No post-2015 improvement found (searched arXiv, Crossref, clique/MIS
  benchmark papers, SDP-bound papers; the SDP literature after Schrijver
  2005 treats Hamming distance, not asymmetric distance). The Marino et al.
  2026 review still lists 112-117.
- OEIS A010101 (Maximal size of binary code of length n and asymmetric
  distance 2): data 1, 2, 2, 4, 6, 12, 18, 36, 62 (n=1..9); comment
  "Next 3 terms are known to be in the range 112-117, 198-210 and 379-410".
  Matches current knowledge.

## 3. 1zc.2048 (length 11)

- 198-210. Lower bound EO98; heuristics (Jin-Hao 2015) reach 198 only.
  Upper bound 210 from the same asymmetric-code tables; theta is 237.4.
- No improvement found. A010101 comment is current.

## 4. 1zc.4096 (length 12)

- Lower bound 379: Butenko, Pardalos, Sergienko, Shylo, Stetsyuk (found 2001),
  published as "Estimating the size of correcting codes using extremal graph
  problems", in Optimization (C. Pearce, ed.), Springer Optim. Appl. 32,
  2009, pp. 227-243. Previous 336. Jin-Hao 2015 also reaches 379.
- Upper bound 410 (EO98 table). No theta value computed on Sloane's page.
- No improvement found. A010101 comment is current. Note: Marino et al.
  arXiv:2403.09742 v1 printed the stale range 336-410; v2 corrected to
  379-410.

## 5. A_4(6,3) (quaternary, length 6, minimum distance 3)

- Lower bound 164: Bogdanova, Brouwer, Kapralov, Ostergard, "Error-correcting
  codes over an alphabet of four elements", Des. Codes Cryptogr. 23 (2001)
  333-342, https://doi.org/10.1023/A:1011275112159 . Unchanged.
- Upper bound 176: B. Litjens, S. Polak, A. Schrijver, "Semidefinite bounds
  for nonbinary codes based on quadruples", Des. Codes Cryptogr. 84 (2017)
  87-100 (online May 2016), arXiv:1602.02531 . SDP over codes of size <= 4.
  Previous best 179 was the Delsarte LP bound. Same paper gives
  A_4(7,3) <= 596 (was 614).
- Brouwer's current table (https://aeb.win.tue.nl/codes/quaternary-1.html ,
  old win.tue.nl/~aeb URL redirects) lists A_4(6,3) = 164-176,
  A_4(7,3) = 512-596, A_4(8,3) = 2048-2340.
- No newer bound found for n=6, d=3.
- OEIS A265032 (Maximal size of a code of length n, min distance 3, alphabet
  size 4): data 1, 1, 4, 16, 64; comment still says a(6) in [164-179] and
  a(7) in [512-614]. Outdated on both upper bounds (should be 176 and 596).
  Sloane's page also still says [164-179].

## Other statuses on Sloane's page

Checked every graph family on the page (1dc, 2dc, 1tc, 1et, 1zc, quaternary).

- Outdated: 1dc.2048 (now solved, 172) and the quaternary entry (179 -> 176).
- 2dc.2048 = 24 (San Segundo and Artieda, Dec 2015) is already on the page.
- 1et.256 = 50 is stated as known on the page (sum over the 9 weight
  components); A057657 agrees. The theta table's 53* is just the
  componentwise theta bound, not an open range.
- 1tc.*, 1et.*, 2dc.*, 1zc.128/256/512 all marked known on the page and
  consistent with OEIS A057608, A057657, A057591, A010101.
- Reference [BPS03] on the page is now the 2009 Springer chapter above.

## Sources

- Sloane challenge page: https://oeis.org/A265032/a265032.html
- No 2019: https://doi.org/10.3390/e21121202
- Nakasho et al. 2024: https://doi.org/10.23919/ISITA60732.2024.10858234 , https://arxiv.org/abs/2309.14736
- Litjens-Polak-Schrijver 2017: https://arxiv.org/abs/1602.02531
- Brouwer quaternary table: https://aeb.win.tue.nl/codes/quaternary-1.html
- OEIS A000016, A010101, A265032, A057657
- Marino et al. review: https://arxiv.org/abs/2403.09742
- Jin-Hao MIS results: https://leria-info.univ-angers.fr/~jinkao.hao/mis.html
