# OEIS A168295: "Conjecture: Worpitzky forms" states no claim

**Source.** OEIS wiki, Talk:Conjectures/List, line for A168295: "Conjecture: \"Worpitzky forms\"".
[A168295](https://oeis.org/A168295) (R. L. Bagula, 2009): triangle of coefficients of
p(x, n) = (n-1)! Sum_{j=1..n} A142458(n, j) binomial(x + j - 1, n - 1).

**Result.** Misstated: nothing to prove. The 2009 comment, after the word "Conjecture", only names a
family: for a "general Pascal recursion" triangle Pascal[n,k,m],
p[x,n,m] = Sum_k Pascal[n,k,m] binomial(x+k-1, n-1), "where p[x,n,m] are the inverse z transform
polynomials". No equation or property is asserted. G. C. Greubel removed the comment in revision #3
(2022-03-17, approved by N. J. A. Sloane in #5); the current entry has no conjecture.

**Argument.** The one reading that turns the comment into a statement is: the ordinary g.f. in x of
p(x) is Sum_k Pascal[n,k,m] z^(n-k)/(1-z)^n. This holds for any coefficient array, since
Sum_{x>=0} binomial(x+k-1, n-1) z^x = z^(n-k)/(1-z)^n (substitute x = n - k + j). So under that
reading it is a tautology, and under any other it has no content.

**Evidence.** README only. Lean: none (no statement). Outside Lean: the reading of the removed comment.

**Review level.** `rechecked`: the removed text was read in the OEIS history (revision #3).

**Prior art.** Verdict `misstated` (not immediate: needs the history). Sources:
[OEIS A168295 history, rev. #3 (G. C. Greubel, 2022-03-17)](https://oeis.org/history?seq=A168295)
(fetched 2026-11-05). Searched: OEIS entry and history, google-deepmind/formal-conjectures (tree
listing: no file for A168295), 2026-11-05.
