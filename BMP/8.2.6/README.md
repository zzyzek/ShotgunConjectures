# BMP 8.2.6: an r-cap or an empty r-cup in every large point set (Valtr's conjecture)

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry* (2005), Section 8.2, Conjecture 6 (attributed to Valtr 2002). Paraphrase: for every r ≥ 3 there is f such that every set of at least f points in general position in the plane, no two on a vertical line, contains an r-cap or an empty r-cup (an r-cup whose convex hull contains no other point of the set).

**Result.** True.

**Argument.** P. Valtr (2007) calls a k-cap or k-cup p1, ..., pk *open* if no point p of the set with x(p1) < x(p) < x(pk) lies above the polygonal line p1 ... pk. The convex hull of a cup lies above the cup and inside that vertical strip, so an open cup is empty (Valtr states this in the proof of his Corollary 2). His Theorem 2 gives f(k, l) such that every configuration (general position, distinct x-coordinates) of size ≥ f(k, l) contains an open k-cap or an open l-cup; his Theorem 3(i) bounds f'(k, l), the threshold for "a k-cap or an open l-cup", between two double exponentials. With k = l = r this is the conjecture. Valtr also derives the consequence BMP state (a large set with no k-cap contains an empty l-gon, his Corollary 2) and notes he had asked this in the 2002 paper BMP cite.

**Evidence.** Citation; full text read (Charles University preprint, KAM series 2004-671). No Lean.

**Review level.** `rechecked` (the step from Theorem 2/3 to the conjecture, open cup ⇒ empty cup, re-derived).

**Prior art.** Verdict `known`. P. Valtr, *Open caps and cups in planar point sets*, Discrete Comput. Geom. 37 (2007) 565-576, doi:10.1007/s00454-006-1286-3; preprint https://kam.mff.cuni.cz/kamserie/clanky/2004/s671.pdf (read 2026-11-06). Searched: web, google-deepmind/formal-conjectures (local clone 2026-11-06) (2026-11-06).
