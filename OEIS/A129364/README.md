# OEIS A129364: a(n) divides A092287(n) (known)

**Source.** [A129364](https://oeis.org/A129364) (offset 1): a(n) = Π_{k=1..n} A066841(k) = Π_{k=1..n} Π_{d|k} d^(k/d);
the entry also gives a(n) = Π_{k=1..n} (⌊n/k⌋!)^k. Comment: "Conjecture: a(n) divides A092287(n) for all n - see
comments in A129365", where A092287(n) = Π_{j,k ≤ n} gcd(j,k). This is Conjecture A of
[A129365](https://oeis.org/A129365) (A129365 = A092287/A129364 is an integer). (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Result.** True, known.

**Argument.** Fix a prime p and write m_r = ⌊n/p^r⌋. Counting pairs (j,k) with p^r | gcd(j,k) gives
v_p(A092287(n)) = Σ_{r≥1} m_r² (Greathouse, in A092287, 2013). By Legendre, v_p(Π_k (⌊n/k⌋!)^k) =
Σ_{r≥1} Σ_k k·⌊m_r/k⌋, and m² − Σ_{k≤m} k⌊m/k⌋ = Σ_{k≤m} (m mod k) ≥ 0 (A004125). So every p-adic valuation of
a(n) is at most that of A092287(n).

**Evidence.** A Lean 4 proof of this exact statement (`conjecture1`, with the denominator Π_k (⌊n/k⌋!)^k) exists:
KitaKen1/oeis-a129365-conjectures, `lean/OeisA129365FC.lean` (commit 9c02015), linked as `formal_proof` from
google-deepmind/formal-conjectures `FormalConjectures/OEIS/129365.lean` (tag `research solved`). Not re-checked
here; the file contains no `sorry` or `native_decide` (grep). Outside Lean here: the identification of A129364's
definition with Π_k (⌊n/k⌋!)^k (an entry formula; it follows from Π_{k≤n} Π_{d|k} d^(k/d) = Π_{d≤n} Π_{t≤n/d} d^t…
regrouped by the quotient), not formalised.

**Review level.** `rechecked` (argument re-derived; third-party Lean proof not run).

**Prior art.** Checked 2026-11-06: formal-conjectures A129365 (research solved, formal proof link); T. Adamczewski,
"OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (2026), App. A (cited
in A129365 for Conjectures B, C); the valuation formula for A092287 confirmed by C. R. Greathouse IV (2013).
