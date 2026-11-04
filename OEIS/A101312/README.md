# OEIS A101312: other weekday/day pairs do not give a shifted Friday-13th sequence

**Source.** [A101312](https://oeis.org/A101312) (number of Friday the 13ths in year n, from 1901), comment:
"Conjecture: The same basic repeating pattern results if we seek the number of "Sunday the 22nds" or "Wednesday
the 8ths" or anything else similar, with the only difference being that the sequence starts at a different point
in the repeating pattern." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Weekday w on day d" counts per year, compared with the Friday-13th counts up to a shift in years.
Changing d shifts the weekday of day d in every month by the same amount, so every such sequence equals
"weekday u on the 13th" for some u. The question is whether each of these is a year-shift of the Friday sequence.

**Result.** True on 1901–2099 (where the Gregorian calendar agrees with the Julian one and the pattern has period
28: weekday u corresponds to a shift of 20, 8, 24, 12, 0, 16, 4 years for Monday..Sunday). False for the
Gregorian calendar as a whole: over the 400-year cycle no weekday other than Friday gives a cyclic shift of the
Friday sequence. Disputed relative to the scan, which called the full statement trivially true and said the
Gregorian century years "cause the same jumps"; they do not.

**Argument.** On 1901–2099 every fourth year is a leap year, so the (weekday of 1 January, leap) pattern has
period 28, and shifting the year by 12 moves every date's weekday by 12 + 3 = 15 ≡ 1 days; hence any weekday
shift is a time shift. Across a non-leap century year this correspondence breaks; the computation shows that
no shift s (mod 400) satisfies G_u(y) = F(y + s) for all y when u ≠ Friday.

**Evidence.** `certificate/check.py` (Python `datetime`, proleptic Gregorian): all shifts mod 400 for each weekday,
and the period-28 shifts on 1901–2099. No Lean file.

**Review level.** `rechecked`.
**Prior art.** Partly known: the 400-year totals of 13ths per weekday (688 for Friday, 684-687 for the others; see [Wikipedia](https://en.wikipedia.org/wiki/Friday_the_13th)) already rule out a cyclic shift over the full Gregorian cycle; nobody has drawn the conclusion for [A101312](https://oeis.org/A101312), whose comments still claim the same pattern. Searched OEIS entry, references and history, web. Checked 2026-11-04.
