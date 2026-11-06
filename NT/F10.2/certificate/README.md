`benkoski.c` (from the scan, scratch/nt-EF): prints every n = 9 (mod 10), lo <= n <= N, with 2^n = 4 (mod n)
(64-bit arithmetic, valid for n < 2^32). Run 2026-11-06: `./benk 1210344599 9` printed only 1210344599
(47 s, one core). So 1210344599 is the least positive n = 9 (mod 10) with 2^n = 4 (mod n).
