# A002093: for small k, the last term among the first 10000 (OEIS b-file,
# read from the path given as argv[1]) not divisible by k.  Illustration of
# part (b); the proof is in README.md.
import sys
v = [int(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
assert len(v) == 10000
for k in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49]:
    bad = [x for x in v if x % k]
    print(k, bad[-1] if bad else None)
