# Check the Korselt-residue conjectures against Pinch's list of all
# Carmichael numbers < 1e21 (A182151, A182206, A182207 for p <= 97,
# A182208, A182381, A182515, A182532).
#
import gzip, sys
P207 = [p for p in (3, 7, 19, 31, 37, 79, 97)]
viol = {k: [] for k in ('A182151', 'A182206', 'A182207', 'A182208', 'A182381', 'A182515', 'A182532')}
cnt = {k: 0 for k in viol}
with gzip.open(sys.argv[1], 'rt') as f:
  for line in f:
    if not line[:1].isdigit(): continue
    C = int(line.split()[0])
    if C % 31 == 0:
      cnt['A182151'] += 1
      if C % 2790 not in (31, 961, 1891): viol['A182151'].append(C)
    if C % 2701 == 0:
      cnt['A182206'] += 1
      m = C // 2701
      if not (m >= 91 and (m - 91) % 18 == 0): viol['A182206'].append(C)
    for p in P207:
      q = p * (2 * p - 1)
      if C % q == 0:
        cnt['A182207'] += 1
        m = C // q
        if not (m >= p and (m - p) % (2 * p - 2) == 0): viol['A182207'].append((p, C))
    if C % 7 == 0:
      cnt['A182208'] += 1
      if (C // 7) % 6 != 1: viol['A182208'].append(C)
    if C % 493 == 0:
      cnt['A182381'] += 1
      if C % 952 != 561: viol['A182381'].append(C)
    if C % 1541 == 0:
      cnt['A182515'] += 1
      m = C // 1541
      if not (m >= 23 and (m - 23) % 66 == 0): viol['A182515'].append(C)
    if C % 119 == 0:
      cnt['A182532'] += 1
      m = C // 119
      want = {1: 119, 5: 95, 3: 47, 9: 71}.get(C % 10)
      if want is not None and m % 120 != want: viol['A182532'].append(C)
for k in viol: print(k, 'tested', cnt[k], 'violations', viol[k][:5])
