# Read Chernykh's amicable-pair list (header line, two factorization lines, blank)
# from stdin; write odd pairs to argv[1]; report mod-4 classes and Euler-form test.
#
import sys
def parse(s):
  n, f = s.split('=')
  fs = []
  for t in f.split('*'):
    if '^' in t:
      p, e = t.split('^'); fs.append((int(p), int(e)))
    else:
      fs.append((int(t), 1))
  return int(n), fs
def euler(fs):
  odd = [(p, e) for (p, e) in fs if e % 2 == 1]
  return len(odd) == 1 and odd[0][0] % 4 == 1 and odd[0][1] % 4 == 1
out = open(sys.argv[1], 'w')
lines = []
tot = odd = cong = eu = 0
def handle(rec):
  global tot, odd, cong, eu
  fl = [l for l in rec if '=' in l]
  if len(fl) != 2:
    return
  tot += 1
  (m, fm), (n, fn) = parse(fl[0]), parse(fl[1])
  assert m == eval_f(fm) and n == eval_f(fn)
  if m % 2 == 1 and n % 2 == 1:
    odd += 1
    out.write(fl[0] + ' ' + fl[1] + '\n')
    if (m % 4) == (n % 4):
      cong += 1; print('CONGRUENT', fl, flush=True)
    if euler(fm) or euler(fn):
      eu += 1; print('EULER', fl, flush=True)
def eval_f(fs):
  r = 1
  for p, e in fs:
    r *= p ** e
  return r
rec = []
for line in open(0, encoding="latin-1"):
  line = line.strip()
  if not line:
    if rec: handle(rec)
    rec = []
  else:
    rec.append(line)
if rec: handle(rec)
print('pairs', tot, 'odd', odd, 'congruent', cong, 'euler', eu)
