"""
OEIS access: batched, cached, paced.

Pattern. Status checks dominate triage cost. The search endpoint returns up to
10 entries per request (`id:A1|id:A2|...`), so batch, cache every response
under data/oeis-cache/ (git-ignored), and pace requests a few seconds apart.
Read the current entry before investing: many old conjectures are now
marked proved, refuted, or reworded.
"""
import os, re, time, urllib.request

# Repository root (oplib lives in methods/oplib/); the cache is under data/.
#
ROOT  = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CACHE = os.path.join(ROOT, 'data', 'oeis-cache')
PAUSE = 4.0


def _get(url):
  req = urllib.request.Request(url, headers={ 'User-Agent': 'open-problems-scan (research; low rate)' })
  with urllib.request.urlopen(req, timeout=60) as r:
    return r.read().decode('utf-8', 'replace')


def fetch(anums, refresh=False, pause=PAUSE):
  """Return {A-number: entry text (internal format)} for the given ids."""
  os.makedirs(CACHE, exist_ok=True)
  out, todo = {}, []
  for a in anums:
    p = os.path.join(CACHE, a + '.txt')
    if os.path.exists(p) and (not refresh):
      out[a] = open(p, encoding='utf-8').read()
    else:
      todo.append(a)
  for i in range(0, len(todo), 10):
    batch = todo[i:i + 10]
    txt = _get('https://oeis.org/search?q=' + '|'.join('id:' + a for a in batch) + '&fmt=text')
    for a in batch:
      lines = [l for l in txt.splitlines() if re.match(r'^%[A-Za-z] ' + a + r'\b', l)]
      entry = '\n'.join(lines) + '\n'
      open(os.path.join(CACHE, a + '.txt'), 'w', encoding='utf-8').write(entry)
      out[a] = entry
    if i + 10 < len(todo):
      time.sleep(pause)
  return out


def field(entry, code):
  """All lines of one field (%S %T %U data, %N name, %C comments, %F formulas,
  %O offset, ...), with the '%X Annnnnn ' prefix removed."""
  return [re.sub(r'^%\w A\d{6} ?', '', l) for l in entry.splitlines() if l.startswith('%' + code + ' ')]


def data(entry):
  """Terms from %S %T %U, and the offset (first index)."""
  s = ''.join(field(entry, 'S') + field(entry, 'T') + field(entry, 'U'))
  terms = [int(x) for x in s.replace(' ', '').split(',') if x]
  off = field(entry, 'O')
  first = int(off[0].split(',')[0]) if off else 0
  return terms, first


def bfile(anum, refresh=False):
  """b-file as list of (n, a(n)); cached."""
  os.makedirs(CACHE, exist_ok=True)
  p = os.path.join(CACHE, 'b' + anum[1:] + '.txt')
  if refresh or (not os.path.exists(p)):
    txt = _get('https://oeis.org/%s/b%s.txt' % (anum, anum[1:]))
    open(p, 'w', encoding='utf-8').write(txt)
    time.sleep(PAUSE)
  out = []
  for l in open(p, encoding='utf-8'):
    t = l.split()
    if (len(t) >= 2) and t[0].lstrip('-').isdigit() and (not l.startswith('#')):
      out.append((int(t[0]), int(t[1])))
  return out


def mentions_resolution(entry):
  """Comment/formula lines that look like a resolution note (proved, refuted, ...)."""
  pat = re.compile(r'(?i)\b(proved|proof|disproved|refuted|counterexample|false|is true|confirmed)\b')
  return [l for l in field(entry, 'C') + field(entry, 'F') if pat.search(l)]
