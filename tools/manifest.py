#!/usr/bin/env python3
# Build problems.jsonl and the <SRC>/<REST>/ skeleton from the scan
# repo (../open-problems): every record the scan resolved itself
# (resolver == "ours"). Existing per-problem files are never overwritten;
# the index is regenerated, keeping fields that agents filled in.
#
# Usage: python3 -I tools/manifest.py
#
import json, os, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCAN = os.path.join(os.path.dirname(HERE), 'open-problems')
sys.path.insert(0, SCAN)
from progress import resolver, VERIFIED, title_of

SOURCES = {
  'NT':   ('Guy, Unsolved Problems in Number Theory, 3rd ed. (Springer 2004)', 'guy-upint'),
  'GEO':  ('Croft, Falconer, Guy, Unsolved Problems in Geometry (Springer 1991)', 'cfg-geometry'),
  'COM':  ('Coman, Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes (2013)', 'coman-psp'),
  'OEIS': ('OEIS, https://oeis.org/ (conjecture comment; list at OEIS wiki Talk:Conjectures/List)', 'oeis'),
  'BMP':  ('Brass, Moser, Pach, Research Problems in Discrete Geometry (Springer 2005)', 'bmp-rpdg'),
  'SHK':  ('Shanks, Solved and Unsolved Problems in Number Theory, 3rd ed. (Chelsea 1985)', 'shanks-supnt'),
  'AMR':  ('Open-problem lists linked from https://amathr.org/problems/', 'amathr'),
  'FAM':  ('Famous open problems (Wikipedia list of unsolved problems, MathWorld, Guy); weaker results only', 'famous'),
}

def paths(rid):
  src, rest = rid.split('-', 1)
  mod = rest.replace('.', '_').replace('-', '_')
  return src, ('%s/%s' % (src, rest)), ('%s/%s/%s.lean' % (src, rest, mod))

def main():
  old = {}
  idx = os.path.join(HERE, 'problems.jsonl')
  if os.path.exists(idx):
    for l in open(idx, encoding='utf-8'):
      if l.strip():
        r = json.loads(l)
        old[r['id']] = r
  # Agent updates (updates/<group>.jsonl, one object per line with an id)
  # override the stored fields; later files win.
  #
  upd_dir = os.path.join(HERE, 'updates')
  if os.path.isdir(upd_dir):
    for fn in sorted(os.listdir(upd_dir)):
      if fn.endswith('.jsonl'):
        for l in open(os.path.join(upd_dir, fn), encoding='utf-8'):
          if l.strip():
            u = json.loads(l)
            old.setdefault(u['id'], {}).update(u)
  out = []
  for fn in sorted(os.listdir(os.path.join(SCAN, 'triage'))):
    if not fn.endswith('.jsonl'):
      continue
    for l in open(os.path.join(SCAN, 'triage', fn), encoding='utf-8'):
      if not l.strip():
        continue
      r = json.loads(l)
      ours = (r.get('status') in ('solved', 'false', 'trivial')) and (resolver(r) == 'ours')
      if (not ours) and (r['id'] not in old):
        continue
      if ours:
        cat = 'scan resolution'
      elif r.get('status') in ('solved', 'false', 'trivial'):
        cat = 'answered elsewhere; confirmed or written up here'
      else:
        cat = 'disputed or partial; not a resolution'
      src, pdir, lean = paths(r['id'])
      e = {
        'id': r['id'], 'source': SOURCES[src][0], 'section': r.get('section', ''),
        'category': cat,
        'title': title_of(r), 'result': { 'solved': 'proved', 'false': 'disproved', 'trivial': 'trivial or misstated' }.get(r['status'], r['status']),
        'summary': r.get('status_note', ''), 'dir': pdir,
        'lean': None, 'lean_status': 'not started',
        'review': ( 'rechecked' if r['id'] in VERIFIED else 'agent' ),
        'status_checked_online': bool(r.get('web_checked')),
        'prior_art_search': False,
      }
      if r['id'] in old:
        for k in ('lean', 'lean_status', 'review', 'prior_art_search', 'certificate', 'depends_on', 'notes', 'disputed', 'result', 'methods', 'prior_art'):
          if k in old[r['id']]:
            e[k] = old[r['id']][k]
        if 'category_override' in old[r['id']]:
          e['category'] = old[r['id']]['category_override']
        if 'summary_override' in old[r['id']]:
          e['summary'] = old[r['id']]['summary_override']
      out.append(e)
      os.makedirs(os.path.join(HERE, pdir), exist_ok=True)
  # Entries that come from outside the scan (updates with "standalone": true).
  #
  have = { e['id'] for e in out }
  for rid, u in old.items():
    if u.get('standalone') and (rid not in have):
      src, pdir, lean = paths(rid)
      e = { 'id': rid, 'source': SOURCES[src][0], 'section': u.get('section', ''),
            'category': u['category'], 'title': u.get('title', ''), 'result': u.get('result', ''),
            'summary': u.get('summary', ''), 'dir': pdir, 'lean': u.get('lean'),
            'lean_status': u.get('lean_status', 'none'), 'review': u.get('review', 'agent'),
            'status_checked_online': True, 'prior_art_search': u.get('prior_art_search', False) }
      for k in ('certificate', 'depends_on', 'notes', 'methods', 'prior_art'):
        if k in u: e[k] = u[k]
      out.append(e)
  with open(idx, 'w', encoding='utf-8') as f:
    for e in sorted(out, key=lambda e: e['id']):
      f.write(json.dumps(e, ensure_ascii=False) + '\n')
  by = {}
  for e in out:
    k = (e['id'].split('-')[0], e['category'][:4])
    by[k] = by.get(k, 0) + 1
  print('%d entries' % len(out), sorted(by.items()))

if __name__ == '__main__':
  main()
