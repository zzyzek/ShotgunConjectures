#!/usr/bin/env python3
# Build OUTREACH-OEIS.md: OEIS entries whose conjecture we settled and that
# OEIS does not yet record as settled, from the prior-art review in
# problems.jsonl. Draft comments are starting points to edit before sending.
#
# Usage: python3 -I tools/build_outreach.py
#
import json, os, re, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(HERE)
sys.path.insert(0, os.path.join(HERE, 'tools'))
from build_readmes import parse, natkey

# Book problems whose conjecture also stands in an OEIS entry (from the
# prior-art notes).
#
EXTRA = {
  'COM-C016': 'A182132', 'COM-C032': 'A215944', 'COM-C037': 'A215343',
  'COM-C042': 'A182207', 'COM-C044': 'A212843',
  'NT-B10.3': 'A045764', 'NT-B41.5': 'A229487',
}
REPO = 'https://github.com/zzyzek/ShotgunConjectures/tree/main'
REPO_HOME = 'https://github.com/zzyzek/ShotgunConjectures'


def lean_level(e):
  return { 'lean-proof': 'Lean proof', 'lean-witness': 'Lean (partial)' }.get(e['review'], 'paper proof')


def draft(anum, e, res):
  verdict = { 'proved': 'The conjecture is true', 'disproved': 'The conjecture is false',
              'corrected-and-proved': 'The conjecture is misstated as written; the corrected form is true' }.get(e['result'], 'Remark')
  where = ( 'proof verified in Lean 4' + ( ' + Mathlib' if (e.get('lean') or '').endswith('_mathlib.lean') else '' )
            if e['review'] == 'lean-proof' else 'proof' )
  res = re.sub(r'^(True|False)[.:;,]?\s*', '', re.sub(r'\s+', ' ', res)).strip()
  return '%s%s (%s: %s/%s). - _<Name>_, <Mon DD YYYY>' % (verdict, ( ': ' + res if res else '' ), where, REPO, e['dir'])


def rec(anum, e, settled_by, comment):
  return {
    'anum': anum, 'oeis_url': 'https://oeis.org/' + anum, 'settled_by': settled_by,
    'verdict': { 'proved': 'true', 'disproved': 'false', 'corrected-and-proved': 'trivial or misstated' }.get(e['result'], e['result']),
    'lean': { 'lean-proof': 'full', 'lean-witness': 'partial' }.get(e['review'], 'none'),
    'path': e['dir'], 'proof_url': REPO + '/' + e['dir'],
    'comment': comment,
  }


def main():
  ents = [json.loads(l) for l in open('problems.jsonl', encoding='utf-8') if l.strip()]
  # Hand-written drafts (outreach-drafts.jsonl) replace the generated ones.
  #
  drafts = {}
  if os.path.exists('outreach-drafts.jsonl'):
    for l in open('outreach-drafts.jsonl', encoding='utf-8'):
      if l.strip():
        d = json.loads(l)
        drafts[(d['anum'], d['id'])] = d['comment'].replace('<REPO>', REPO)
  rows = {}
  for e in ents:
    pa = e.get('prior_art') or {}
    if (e['category'] != 'scan resolution') or (pa.get('verdict') not in ('new', 'partly-known')) or pa.get('conflict'):
      continue
    if e['id'].startswith('OEIS-'):
      if pa.get('oeis_status') != 'conjecture':
        continue
      anum = e['id'][5:]
    elif e['id'] in EXTRA:
      anum = EXTRA[e['id']]
    else:
      continue
    rows.setdefault(anum, []).append(e)

  # Known in the literature but still labelled a conjecture in OEIS: a
  # cross-reference comment only.
  #
  xref = sorted([e for e in ents if (e['category'] == 'scan resolution') and e['id'].startswith('OEIS-') and
                 ((e.get('prior_art') or {}).get('verdict') == 'known') and
                 ((e.get('prior_art') or {}).get('oeis_status') == 'conjecture')], key=lambda e: natkey(e['id']))
  tiers = [('Substantive (not an immediate consequence of a known theorem)', lambda e: not e['prior_art'].get('immediate')),
           ('Immediate from a known theorem or short argument, still open in OEIS', lambda e: e['prior_art'].get('immediate'))]
  out = ['# OEIS outreach list', '',
         'OEIS entries whose conjecture this project settled and which OEIS does not yet record as settled',
         '(prior-art review 2026-11-04: current entry, entries citing it, edit history, web, arXiv).',
         'Each draft comment is a starting point: shorten it to OEIS style and sign it. "Partly known" means a source covers part of it; the note says which part.', '',
         '%d entries.' % len(rows), '']
  for title, pick in tiers:
    sel = sorted([a for a, es in rows.items() if pick(es[0])], key=natkey)
    out += ['## %s (%d)' % (title, len(sel)), '']
    for a in sel:
      for e in rows[a]:
        t, sec = parse(os.path.join(e['dir'], 'README.md'))
        pa = e['prior_art']
        out += ['### [%s](https://oeis.org/%s): %s' % (a, a, t), '',
                '- Problem: [%s](%s/README.md) (%s, %s). Lean: %s%s.' % (e['id'], e['dir'], e['result'], pa['verdict'], lean_level(e),
                  ( ', [`%s`](%s)' % (os.path.basename(e['lean']), e['lean']) if e.get('lean') else '' )),
                '- Prior art: %s' % re.sub(r'\s+', ' ', pa.get('note', '')),
                '- Draft comment:', '', '  > ' + drafts.get((a, e['id']), draft(a, e, sec.get('Result', ''))), '']
  out += ['## Known elsewhere, still labelled a conjecture in OEIS (%d): cross-reference only' % len(xref), '']
  for e in xref:
    t, _ = parse(os.path.join(e['dir'], 'README.md'))
    a = e['id'][5:]
    out += ['- [%s](https://oeis.org/%s): %s. Known from: %s' % (a, a, t, re.sub(r'\s+', ' ', e['prior_art'].get('note', '')))]
  out.append('')
  open('OUTREACH-OEIS.md', 'w', encoding='utf-8').write('\n'.join(out) + '\n')

  # Machine-readable list: one object per OEIS entry that OEIS still
  # presents as open, settled either here or in the literature.
  #
  os.makedirs('outreach', exist_ok=True)
  recs = []
  for a in sorted(rows, key=natkey):
    es = sorted(rows[a], key=lambda e: (not e['id'].startswith('OEIS-'), e['id']))
    e = es[0]
    r = rec(a, e, 'this project', drafts.get((a, e['id']), draft(a, e, parse(os.path.join(e['dir'], 'README.md'))[1].get('Result', ''))))
    r['also'] = [x['dir'] for x in es[1:]]
    recs.append(r)
  for e in xref:
    recs.append(rec(e['id'][5:], e, 'literature', 'This conjecture is already settled in the literature: %s'
                    % re.sub(r'\s+', ' ', e['prior_art'].get('note', ''))))
  recs.sort(key=lambda r: natkey(r['anum']))
  with open('outreach/oeis-updates.jsonl', 'w', encoding='utf-8') as f:
    for r in recs:
      f.write(json.dumps(r, ensure_ascii=False) + '\n')
  t = ['# OEIS entries presented as open that are settled', '',
       'One line per OEIS entry (%d). `settled by`: this project, or the literature (cross-reference only).' % len(recs),
       '`Lean`: full = the whole result is proved in Lean; partial = one named step is outside Lean; none = written proof.',
       'Machine-readable: [oeis-updates.jsonl](oeis-updates.jsonl).', '',
       '| A-number | settled by | verdict | Lean | proof |', '|---|---|---|---|---|']
  for r in recs:
    t.append('| [%s](%s) | %s | %s | %s | [%s](%s) |' % (r['anum'], r['oeis_url'], r['settled_by'], r['verdict'],
             r['lean'], r['path'], r['proof_url']))
  open('outreach/OEIS-LIST.md', 'w', encoding='utf-8').write('\n'.join(t) + '\n')

  # Cover note; counts are per A-number.
  #
  per = {}
  for r in recs:
    per.setdefault(r['anum'], r)
  n = len(per)
  k = lambda f, v: sum(1 for r in per.values() if r[f] == v)
  letter = '''Subject: Settled conjectures in %(n)d OEIS entries (list and proofs)

Dear OEIS editors,

The attached list covers %(n)d OEIS entries whose comments state a conjecture
that is now settled: %(t)d true, %(f)d false, %(m)d trivial or misstated as
written. For %(x)d of them the answer is already in the literature and the
entry only needs a cross-reference; for the other %(o)d no source we found
states the full answer
(entry, cross-referenced entries, edit history, web, arXiv; checked
2026-11-04).

The results come from an AI-assisted scan (Claude agents) of open problems.
Each was re-derived by a second agent, and %(full)d are proved in full in
Lean 4 (core Lean or Mathlib), checked by the Lean kernel; %(part)d are partly
formalised (the remaining step is named) and %(none)d have written proofs
only. Every proof, its Lean file and the scripts are in

  <REPO>

one directory per problem. Where a conjecture needed an interpretation (an
index shift, a reading of the definition), the problem README says which.

Files:
  outreach/OEIS-LIST.md       one line per entry
  outreach/oeis-updates.jsonl one JSON object per entry: anum, kind,
                              verdict, lean (full/partial/none), problem path,
                              a draft comment, prior-art note and sources

The draft comments are suggestions; edit or ignore them as you see fit.
Corrections are welcome.

<Name>
''' % dict(n=n, t=k('verdict', 'true'), f=k('verdict', 'false'), m=k('verdict', 'trivial or misstated'),
           x=k('settled_by', 'literature'), o=n - k('settled_by', 'literature'),
           full=k('lean', 'full'), part=k('lean', 'partial'), none=k('lean', 'none'))
  open('outreach/COVER-LETTER.txt', 'w', encoding='utf-8').write(letter.replace('<REPO>', REPO_HOME))
  print(len(rows), [len([a for a, es in rows.items() if p(es[0])]) for _, p in tiers])


if __name__ == '__main__':
  main()
