# Remove LeanArchitect blueprint metadata from a PNT+ Lean file:
# `import Architect`, `@[blueprint ...]` attribute entries and
# `blueprint_comment /-- ... -/` commands. Only metadata is removed;
# declarations are untouched. Exits nonzero on any unexpected form.
#
import sys, re
src = open(sys.argv[1]).read()
out = []; i = 0; n = len(src); removed = 0

def skip_comment(j):
    # src[j:j+2] == '/-'; return index after matching '-/' (nested).
    #
    d = 0
    while j < n:
        if src.startswith('/-', j): d += 1; j += 2
        elif src.startswith('-/', j):
            d -= 1; j += 2
            if d == 0: return j
        else: j += 1
    raise SystemExit('unterminated comment')

def skip_string(j):
    j += 1
    while src[j] != '"':
        j += 2 if src[j] == '\\' else 1
    return j + 1

def attr_end(j):
    # j points just after '@['; return index of matching ']'.
    #
    depth = 0
    while j < n:
        c = src[j]
        if src.startswith('/-', j): j = skip_comment(j); continue
        if c == '"': j = skip_string(j); continue
        if src.startswith('--', j): j = src.index('\n', j); continue
        if c in '([{': depth += 1
        elif c in ')}': depth -= 1
        elif c == ']':
            if depth == 0: return j
            depth -= 1
        elif c == ',' and depth == 0:
            raise SystemExit('combined attribute list at offset %d' % j)
        j += 1
    raise SystemExit('unterminated attribute')

while i < n:
    if src.startswith('/-', i) and not src.startswith('/--', i) and (i == 0 or src[i-1] != '@'):
        j = skip_comment(i); out.append(src[i:j]); i = j; continue
    if src.startswith('@[blueprint', i) and not src[i+11].isalnum() and src[i+11] != '_':
        e = attr_end(i + 2); i = e + 1
        if i < n and src[i] == '\n': i += 1
        removed += 1; continue
    if src.startswith('blueprint_comment', i) and (i == 0 or src[i-1] == '\n'):
        j = src.index('/-', i); j = skip_comment(j); i = j
        if i < n and src[i] == '\n': i += 1
        removed += 1; continue
    if src.startswith('import Architect\n', i) and (i == 0 or src[i-1] == '\n'):
        i += len('import Architect\n'); continue
    out.append(src[i]); i += 1
res = ''.join(out)
if 'blueprint' in re.sub(r'/-.*?-/|--[^\n]*', '', res, flags=re.S):
    for k, l in enumerate(res.split('\n')):
        if 'blueprint' in l: print('LEFT', k+1, l, file=sys.stderr)
open(sys.argv[2], 'w').write(res)
print(removed, sys.argv[1])
