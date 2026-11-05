"""Rewrite a monolithic core<d> proof (from gen_lean.core) into one declaration per
linear_combination (Lean caches are per declaration; the degree-6 certificate needs this to stay
under 6 GB)."""
import re

def split_core(txt, d):
    L = txt.split('\n')
    head = []
    k = 0
    while not L[k].rstrip().endswith(':= by'):
        head.append(L[k]); k += 1
    head.append(L[k]); k += 1
    htxt = '\n'.join(head)
    nb = d - 2
    bvars = [f'b{j}' for j in range(1, nb + 1)]
    hyp = dict(re.findall(r'\((h[QH]\d+) : (.*?) = 0\)', htxt))
    body = L[k:]
    rs, ts = {}, {}
    i = 0
    while i < len(body):
        l = body[i]
        m = re.match(r'  have r(\d+) : \((\d+):K\) \* \((.*)\) = 0 := by$', l)
        if m:
            rs[int(m.group(1))] = (m.group(2), m.group(3), body[i+1].strip()); i += 2; continue
        m = re.match(r'  have t(\d+) : \((\d+):K\) \* (b\d+)\^(\d+) = 0 := by$', l)
        if m:
            ts[int(m.group(1))] = (m.group(2), m.group(3), m.group(4), body[i+1].strip()); i += 2; continue
        i += 1
    assert len(rs) == nb and len(ts) == nb
    def opt(comb):
        return 'set_option maxHeartbeats 0 in\n' if len(comb) > 20000 else ''
    out = []
    for i in range(1, nb + 1):
        den, R, comb = rs[i]
        out.append(f'{opt(comb)}theorem core{d}_r{i} {{K : Type*}} [Field K] ({" ".join(bvars)} x{i} : K)\n'
                   f'    (hQ{i} : {hyp[f"hQ{i}"]} = 0) (hH{i} : {hyp[f"hH{i}"]} = 0) :\n'
                   f'    ({den}:K) * ({R}) = 0 := by\n  {comb}\n')
    shyps = ' '.join(f'(s{i} : ({rs[i][1]}) = 0)' for i in range(1, nb + 1))
    for j in range(1, nb + 1):
        N, v, e, comb = ts[j]
        out.append(f'{opt(comb)}theorem core{d}_t{j} {{K : Type*}} [Field K] ({" ".join(bvars)} : K)\n'
                   f'    {shyps} :\n    ({N}:K) * {v}^{e} = 0 := by\n  {comb}\n')
    main = [htxt]
    bs = ' '.join(bvars)
    for i in range(1, nb + 1):
        main.append(f'  have s{i} := (mul_eq_zero.mp (core{d}_r{i} {bs} x{i} hQ{i} hH{i})).resolve_left (by norm_num)')
    ss = ' '.join(f's{i}' for i in range(1, nb + 1))
    for j in range(1, nb + 1):
        N, v, e, _ = ts[j]
        main.append(f'  have z{j} : {v} = 0 := pow_eq_zero_iff (n := {e}) (by norm_num) |>.mp\n'
                    f'    ((mul_eq_zero.mp (core{d}_t{j} {bs} {ss})).resolve_left (by norm_num))')
    main.append('  exact ' + ('z1' if nb == 1 else '⟨' + ', '.join(f'z{j}' for j in range(1, nb + 1)) + '⟩'))
    out.append('\n'.join(main))
    return '\n'.join(out)
