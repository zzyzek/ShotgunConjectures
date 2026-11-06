"""Assemble a Casas-Alvero file whose core<d> uses reflective certificates.
Usage: python3 gen_reflect_degree.py [--split|--nosplit|--auto] [--msolve] d1 d2 ... > file.lean
--auto (default): split for d >= 6, unsplit below (as in the linear_combination files)."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import gen_reflect, gen_degree

def header():
    h = open(os.path.join(here, 'header.lean')).read()
    rpi = open(os.path.join(here, 'RPI.lean')).read().replace('import Mathlib\n', '', 1)
    old = ('explicit ideal-membership certificate (`linear_combination`, checked by `ring`). The cofactors\n'
           'were found by `certificate/gen_lean.py`')
    assert old in h
    h = h.replace(old, 'explicit ideal-membership certificate, checked by the reflective checker `RPI.check`\n'
                  '(`decide +kernel`; soundness theorem `RPI.check_zero`, proved below). The cofactors\n'
                  'were found by `certificate/gen_reflect.py`')
    i = h.index('namespace CasasAlveroSmall')
    return h[:i] + rpi.strip() + '\n\nopen RPI\n\n' + h[i:]

if __name__ == '__main__':
    flags = [a for a in sys.argv[1:] if a.startswith('--')]
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    mode = ([f for f in flags if f in ('--split', '--nosplit', '--auto')] or ['--auto'])[0]
    if '--msolve' in flags:
        # multimodular-friendly exact solver plus mod-p binary search for exponents (d >= 7)
        import msolve
        msolve.install()
        gen_reflect.FEAS = msolve.feasible
    parts = [header()]
    for d in map(int, args):
        split = (d >= 6) if mode == '--auto' else (mode == '--split')
        gen_degree.CORE = lambda dd, s=split: gen_reflect.core_reflect(dd, s)
        txt, st = gen_degree.section(d)
        parts.append(txt)
    print('\n'.join(parts))
