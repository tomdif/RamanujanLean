# Cross-check sweep.py (new recurrence/memory-lean code, python-flint 0.9) against the original
# scripts/frontier/pattern/l859_compose.py (python-flint 0.6, system python) on small primes.
# Run with system python3: prints original results as JSON lines.
import sys, json, sympy
sys.path.insert(0, '../pattern')
import l859_compose as C
for l in sympy.primerange(int(sys.argv[1]), int(sys.argv[2]) + 1):
    d = C.dimS(l - 1)
    o = C.analyze(l, EXTRA=min(12, l - 1 - d))
    print(json.dumps(dict(l=l, detXi=o['detXi'], krylov=o['krylov'], rkX=o['rkX'], rk_aug=o['rk_aug'],
                          rkXd=o['rkXd'], charpolyXi=o['charpolyXi'], rkD_M=o['rkD_M'])), flush=True)
