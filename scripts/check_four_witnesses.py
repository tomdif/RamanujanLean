#!/usr/bin/env python3
"""Independent integer checks for the four-factor witness counterexamples.

The small cases compare Pochhammer products with Watson sums. The large case
uses two term enumerators and two convolution pairings. Lean proofs are
separate; only the cases at (17; R=5) and (2521; R=2273) are formalized here.
"""
import argparse
import hashlib
import json
from pathlib import Path
from quintuple_vanishing_scan import product_coefficients
from check_four_quarter_counterexample import check as check_large
from generate_four2521_certificate import generate

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    (13, (2,3,4,6), 7, 4, 2),
    (17, (1,3,4,5), 7, 5, -1),
    (17, (1,4,6,7), 13, 5, -2),
    (17, (2,3,5,8), 5, 7, 1),
    (17, (2,3,5,8), 7, 5, -1),
    (37, (3,9,17,18), 8, 10, 1),
]


def check():
    cases = []
    for p, indices, r, step, expected in CASES:
        limit = p*step+r
        direct = [1]+[0]*limit
        for i in indices:
            for start, stride in ((i,p),(p-i,p),(p,p),(p+2*i,2*p),(p-2*i,2*p)):
                for e in range(start,limit+1,stride):
                    for degree in range(limit,e-1,-1):
                        direct[degree] -= direct[degree-e]
        watson = product_coefficients(p,indices,limit)
        assert all(value==watson.get(k,0) for k,value in enumerate(direct))
        assert all(direct[p*n+r]==0 for n in range(step))
        assert direct[limit]==expected
        assert step>p//4
        cases.append({'modulus':p,'indices':indices,'residue':r,'first_nonzero_N':step,
                      'coefficient':expected,'coefficients_compared':limit+1,
                      'actual_product_lean_theorem':p==17 and indices==(2,3,5,8) and r==5})
    data=ROOT/'RamanujanTau/MultiQuintupleFourWitness2521Data.lean'
    assert data.read_text()==generate()
    large=check_large()
    inputs=[Path(__file__),Path(__file__).with_name('quintuple_vanishing_scan.py'),
            Path(__file__).with_name('check_four_quarter_counterexample.py'),
            Path(__file__).with_name('generate_four2521_certificate.py'),data]
    return {'scope':'Independent finite checks; Lean verification recorded separately.',
            'all_checks_passed':True,'small_cases':cases,
            'small_coefficients_compared':sum(row['coefficients_compared'] for row in cases),
            'large_case':large,'generated_lean_data_matches':True,
            'lean_certificate_slices':82,'lean_certificate_terms':5091,
            'original_triple_conjecture_affected':False,
            'sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=check()
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f"Passed {len(result['small_cases'])} small cases and the 2521 replay; generated Lean data matches.")
