#!/usr/bin/env python3
"""Independently check every affine identity in a four-factor certificate.

Uses only exact standard-library arithmetic. The identities bijectively pair
all eight positive Watson branches with all eight negative branches. No
coefficient truncation or discovery code is trusted.
"""
import argparse
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
import json
from pathlib import Path


def dot(x,y):
    return sum(a*b for a,b in zip(x,y))


def transpose(a):
    return list(map(list,zip(*a)))


def multiply(a,b):
    return [[dot(row,col) for col in transpose(b)] for row in a]


def vector(a,x):
    return [dot(row,x) for row in a]


def determinant(a):
    a=[list(map(Fraction,row)) for row in a]
    value=Fraction(1)
    for j in range(len(a)):
        k=next((k for k in range(j,len(a)) if a[k][j]),None)
        if k is None:
            return Fraction(0)
        if k!=j:
            a[j],a[k]=a[k],a[j]
            value=-value
        pivot=a[j][j]
        value*=pivot
        for i in range(j+1,len(a)):
            t=a[i][j]/pivot
            a[i]=[x-t*y for x,y in zip(a[i],a[j])]
    return value


def check(record):
    p=record['p'];v=record['indices'];b=record['basis']
    assert p>=5 and all(p%d for d in range(2,isqrt(p)+1))
    assert len(v)==4 and all(0<2*x<p for x in v)
    assert len(b)==4 and all(len(row)==4 for row in b)
    assert all(isinstance(x,int) for row in b for x in row)
    assert abs(determinant(b))==p
    assert all(dot(v,col)%p==0 for col in transpose(b))
    # Full-index containment identifies B Z^4 with the residue kernel.
    assert gcd(v[-1],p)==1
    h=multiply(transpose(b),b)
    assert h==record['gram']
    q=[[3*p*x for x in row] for row in h]
    positive={bits for bits in product((0,1),repeat=4) if sum(bits)%2==0}
    negative=set(product((0,1),repeat=4))-positive
    checked=0
    for residue,edges in record['certificates'].items():
        residue=int(residue)
        assert 0<=residue<p and len(edges)==8
        assert {tuple(edge[0]) for edge in edges}==positive
        assert {tuple(edge[1]) for edge in edges}==negative
        def polynomial(bits):
            displacement=[0,0,0,((residue-dot(v,bits))*pow(3*v[-1],-1,p))%p]
            ell=[6*x+p*(2*bit-1) for x,bit in zip(v,bits)]
            linear=vector(transpose(b),[6*p*x+y for x,y in zip(displacement,ell)])
            constant=3*p*dot(displacement,displacement)+dot(ell,displacement)+2*dot(v,bits)
            return linear,constant
        for source,target,a,c in edges:
            assert len(a)==4 and all(len(row)==4 for row in a) and len(c)==4
            assert all(isinstance(x,int) for row in a for x in row)
            assert all(isinstance(x,int) for x in c)
            assert abs(determinant(a))==1
            assert multiply(multiply(transpose(a),q),a)==q
            ls,cs=polynomial(source);lt,ct=polynomial(target)
            qc=vector(q,c)
            assert vector(transpose(a),[2*x+y for x,y in zip(qc,lt)])==ls
            assert dot(c,qc)+dot(lt,c)+ct==cs
            checked+=1
    return checked


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--negative-control',action='store_true')
    args=parser.parse_args()
    record=json.loads(args.certificate.read_text())
    count=check(record)
    if args.negative_control:
        changed=json.loads(json.dumps(record))
        first=next(iter(changed['certificates'].values()))
        first[0][3][0]+=1
        try:
            check(changed)
        except AssertionError:
            pass
        else:
            raise AssertionError('corrupted translation was accepted')
    print(f'Passed: {count} exact affine branch identities; residues {list(record["certificates"])}.')
