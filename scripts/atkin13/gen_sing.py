import json
chi=json.load(open('chi13.json')); co=json.load(open('modeq_coeffs.json')); W=json.load(open('weier13.json'))
cname=['c0','c1','c2','c5','c9','c12']
def mono(k,q):
    s=[]
    for n,a in zip(cname,k):
        if a: s.append(f'{n}^{a}')
    if q: s.append(f'Q^({q})')
    return '*'.join(s) if s else '1'
lines=[]
lines.append('ring r=0,(J1,J2,J3,J4,J5,J6,Q,iQ),dp;')
lines.append('option(redSB);')
rels=[]
for rel in W:
    terms=[]
    for s,m,mon in rel:
        t=f'({s})*Q^{m}*'+'*'.join(f'J{x}' for x in mon)
        terms.append(t)
    rels.append('+'.join(terms))
lines.append('ideal I='+',\n'.join(rels)+',Q*iQ-1;')
lines.append('ideal S=sat(I,J1*J2*J3*J4*J5*J6)[1];')
lines.append('ideal G=std(S);')
lines.append('size(G);')
# c's as rational -> we work in localization: define polys numerators with D
lines.append('poly D=J1*J2*J3*J4*J5*J6;')
# c_r * D:
cD={'c0':'J4*J1*J3*J4*J5*J6','c1':'-J6*J1*J2*J4*J5*J6','c2':'-J2*J2*J3*J4*J5*J6','c5':'J5*J1*J2*J3*J5*J6','c9':'Q*J1*J1*J2*J3*J4*J5','c12':'-J3*J1*J2*J3*J4*J6'}
for n,v in cD.items(): lines.append(f'poly {n}D={v};')
# T*D^2 : T = -1 - c0c1/Q - c2c12 - c5c9
lines.append('poly TD2=-D^2 - c0D*c1D*iQ - c2D*c12D - c5D*c9D;')
for j in range(1,14):
    terms=[]
    for k,q,v in chi[j]:
        d=sum(k)
        parts=[f'({v})']+[f'{n}D^{a}' for n,a in zip(cname,k) if a]
        if q>0: parts.append(f'Q^{q}')
        if q<0: parts.append(f'iQ^{-q}')
        parts.append(f'D^{2*7+j-d}')   # scale everything to D^{j+14}
        terms.append('*'.join(parts))
    lines.append(f'poly X{j}='+'+'.join(terms)+';')
    a=co[f'phi{13-j}'] if j<13 else [1]
    fterms=[]
    for i,ai in enumerate(a):
        if ai: fterms.append(f'({ai})*TD2^{7-i}*D^{j+14-2*(7-i)}')
    lines.append(f'poly F{j}='+('+'.join(fterms) if fterms else '0')+';')
    lines.append(f'"j={j}"; reduce(X{j}-F{j},G)==0;')
lines.append('quit;')
open('mem.sing','w').write('\n'.join(lines))
