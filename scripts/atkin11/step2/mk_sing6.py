import pickle, sympy as sp, sys
exec(open('mk_singular.py').read().split("E=pickle.load")[0])
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7=sp.symbols('c0 c1 c2 c4 c7')
sub={c0:t[3]/t[1], c1:-t[1]/t[0], c2:-t[4]/t[2], c7:t[2]/t[3], c4:-Q*t[0]/t[4]}
def clear(expr):
    n,d=sp.fraction(sp.together(sp.expand(expr)))
    return sp.expand(n)
N11=clear(E[11].subs(sub)-sp.Mul(*t)**12/Q**5)
s=open('test3b.sing').read()
s=s.replace("ideal G=std(W);","ideal W2=W,"+str(N11).replace('**','^')+";\nideal S=sat(W2,t1*t2*t3*t4*t5*Q);\nS=std(S);\n\"sat size\"; size(S);\nideal G=S;",1)
s=s.replace('in W:"','in W+N11 sat:"')
open('test6.sing','w').write(s)
print(len(str(N11)))
