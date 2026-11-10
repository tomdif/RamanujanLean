"""find linear_combination certificates with Singular `lift` (goal * mult in ideal(hyps))."""
import sympy as sp, subprocess, tempfile, os, re
def lift(goal, hyps, vars_, mult=1, ordering='dp'):
    names=[str(v) for v in vars_]
    def S(e): return str(sp.expand(e)).replace('**','^')
    src=f"ring r=0,({','.join(names)}),{ordering};\noption(redSB);\n"
    src+="ideal I="+",".join(S(h) for h in hyps)+";\n"
    src+=f"poly g={S(goal*mult)};\n"
    src+="ideal Is=std(I);\nif(reduce(g,Is)!=0){\"NOTIN\";quit;}\nmatrix T=lift(I,g);\nint i;for(i=1;i<=nrows(T);i++){string(T[i,1]);}\nquit;\n"
    with tempfile.NamedTemporaryFile('w',suffix='.sing',delete=False) as f: f.write(src); fn=f.name
    out=subprocess.run(['Singular','-q',fn],capture_output=True,text=True).stdout
    os.unlink(fn)
    lines=[l.strip() for l in out.strip().split('\n') if l.strip()]
    if lines and lines[0]=='NOTIN': return None
    loc={n:v for n,v in zip(names,vars_)}
    coefs=[sp.sympify(l.replace('^','**'),locals=loc) for l in lines]
    # verify
    assert sp.expand(goal*mult-sum(c*h for c,h in zip(coefs,hyps)))==0
    return coefs
def lean(e):
    s=str(sp.factor(e)) if e!=0 else '0'
    s=s.replace('**','^')
    return s
