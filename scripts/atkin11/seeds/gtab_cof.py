import sympy as sp, subprocess
g2,g3,z=sp.symbols('g2 g3 z')
g=[1,g2,g3,g2**2-g3,g2*(g2**2-g3)]
tab={(1,1):[(2,1),(3,1)],(1,2):[(3,1),(5,11)],(1,3):[(4,1)],(1,4):[(5,1),(6,12),(7,11)],(2,2):[(4,1),(5,-1)],(2,3):[(5,1),(6,11)],(2,4):[(6,1),(7,11),(8,11)],(3,3):[(6,1),(7,11)],(3,4):[(7,1),(8,12),(10,121)],(4,4):[(8,1),(9,12),(10,11),(11,121)]}
R1=g2*g3-(g2**2-g3+11*z); R2=g3**2-(g2**3-g2*g3-z)
out={}
for (i,r),l in tab.items():
    rhs=sum(s*z**(d//5)*g[d%5] for d,s in l)
    D=sp.expand(g[i]*g[r]-rhs)
    # find a,b with D = a R1 + b R2 via Singular lift
    sing=f"""ring R=0,(g3,g2,z),dp; ideal I={sp.sstr(R1)},{sp.sstr(R2)}; poly D={sp.sstr(D)};
matrix T=lift(I,D); print(T[1,1]); print("SEP"); print(T[2,1]); quit;"""
    o=subprocess.run(['Singular','-q'],input=sing,capture_output=True,text=True).stdout
    a,b=[x.strip() for x in o.split("SEP")]
    a,b=sp.sympify(a),sp.sympify(b)
    assert sp.expand(a*R1+b*R2-D)==0,(i,r)
    out[(i,r)]=(a,b); print(i,r,a,"|",b)
