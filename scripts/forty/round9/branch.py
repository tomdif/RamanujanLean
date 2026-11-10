"""round 9: the branch of (3.39)->(3.40) modulo q^3; quotients B with  lhs - rhs - A*h = B*x^3."""
import sympy as sp
x,y,h,hn=sp.symbols('x y h hn')
def quo(e):
    e=sp.expand(e); q,r=sp.div(e, x**3, x); assert r==0, r; return sp.expand(q)
# piG: h: y*((1-x)*(1-x^6)) = 1
print('G', quo(y-(1+x+x**2)-(1+x+x**2)*(y*(1-x)*(1-x**6)-1)))
print('NgG', quo(y-(1-x+x**2)-(1+x**2)*(y*(1-x**2)*(1-x**22)-(1-x)*(1-x**11))))
print('S2G', quo(y-(1+x**2)-(1+x**2)*(y*(1-x**2)*(1-x**12)-1)))
S2U=1-x**6; S2V=(1+x**2)+x**14; V=(1+x+x**2)+x**7*h; NgV=(1-x+x**2)-x**7*hn
W=(1+x**6)*(1+x**28); c=(1-x**2)*(1-x**6); d=1
E=((S2U*S2V)**2+2*x**2)*d-c*(V*NgV)*W
print('E', quo(E-4*x**2))
