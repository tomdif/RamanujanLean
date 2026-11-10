import sympy as sp
x1,x2,y1,y2,q=sp.symbols('x1 x2 y1 y2 q')
c1=x1*x2; d1=y1*y2
V=(y1/c1-q**2*x1/d1)/x2
Vm=(y2/c1+q**2*x2/d1)/x1
star=(c1*V*Vm)**2-(d1*c1**2*(Vm*x1**2-V*x2**2)/(2*q))**2-4*q**4/(c1*d1)
Nst=sp.factor(sp.numer(sp.together(star)))
print("star:",Nst)
S=V**2*x2/y2
t38=S**4-q*S**2-(y2**3/x2**3)*(1+q**2*x2**3/y2**3)**2
N38=sp.factor(sp.numer(sp.together(t38)))
print("t38:",N38)
